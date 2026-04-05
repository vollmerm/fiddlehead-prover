from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional, Protocol, Tuple

from .syntax import (
    App,
    Const,
    Fun,
    Term,
    TypeConst,
    TypeTerm,
    TypeVar,
    V,
    Var,
    _to_type_term,
    apply_subst,
    false,
    match,
    true,
)


@dataclass(frozen=True)
class Rule:
    lhs: Term
    rhs: Term
    conditions: Tuple[Tuple[Term, Term], ...] = ()


class RuleIndex:
    def __init__(self, rules: list[Rule]):
        self.by_symbol: Dict[Optional[str], list[Rule]] = {}
        for rule in rules:
            match rule.lhs:
                case Fun(symbol, _):
                    self.by_symbol.setdefault(symbol, []).append(rule)
                case Var():
                    self.by_symbol.setdefault(None, []).append(rule)

    def get(self, term: Term) -> list[Rule]:
        match term:
            case Fun(symbol, _):
                return self.by_symbol.get(symbol, []) + self.by_symbol.get(None, [])
            case Var():
                return self.by_symbol.get(None, [])


def builtin_rules() -> list[Rule]:
    x = V("x")
    y = V("y")
    return [
        Rule(App("eq", x, x), true),
        Rule(App("neq", x, x), false),
        Rule(App("if", true, x, y), x),
        Rule(App("if", false, x, y), y),
        Rule(App("not", true), false),
        Rule(App("not", false), true),
        Rule(App("and", true, x), x),
        Rule(App("and", false, x), false),
        Rule(App("and", x, true), x),
        Rule(App("and", x, false), false),
        Rule(App("or", true, x), true),
        Rule(App("or", false, x), x),
        Rule(App("or", x, true), true),
        Rule(App("or", x, false), x),
    ]


@dataclass(frozen=True)
class Context:
    equalities: Tuple[Tuple[Term, Term], ...] = ()
    disequalities: Tuple[Tuple[Term, Term], ...] = ()


@dataclass(frozen=True)
class EngineConfig:
    precedence: Dict[str, int]
    assoc: set[str]
    comm: set[str]


def default_engine_config() -> EngineConfig:
    return EngineConfig(
        precedence={
            "not": 2,
            "and": 2,
            "or": 2,
            "S": 2,
            "if": 1,
            "eq": 1,
            "neq": 1,
            "0": 0,
            "1": 0,
            "true": 0,
            "false": 0,
        },
        assoc=set(),
        comm=set(),
    )


@dataclass(frozen=True)
class SortSignature:
    arg_sorts: Tuple[TypeTerm, ...]
    result_sort: TypeTerm

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "arg_sorts",
            tuple(_to_type_term(arg_sort) for arg_sort in self.arg_sorts),
        )
        object.__setattr__(self, "result_sort", _to_type_term(self.result_sort))


def default_sort_signatures() -> Dict[str, SortSignature]:
    a = TypeVar("A")
    return {
        "0": SortSignature((), TypeConst("Nat")),
        "1": SortSignature((), TypeConst("Nat")),
        "true": SortSignature((), TypeConst("Bool")),
        "false": SortSignature((), TypeConst("Bool")),
        "not": SortSignature((TypeConst("Bool"),), TypeConst("Bool")),
        "and": SortSignature((TypeConst("Bool"), TypeConst("Bool")), TypeConst("Bool")),
        "or": SortSignature((TypeConst("Bool"), TypeConst("Bool")), TypeConst("Bool")),
        "S": SortSignature((TypeConst("Nat"),), TypeConst("Nat")),
        "eq": SortSignature((a, a), TypeConst("Bool")),
        "neq": SortSignature((a, a), TypeConst("Bool")),
        "if": SortSignature((TypeConst("Bool"), a, a), a),
    }


def _prec(config: EngineConfig, symbol: str) -> int:
    return config.precedence.get(symbol, 0)


def _lpo_greater(config: EngineConfig, left: Term, right: Term) -> bool:
    if left is right:
        return False

    match left, right:
        case _, Var():
            return True
        case Var(), Fun():
            return False
        case Fun(left_symbol, left_args), Fun(right_symbol, right_args):
            if any(_lpo_greater(config, arg, right) or arg is right for arg in left_args):
                return True
            if _prec(config, left_symbol) > _prec(config, right_symbol) and all(
                _lpo_greater(config, left, arg) for arg in right_args
            ):
                return True
            if left_symbol == right_symbol:
                for left_arg, right_arg in zip(left_args, right_args):
                    if left_arg is right_arg:
                        continue
                    if _lpo_greater(config, left_arg, right_arg):
                        return True
                    if _lpo_greater(config, right_arg, left_arg):
                        return False
    return False


def _decreases(config: EngineConfig, before: Term, after: Term) -> bool:
    return _lpo_greater(config, before, after)


def _term_key(term: Term) -> tuple[object, ...]:
    match term:
        case Fun(symbol, args):
            return (0, symbol, len(args), tuple(_term_key(arg) for arg in args))
        case Var(name):
            return (1, name)


def _rep_priority(term: Term) -> tuple[int, tuple[object, ...]]:
    match term:
        case Fun(_, args) if not args:
            return (0, _term_key(term))
        case Var():
            return (1, _term_key(term))
        case Fun():
            return (2, _term_key(term))


class EqClasses:
    def __init__(self) -> None:
        self.parent: Dict[Term, Term] = {}
        self.rank: Dict[Term, int] = {}
        self.terms: set[Term] = set()
        self.rep: Dict[Term, Term] = {}

    def _ensure(self, term: Term) -> None:
        if term not in self.parent:
            self.parent[term] = term
            self.rank[term] = 0
            self.terms.add(term)
            self.rep[term] = term

    def _register(self, term: Term) -> None:
        self._ensure(term)
        match term:
            case Fun(_, args):
                for arg in args:
                    self._register(arg)

    def find(self, term: Term) -> Term:
        self._ensure(term)
        parent = self.parent[term]
        if parent is not term:
            self.parent[term] = self.find(parent)
        return self.parent[term]

    def union(self, left: Term, right: Term) -> bool:
        self._register(left)
        self._register(right)
        root_left = self.find(left)
        root_right = self.find(right)
        if root_left is root_right:
            return False

        if self.rank[root_left] < self.rank[root_right]:
            root_left, root_right = root_right, root_left
        elif self.rank[root_left] == self.rank[root_right] and _term_key(root_right) < _term_key(
            root_left
        ):
            root_left, root_right = root_right, root_left

        self.parent[root_right] = root_left
        if self.rank[root_left] == self.rank[root_right]:
            self.rank[root_left] += 1
        if _rep_priority(self.rep[root_right]) < _rep_priority(self.rep[root_left]):
            self.rep[root_left] = self.rep[root_right]
        return True

    def close_congruence(self) -> None:
        changed = True
        while changed:
            changed = False
            sig_to_term: Dict[Tuple[str, Tuple[Term, ...]], Term] = {}
            for term in list(self.terms):
                match term:
                    case Fun(symbol, args):
                        signature = (symbol, tuple(self.find(arg) for arg in args))
                        other = sig_to_term.get(signature)
                        if other is None:
                            sig_to_term[signature] = term
                        elif self.union(term, other):
                            changed = True

    def canonical(self, term: Term) -> Term:
        self._register(term)
        self.close_congruence()
        match term:
            case Var():
                return self.rep[self.find(term)]
            case Fun(symbol, args):
                canonical_args = tuple(self.canonical(arg) for arg in args)
                rebuilt = Fun(symbol, canonical_args)
                self._register(rebuilt)
                self.close_congruence()
                return self.rep[self.find(rebuilt)]

    def are_equal(self, left: Term, right: Term) -> bool:
        return self.canonical(left) is self.canonical(right)


def _build_eq_classes(ctx: Context, extra_terms: Tuple[Term, ...] = ()) -> EqClasses:
    eq_classes = EqClasses()
    for left, right in ctx.equalities:
        eq_classes._register(left)
        eq_classes._register(right)
        eq_classes.union(left, right)
    for left, right in ctx.disequalities:
        eq_classes._register(left)
        eq_classes._register(right)
    for term in extra_terms:
        eq_classes._register(term)
    eq_classes.close_congruence()
    return eq_classes


def _context_rules(ctx: Context, config: EngineConfig):
    for lhs, rhs in ctx.equalities:
        if _decreases(config, lhs, rhs):
            yield Rule(lhs, rhs)
        elif _decreases(config, rhs, lhs):
            yield Rule(rhs, lhs)
        elif _term_key(lhs) <= _term_key(rhs):
            yield Rule(rhs, lhs)
        else:
            yield Rule(lhs, rhs)


def _ac_normalize(config: EngineConfig, term: Term) -> Term:
    match term:
        case Fun(symbol, (left, right)) if symbol in config.assoc:
            flat: list[Term] = []

            def collect(current: Term) -> None:
                match current:
                    case Fun(inner_symbol, (inner_left, inner_right)) if inner_symbol == symbol:
                        collect(inner_left)
                        collect(inner_right)
                    case _:
                        flat.append(current)

            collect(term)
            if symbol in config.comm:
                flat.sort(key=_term_key)

            out = flat[-1]
            for current in reversed(flat[:-1]):
                out = Fun(symbol, (current, out))
            return out

    return term


def is_ground(term: Term) -> bool:
    match term:
        case Var():
            return False
        case Fun(_, args):
            return all(is_ground(arg) for arg in args)


def _apply_type_subst(term: TypeTerm, subst: Dict[TypeVar, TypeTerm]) -> TypeTerm:
    match term:
        case TypeVar() as type_var:
            if type_var in subst:
                out = _apply_type_subst(subst[type_var], subst)
                subst[type_var] = out
                return out
            return type_var
        case TypeConst(name, args):
            if not args:
                return term
            return TypeConst(name, tuple(_apply_type_subst(arg, subst) for arg in args))


def _occurs_in_type(type_var: TypeVar, term: TypeTerm, subst: Dict[TypeVar, TypeTerm]) -> bool:
    term = _apply_type_subst(term, subst)
    match term:
        case TypeVar() as other:
            return other == type_var
        case TypeConst(_, args):
            return any(_occurs_in_type(type_var, arg, subst) for arg in args)


def _unify_types(left: TypeTerm, right: TypeTerm, subst: Dict[TypeVar, TypeTerm], where: str) -> None:
    resolved_left = _apply_type_subst(left, subst)
    resolved_right = _apply_type_subst(right, subst)
    if resolved_left == resolved_right:
        return
    match resolved_left, resolved_right:
        case TypeVar() as left_var, _:
            if _occurs_in_type(left_var, resolved_right, subst):
                raise ValueError(
                    f"Ill-typed {where}: recursive type in {left_var} ~ {resolved_right}."
                )
            subst[left_var] = resolved_right
            return
        case _, TypeVar() as right_var:
            if _occurs_in_type(right_var, resolved_left, subst):
                raise ValueError(
                    f"Ill-typed {where}: recursive type in {resolved_left} ~ {right_var}."
                )
            subst[right_var] = resolved_left
            return
        case TypeConst(left_name, left_args), TypeConst(right_name, right_args):
            if left_name != right_name or len(left_args) != len(right_args):
                raise ValueError(
                    f"Ill-typed {where}: cannot unify {resolved_left} with {resolved_right}."
                )
            for index, (left_arg, right_arg) in enumerate(zip(left_args, right_args)):
                _unify_types(left_arg, right_arg, subst, f"{where} arg[{index}]")
            return
    raise ValueError(f"Ill-typed {where}: cannot unify {resolved_left} with {resolved_right}.")


def _fresh_type_var(prefix: str, counter: list[int]) -> TypeVar:
    n = counter[0]
    counter[0] = n + 1
    return TypeVar(f"{prefix}_{n}")


_ANNOTATED_PARAM_SORT_ARITY: Dict[str, int] = {
    "List": 1,
}


def _type_from_sort_annotation(sort: str, counter: list[int]) -> TypeTerm:
    arity = _ANNOTATED_PARAM_SORT_ARITY.get(sort)
    if arity is not None:
        return TypeConst(sort, tuple(_fresh_type_var("s", counter) for _ in range(arity)))
    return TypeConst(sort)


def _matches_sort_name(term: TypeTerm, sort_name: str) -> bool:
    match term:
        case TypeConst(name, _):
            return name == sort_name
        case _:
            return False


def _freshen_signature(
    signature: SortSignature, counter: list[int]
) -> tuple[Tuple[TypeTerm, ...], TypeTerm]:
    mapping: Dict[TypeVar, TypeVar] = {}

    def freshen(term: TypeTerm) -> TypeTerm:
        match term:
            case TypeVar() as type_var:
                out = mapping.get(type_var)
                if out is None:
                    out = _fresh_type_var("t", counter)
                    mapping[type_var] = out
                return out
            case TypeConst(name, args):
                return TypeConst(name, tuple(freshen(arg) for arg in args))

    return tuple(freshen(arg) for arg in signature.arg_sorts), freshen(signature.result_sort)


def _infer_type_inner(
    term: Term,
    engine: Engine,
    var_env: Dict[Var, TypeTerm],
    subst: Dict[TypeVar, TypeTerm],
    counter: list[int],
) -> TypeTerm:
    match term:
        case Var(_, sort) as var:
            existing = var_env.get(var)
            if existing is not None:
                return _apply_type_subst(existing, subst)
            inferred = _type_from_sort_annotation(sort, counter) if sort is not None else _fresh_type_var(
                "v", counter
            )
            var_env[var] = inferred
            return _apply_type_subst(inferred, subst)

        case Fun(symbol, args):
            signature = engine.sort_signatures.get(symbol)
            if signature is None:
                raise ValueError(f"Unknown symbol type: {symbol}. Register a sort signature first.")
            expected_args, expected_result = _freshen_signature(signature, counter)
            if len(expected_args) != len(args):
                raise ValueError(
                    f"Ill-typed term: {symbol} expects {len(expected_args)} args, got {len(args)}."
                )
            for index, (arg, expected_type) in enumerate(zip(args, expected_args)):
                actual_type = _infer_type_inner(arg, engine, var_env, subst, counter)
                _unify_types(actual_type, expected_type, subst, f"{symbol} argument {index}")
            return _apply_type_subst(expected_result, subst)


def infer_type(term: Term, engine: Engine) -> TypeTerm:
    subst: Dict[TypeVar, TypeTerm] = {}
    inferred = _infer_type_inner(term, engine, {}, subst, [0])
    return _apply_type_subst(inferred, subst)


def _contains_type_vars(term: TypeTerm) -> bool:
    match term:
        case TypeVar():
            return True
        case TypeConst(_, args):
            return any(_contains_type_vars(arg) for arg in args)


def infer_sort(term: Term, engine: Engine) -> str:
    inferred = infer_type(term, engine)
    if _contains_type_vars(inferred):
        raise ValueError(f"Ambiguous inferred type for term {term}: {inferred}.")
    match inferred:
        case TypeConst(name, ()) as concrete:
            return concrete.name
        case _:
            return str(inferred)


def _infer_pair_with_shared_env(
    lhs: Term,
    rhs: Term,
    engine: Engine,
    where: str,
) -> tuple[TypeTerm, TypeTerm, Dict[TypeVar, TypeTerm]]:
    subst: Dict[TypeVar, TypeTerm] = {}
    counter = [0]
    env: Dict[Var, TypeTerm] = {}
    left_type = _infer_type_inner(lhs, engine, env, subst, counter)
    right_type = _infer_type_inner(rhs, engine, env, subst, counter)
    _unify_types(left_type, right_type, subst, where)
    return _apply_type_subst(left_type, subst), _apply_type_subst(right_type, subst), subst


def _validate_equality_pair(lhs: Term, rhs: Term, engine: Engine, where: str) -> None:
    _infer_pair_with_shared_env(lhs, rhs, engine, where)


def _validate_rule_sorts(rule: Rule, engine: Engine, where: str) -> None:
    _validate_equality_pair(rule.lhs, rule.rhs, engine, where)
    for index, (left, right) in enumerate(rule.conditions):
        _validate_equality_pair(left, right, engine, f"{where} condition[{index}]")


def _validate_clause_sorts(clause: ClauseLike, engine: Engine, where: str) -> None:
    infer_type(clause.goal, engine)
    for index, (left, right) in enumerate(clause.assumptions):
        _validate_equality_pair(left, right, engine, f"{where} assumption[{index}]")


@dataclass
class TraceStep:
    before: Term
    after: Term
    rule: Rule


class Trace:
    def __init__(self) -> None:
        self.steps: list[TraceStep] = []

    def add(self, before: Term, after: Term, rule: Rule) -> None:
        self.steps.append(TraceStep(before, after, rule))


class ClauseLike(Protocol):
    assumptions: Tuple[Tuple[Term, Term], ...]
    goal: Term


@dataclass
class ProofNode:
    kind: str
    clause: ClauseLike
    note: str = ""
    children: list["ProofNode"] | None = None
    solved: Optional[bool] = None

    def __post_init__(self) -> None:
        if self.children is None:
            self.children = []


@dataclass
class ProofTrace:
    roots: list[ProofNode]

    def __init__(self) -> None:
        self.roots = []


def _new_node(kind: str, clause: ClauseLike, note: str = "") -> ProofNode:
    return ProofNode(kind=kind, clause=clause, note=note, children=[])


def render_proof_trace(trace: ProofTrace) -> str:
    lines: list[str] = []

    def visit(node: ProofNode, indent: int) -> None:
        pad = "  " * indent
        status = ""
        if node.solved is True:
            status = " [solved]"
        elif node.solved is False:
            status = " [failed]"
        note = f" :: {node.note}" if node.note else ""
        lines.append(f"{pad}- {node.kind}{status}{note} -> {node.clause.goal}")
        for child in node.children or []:
            visit(child, indent + 1)

    for root in trace.roots:
        visit(root, 0)
    return "\n".join(lines)


@dataclass(frozen=True)
class InductionConstructor:
    symbol: str
    arity: int
    recursive_positions: Tuple[int, ...] = ()


@dataclass(frozen=True)
class InductionScheme:
    name: str
    sort: str
    base_terms: Tuple[Term, ...]
    constructors: Tuple[InductionConstructor, ...]


def nat_induction_scheme(zero: Optional[Term] = None, succ_symbol: str = "S") -> InductionScheme:
    if zero is None:
        zero = Const("0")
    return InductionScheme(
        name="nat",
        sort="Nat",
        base_terms=(zero,),
        constructors=(InductionConstructor(succ_symbol, 1, (0,)),),
    )


def list_induction_scheme(nil_symbol: str = "nil", cons_symbol: str = "cons") -> InductionScheme:
    return InductionScheme(
        name="list",
        sort="List",
        base_terms=(Const(nil_symbol),),
        constructors=(InductionConstructor(cons_symbol, 2, (1,)),),
    )


def var_matches_scheme(var: Var, scheme: InductionScheme) -> bool:
    return var.sort is None or var.sort == scheme.sort


@dataclass
class Engine:
    rules: list[Rule]
    ctx: Context = Context()
    trace: Optional[Trace] = None
    fuel: int = 1000
    config: Optional[EngineConfig] = None
    ground_cache: Optional[Dict[Term, Term]] = None
    schemes: Optional[Dict[str, InductionScheme]] = None
    sort_signatures: Optional[Dict[str, SortSignature]] = None
    installed_theories: Optional[Dict[str, str]] = None
    theory: Optional[object] = None

    def __post_init__(self) -> None:
        self.index = RuleIndex(self.rules)
        self.memo: Dict[Term, Term] = {}
        self.eq_classes: Optional[EqClasses] = None
        if self.config is None:
            self.config = default_engine_config()
        if self.ground_cache is None:
            self.ground_cache = {}
        if self.schemes is None:
            self.schemes = {}
        if self.sort_signatures is None:
            self.sort_signatures = default_sort_signatures()
        else:
            self.sort_signatures = dict(self.sort_signatures)
        if self.installed_theories is None:
            self.installed_theories = {}
        else:
            self.installed_theories = dict(self.installed_theories)
        for index, rule in enumerate(self.rules):
            _validate_rule_sorts(rule, self, f"rule[{index}]")

    def _ensure_eq_classes(self, term: Optional[Term] = None) -> None:
        if self.eq_classes is None:
            extra = (term,) if term is not None else ()
            self.eq_classes = _build_eq_classes(self.ctx, extra)
        elif term is not None:
            self.eq_classes._register(term)
            self.eq_classes.close_congruence()

    def holds(self, left: Term, right: Term) -> bool:
        left = self.normalize(left)
        right = self.normalize(right)
        self._ensure_eq_classes(left)
        self._ensure_eq_classes(right)
        assert self.eq_classes is not None
        eq_classes = self.eq_classes
        for ctx_left, ctx_right in self.ctx.disequalities:
            if eq_classes.are_equal(left, ctx_left) and eq_classes.are_equal(right, ctx_right):
                return False
            if eq_classes.are_equal(left, ctx_right) and eq_classes.are_equal(right, ctx_left):
                return False
        return eq_classes.are_equal(left, right)

    def conditions_hold(self, conditions: Tuple[Tuple[Term, Term], ...], subst: Dict[Var, Term]) -> bool:
        for left, right in conditions:
            if not self.holds(apply_subst(left, subst), apply_subst(right, subst)):
                return False
        return True

    def rewrite_once(self, term: Term, rule: Rule) -> Optional[Term]:
        subst = match(rule.lhs, term)
        if subst is None:
            return None
        if rule.conditions and not self.conditions_hold(rule.conditions, subst):
            return None
        new_term = apply_subst(rule.rhs, subst)
        assert self.config is not None
        if not rule.conditions and not _decreases(self.config, term, new_term):
            return None
        if self.trace is not None:
            self.trace.add(term, new_term, rule)
        return new_term

    def rewrite_term(self, term: Term) -> Term:
        if term in self.memo:
            return self.memo[term]

        self._ensure_eq_classes(term)
        assert self.eq_classes is not None
        term = self.eq_classes.canonical(term)

        match term:
            case Fun(symbol, args):
                rewritten_args = tuple(self.rewrite_term(arg) for arg in args)
                term = Fun(symbol, rewritten_args)

        assert self.config is not None
        term = _ac_normalize(self.config, term)
        term = self.eq_classes.canonical(term)

        for rule in self.index.get(term):
            rewritten = self.rewrite_once(term, rule)
            if rewritten is not None:
                self.memo[term] = rewritten
                return rewritten

        for rule in _context_rules(self.ctx, self.config):
            rewritten = self.rewrite_once(term, rule)
            if rewritten is not None:
                self.memo[term] = rewritten
                return rewritten

        self.memo[term] = term
        return term

    def normalize(self, term: Term) -> Term:
        original = term
        original_is_ground = is_ground(original)
        self._ensure_eq_classes(term)

        for _ in range(self.fuel):
            if is_ground(term) and term in self.ground_cache:
                cached = self.ground_cache[term]
                if original_is_ground:
                    self.ground_cache[original] = cached
                return cached

            rewritten = self.rewrite_term(term)
            if rewritten is term:
                break
            term = rewritten

        if original_is_ground:
            self.ground_cache[original] = term
        if is_ground(term):
            self.ground_cache[term] = term
        return term

    def register_scheme(self, scheme: InductionScheme) -> None:
        for index, base in enumerate(scheme.base_terms):
            base_type = infer_type(base, self)
            match base_type:
                case TypeConst(name, _):
                    if name != scheme.sort:
                        raise ValueError(
                            f"Induction scheme {scheme.name} base[{index}] has type "
                            f"{base_type}, expected {scheme.sort}."
                        )
                case _:
                    raise ValueError(
                        f"Induction scheme {scheme.name} base[{index}] has non-constructor "
                        f"type {base_type}."
                    )
        for constructor in scheme.constructors:
            signature = self.sort_signatures.get(constructor.symbol)
            if signature is None:
                continue
            if len(signature.arg_sorts) != constructor.arity:
                raise ValueError(
                    f"Induction constructor {constructor.symbol} arity {constructor.arity} "
                    f"mismatches declared arity {len(signature.arg_sorts)}."
                )
            if not _matches_sort_name(signature.result_sort, scheme.sort):
                raise ValueError(
                    f"Induction constructor {constructor.symbol} returns "
                    f"{signature.result_sort}, expected {scheme.sort}."
                )
            for position in constructor.recursive_positions:
                if position < 0 or position >= len(signature.arg_sorts):
                    raise ValueError(
                        f"Induction constructor {constructor.symbol} recursive arg index "
                        f"{position} out of range."
                    )
                expected = signature.arg_sorts[position]
                if not _matches_sort_name(expected, scheme.sort):
                    raise ValueError(
                        f"Induction constructor {constructor.symbol} recursive arg {position} "
                        f"sort {expected} does not match scheme sort {scheme.sort}."
                    )
        self.schemes[scheme.name] = scheme

    def get_scheme(self, name: str) -> Optional[InductionScheme]:
        return self.schemes.get(name)

    def get_scheme_for_sort(self, sort: str) -> Optional[InductionScheme]:
        for scheme in self.schemes.values():
            if scheme.sort == sort:
                return scheme
        return None

    def reset_rules(self, rules: list[Rule]) -> None:
        for index, rule in enumerate(rules):
            _validate_rule_sorts(rule, self, f"rule[{index}]")
        self.rules = list(rules)
        self.index = RuleIndex(self.rules)
        self.memo = {}
        self.eq_classes = None
        if self.ground_cache is not None:
            self.ground_cache.clear()

    def register_sort_signature(self, symbol: str, signature: SortSignature) -> None:
        self.sort_signatures[symbol] = signature

    def get_sort_signature(self, symbol: str) -> Optional[SortSignature]:
        return self.sort_signatures.get(symbol)

    def get_theory(self):
        if self.theory is None:
            from .theory import TheoremEnvironment

            self.theory = TheoremEnvironment(self, self.rules)
        return self.theory


def make_engine(
    rules: list[Rule],
    ctx: Context = Context(),
    trace: Optional[Trace] = None,
    fuel: int = 1000,
    config: Optional[EngineConfig] = None,
    ground_cache: Optional[Dict[Term, Term]] = None,
    schemes: Optional[Dict[str, InductionScheme]] = None,
    sort_signatures: Optional[Dict[str, SortSignature]] = None,
    installed_theories: Optional[Dict[str, str]] = None,
) -> Engine:
    return Engine(
        rules=rules,
        ctx=ctx,
        trace=trace,
        fuel=fuel,
        config=config,
        ground_cache=ground_cache,
        schemes=schemes,
        sort_signatures=sort_signatures,
        installed_theories=installed_theories,
    )


def normalize(term: Term, engine: Engine) -> Term:
    return engine.normalize(term)


def register_induction_scheme(engine: Engine, scheme: InductionScheme) -> None:
    engine.register_scheme(scheme)


def get_induction_scheme(engine: Engine, name: str) -> Optional[InductionScheme]:
    return engine.get_scheme(name)


def get_induction_scheme_for_sort(engine: Engine, sort: str) -> Optional[InductionScheme]:
    return engine.get_scheme_for_sort(sort)


def register_sort_signature(engine: Engine, symbol: str, signature: SortSignature) -> None:
    engine.register_sort_signature(symbol, signature)


def get_sort_signature(engine: Engine, symbol: str) -> Optional[SortSignature]:
    return engine.get_sort_signature(symbol)
