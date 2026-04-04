from __future__ import annotations

"""
Boyer–Moore style rewriting core with:
- hash-consed terms
- LPO ordering
- AC normalization
- contextual rewriting (substitution-based)
- clause reasoning
- tracing
- term indexing
- ground-term caching
- per-call memoization
- conditional rewriting
- negation and split
- congruence closure
- induction schemes

Public API (small, stable surface):
- term constructors: V, Const, App
- proving entry points: normalize, prove, prove_with_induction, prove_with_registered_induction
- induction registration: register_induction_scheme, get_induction_scheme, get_induction_scheme_for_sort
"""

from dataclasses import dataclass
from typing import Tuple, Dict, Optional
from weakref import WeakValueDictionary

__all__ = [
    "Term",
    "Var",
    "Fun",
    "V",
    "reset_var_interner",
    "Const",
    "App",
    "true",
    "false",
    "Rule",
    "Clause",
    "Context",
    "InductionConstructor",
    "InductionScheme",
    "nat_induction_scheme",
    "list_induction_scheme",
    "register_induction_scheme",
    "get_induction_scheme",
    "get_induction_scheme_for_sort",
    "make_engine",
    "EngineConfig",
    "default_engine_config",
    "builtin_rules",
    "normalize",
    "prove",
    "prove_with_induction",
    "prove_with_registered_induction",
    "ProofTrace",
    "ProofNode",
    "render_proof_trace",
    "prove_with_trace",
    "ProofCertificate",
    "certificate_to_proof_trace",
    "prove_checked",
    "check_certificate",
    "Lemma",
    "TheoremEnvironment",
    "get_theorem_environment",
    "ProofSession",
]

# -----------------------------------------------------------------------------
# Terms (hash-consed)
# -----------------------------------------------------------------------------

class Term:
    pass


@dataclass(frozen=True, slots=True)
class Var(Term):
    name: str
    sort: Optional[str] = None

    def __str__(self):
        return self.name


_VAR_INTERN: Dict[Tuple[str, Optional[str]], Var] = {}
_VAR_NAME_SORT: Dict[str, Optional[str]] = {}


def reset_var_interner():
    _VAR_INTERN.clear()
    _VAR_NAME_SORT.clear()


def V(name: str, sort: Optional[str] = None) -> Var:
    existing_sort = _VAR_NAME_SORT.get(name)
    if existing_sort is None and name in _VAR_NAME_SORT:
        if sort is not None:
            raise ValueError(f"Variable '{name}' already declared with sort None; cannot redeclare with sort '{sort}'.")
    elif existing_sort is not None and existing_sort != sort:
        raise ValueError(f"Variable '{name}' already declared with sort '{existing_sort}'; cannot redeclare with sort '{sort}'.")

    key = (name, sort)
    existing = _VAR_INTERN.get(key)
    if existing is not None:
        return existing

    v = Var(name, sort)
    _VAR_INTERN[key] = v
    _VAR_NAME_SORT[name] = sort
    return v


@dataclass(frozen=True, slots=True)
class Fun(Term):
    symbol: str
    args: Tuple[Term, ...]

    def __new__(cls, symbol: str, args: Tuple[Term, ...]):
        key = (symbol, args)
        existing = cls._cache.get(key)
        if existing is not None:
            return existing

        self = object.__new__(cls)
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "args", args)
        cls._cache[key] = self
        return self

    def __str__(self):
        if not self.args:
            return self.symbol
        return f"{self.symbol}({', '.join(map(str, self.args))})"


Fun._cache = WeakValueDictionary()


# -----------------------------------------------------------------------------
# DSL
# -----------------------------------------------------------------------------


def Const(n): return Fun(n, ())
def App(f, *a): return Fun(f, a)

true=Const("true")
false=Const("false")


# -----------------------------------------------------------------------------
# Substitution
# -----------------------------------------------------------------------------

Subst = Dict[Var, Term]


def apply_subst(term: Term, subst: Subst) -> Term:
    match term:
        case Var() as v:
            return subst.get(v, v)
        case Fun(f, args):
            return Fun(f, tuple(apply_subst(a, subst) for a in args))


# -----------------------------------------------------------------------------
# Matching
# -----------------------------------------------------------------------------


def match(pattern: Term, target: Term, subst: Optional[Subst] = None) -> Optional[Subst]:
    if subst is None:
        subst = {}

    if pattern is target:
        return subst

    match pattern, target:
        case Var() as v, t:
            if v in subst:
                if subst[v] is t:
                    return subst
                return subst if subst[v] == t else None
            new = subst.copy()
            new[v] = t
            return new

        case Fun(f1, a1), Fun(f2, a2):
            if f1 != f2 or len(a1) != len(a2):
                return None
            for x, y in zip(a1, a2):
                subst = match(x, y, subst)
                if subst is None:
                    return None
            return subst

    return None


# -----------------------------------------------------------------------------
# LPO ordering
# -----------------------------------------------------------------------------


def _prec(config: EngineConfig, f: str):
    return config.precedence.get(f, 0)


def _lpo_greater(config: EngineConfig, s: Term, t: Term) -> bool:
    if s is t:
        return False

    match s, t:
        case _, Var():
            return True
        case Var(), Fun():
            return False
        case Fun(f, s_args), Fun(g, t_args):
            if any(_lpo_greater(config, si, t) or si is t for si in s_args):
                return True
            if _prec(config, f) > _prec(config, g) and all(_lpo_greater(config, s, ti) for ti in t_args):
                return True
            if f == g:
                for si, ti in zip(s_args, t_args):
                    if si is ti:
                        continue
                    if _lpo_greater(config, si, ti):
                        return True
                    if _lpo_greater(config, ti, si):
                        return False
    return False


def _decreases(config: EngineConfig, a, b):
    return _lpo_greater(config, a, b)


# -----------------------------------------------------------------------------
# Rules + indexing
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class Rule:
    lhs: Term
    rhs: Term
    conditions: Tuple[Tuple[Term, Term], ...] = ()


class RuleIndex:
    def __init__(self, rules):
        self.by_symbol: Dict[Optional[str], list] = {}
        for r in rules:
            match r.lhs:
                case Fun(sym, _):
                    self.by_symbol.setdefault(sym, []).append(r)
                case Var():
                    self.by_symbol.setdefault(None, []).append(r)

    def get(self, term: Term):
        match term:
            case Fun(sym, _):
                return self.by_symbol.get(sym, []) + self.by_symbol.get(None, [])
            case Var():
                return self.by_symbol.get(None, [])


# -----------------------------------------------------------------------------
# Boolean + disequality rules
# -----------------------------------------------------------------------------

def builtin_rules():
    x=V("x"); y=V("y")
    return [
        Rule(App("eq",x,x),true),
        Rule(App("neq",x,x),false),
        Rule(App("if",true,x,y),x),
        Rule(App("if",false,x,y),y),
    ]

            
# -----------------------------------------------------------------------------
# Context
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class Context:
    equalities: Tuple[Tuple[Term, Term], ...] = ()
    disequalities: Tuple[Tuple[Term,Term],...]=()


@dataclass(frozen=True)
class EngineConfig:
    precedence: Dict[str, int]
    assoc: set[str]
    comm: set[str]


def default_engine_config() -> EngineConfig:
    return EngineConfig(
        precedence={
            "add": 3,
            "append": 3,
            "length": 3,
            "S": 2,
            "cons": 2,
            "if": 1,
            "eq": 1,
            "neq": 1,
            "0": 0,
            "1": 0,
            "nil": 0,
            "true": 0,
            "false": 0,
        },
        assoc={"add"},
        comm={"add"},
    )


class EqClasses:
    def __init__(self):
        self.parent: Dict[Term, Term] = {}
        self.rank: Dict[Term, int] = {}
        self.terms: set[Term] = set()
        self.rep: Dict[Term, Term] = {}

    def _ensure(self, t: Term):
        if t not in self.parent:
            self.parent[t] = t
            self.rank[t] = 0
            self.terms.add(t)
            self.rep[t] = t

    def _register(self, t: Term):
        self._ensure(t)
        match t:
            case Fun(_, args):
                for a in args:
                    self._register(a)

    def find(self, t: Term) -> Term:
        self._ensure(t)
        p = self.parent[t]
        if p is not t:
            self.parent[t] = self.find(p)
        return self.parent[t]

    def union(self, a: Term, b: Term) -> bool:
        self._register(a)
        self._register(b)
        ra = self.find(a)
        rb = self.find(b)
        if ra is rb:
            return False

        if self.rank[ra] < self.rank[rb]:
            ra, rb = rb, ra
        elif self.rank[ra] == self.rank[rb] and _term_key(rb) < _term_key(ra):
            ra, rb = rb, ra

        self.parent[rb] = ra
        if self.rank[ra] == self.rank[rb]:
            self.rank[ra] += 1
        if _rep_priority(self.rep[rb]) < _rep_priority(self.rep[ra]):
            self.rep[ra] = self.rep[rb]
        return True

    def close_congruence(self):
        changed = True
        while changed:
            changed = False
            sig_to_term: Dict[Tuple[str, Tuple[Term, ...]], Term] = {}
            for t in list(self.terms):
                match t:
                    case Fun(sym, args):
                        sig = (sym, tuple(self.find(a) for a in args))
                        other = sig_to_term.get(sig)
                        if other is None:
                            sig_to_term[sig] = t
                        elif self.union(t, other):
                            changed = True

    def canonical(self, t: Term) -> Term:
        self._register(t)
        self.close_congruence()
        match t:
            case Var():
                return self.rep[self.find(t)]
            case Fun(sym, args):
                args2 = tuple(self.canonical(a) for a in args)
                rebuilt = Fun(sym, args2)
                self._register(rebuilt)
                self.close_congruence()
                return self.rep[self.find(rebuilt)]

    def are_equal(self, a: Term, b: Term) -> bool:
        return self.canonical(a) is self.canonical(b)


def _build_eq_classes(ctx: Context, extra_terms: Tuple[Term, ...] = ()) -> EqClasses:
    eq = EqClasses()
    for l, r in ctx.equalities:
        eq._register(l)
        eq._register(r)
        eq.union(l, r)
    for l, r in ctx.disequalities:
        eq._register(l)
        eq._register(r)
    for t in extra_terms:
        eq._register(t)
    eq.close_congruence()
    return eq


def _context_rules(ctx: Context, config: EngineConfig):
    for lhs, rhs in ctx.equalities:
        if _decreases(config, lhs, rhs):
            yield Rule(lhs, rhs)
        elif _decreases(config, rhs, lhs):
            yield Rule(rhs, lhs)
        else:
            # Deterministic fallback orientation for context/IH equalities
            # when the ordering does not decide.
            if _term_key(lhs) <= _term_key(rhs):
                yield Rule(rhs, lhs)
            else:
                yield Rule(lhs, rhs)


# -----------------------------------------------------------------------------
# Conditions
# -----------------------------------------------------------------------------

# -----------------------------------------------------------------------------
# AC normalization
# -----------------------------------------------------------------------------

def _term_key(t: Term):
    match t:
        case Fun(f, args):
            return (0, f, len(args), tuple(_term_key(a) for a in args))
        case Var(n):
            return (1, n)


def _rep_priority(t: Term):
    match t:
        case Fun(_, args) if not args:
            return (0, _term_key(t))
        case Var():
            return (1, _term_key(t))
        case Fun():
            return (2, _term_key(t))


def _ac_normalize(config: EngineConfig, t: Term) -> Term:
    match t:
        case Fun(f, (a, b)) if f in config.assoc:
            flat = []

            def collect(x):
                match x:
                    case Fun(f2, (l, r)) if f2 == f:
                        collect(l)
                        collect(r)
                    case _:
                        flat.append(x)

            collect(t)

            if f in config.comm:
                flat.sort(key=_term_key)

            res = flat[-1]
            for x in reversed(flat[:-1]):
                res = Fun(f, (x, res))
            return res

    return t


# -----------------------------------------------------------------------------
# Ground caching + memo
# -----------------------------------------------------------------------------

def is_ground(t: Term) -> bool:
    match t:
        case Var():
            return False
        case Fun(_, args):
            return all(is_ground(a) for a in args)


# -----------------------------------------------------------------------------
# Trace
# -----------------------------------------------------------------------------

@dataclass
class TraceStep:
    before: Term
    after: Term
    rule: Rule


class Trace:
    def __init__(self):
        self.steps = []

    def add(self, b, a, r):
        self.steps.append(TraceStep(b, a, r))


@dataclass
class ProofNode:
    kind: str
    clause: Clause
    note: str = ""
    children: list["ProofNode"] = None
    solved: Optional[bool] = None

    def __post_init__(self):
        if self.children is None:
            self.children = []


@dataclass
class ProofTrace:
    roots: list[ProofNode]

    def __init__(self):
        self.roots = []


def _new_node(kind: str, clause: Clause, note: str = "") -> ProofNode:
    return ProofNode(kind=kind, clause=clause, note=note, children=[])


def render_proof_trace(trace: ProofTrace) -> str:
    lines: list[str] = []

    def visit(node: ProofNode, indent: int):
        pad = "  " * indent
        status = ""
        if node.solved is True:
            status = " [solved]"
        elif node.solved is False:
            status = " [failed]"
        note = f" :: {node.note}" if node.note else ""
        lines.append(f"{pad}- {node.kind}{status}{note} -> {node.clause.goal}")
        for c in node.children:
            visit(c, indent + 1)

    for r in trace.roots:
        visit(r, 0)
    return "\n".join(lines)


# -----------------------------------------------------------------------------
# Engine (rewrite + normalize + condition checks)
# -----------------------------------------------------------------------------


@dataclass
class Engine:
    rules: list[Rule]
    ctx: Context = Context()
    trace: Optional[Trace] = None
    fuel: int = 1000
    config: Optional[EngineConfig] = None
    ground_cache: Optional[Dict[Term, Term]] = None
    schemes: Optional[Dict[str, "InductionScheme"]] = None
    theory: Optional["TheoremEnvironment"] = None

    def __post_init__(self):
        self.index = RuleIndex(self.rules)
        self.memo: Dict[Term, Term] = {}
        self.eq_classes: Optional[EqClasses] = None
        if self.config is None:
            self.config = default_engine_config()
        if self.ground_cache is None:
            self.ground_cache = {}
        if self.schemes is None:
            self.schemes = {}

    def _ensure_eq_classes(self, term: Optional[Term] = None):
        if self.eq_classes is None:
            extra = (term,) if term is not None else ()
            self.eq_classes = _build_eq_classes(self.ctx, extra)
        elif term is not None:
            self.eq_classes._register(term)
            self.eq_classes.close_congruence()

    def holds(self, l: Term, r: Term) -> bool:
        l2 = self.normalize(l)
        r2 = self.normalize(r)
        self._ensure_eq_classes(l2)
        self._ensure_eq_classes(r2)
        assert self.eq_classes is not None
        eq = self.eq_classes
        for a, b in self.ctx.disequalities:
            if eq.are_equal(l2, a) and eq.are_equal(r2, b):
                return False
            if eq.are_equal(l2, b) and eq.are_equal(r2, a):
                return False
        return eq.are_equal(l2, r2)

    def conditions_hold(self, conditions, subst) -> bool:
        for l, r in conditions:
            l2 = apply_subst(l, subst)
            r2 = apply_subst(r, subst)
            if not self.holds(l2, r2):
                return False
        return True

    def rewrite_once(self, term: Term, rule: Rule):
        subst = match(rule.lhs, term)
        if subst is None:
            return None
        if rule.conditions and not self.conditions_hold(rule.conditions, subst):
            return None
        new = apply_subst(rule.rhs, subst)
        assert self.config is not None
        if not rule.conditions and not _decreases(self.config, term, new):
            return None
        if self.trace:
            self.trace.add(term, new, rule)
        return new

    def rewrite_term(self, term: Term):
        if term in self.memo:
            return self.memo[term]

        self._ensure_eq_classes(term)
        assert self.eq_classes is not None
        term = self.eq_classes.canonical(term)

        match term:
            case Fun(f, args):
                args = tuple(self.rewrite_term(a) for a in args)
                term = Fun(f, args)

        assert self.config is not None
        term = _ac_normalize(self.config, term)
        term = self.eq_classes.canonical(term)

        for r in self.index.get(term):
            t2 = self.rewrite_once(term, r)
            if t2 is not None:
                self.memo[term] = t2
                return t2

        for r in _context_rules(self.ctx, self.config):
            t2 = self.rewrite_once(term, r)
            if t2 is not None:
                self.memo[term] = t2
                return t2

        self.memo[term] = term
        return term

    def normalize(self, term: Term):
        original = term
        self._ensure_eq_classes(term)

        for _ in range(self.fuel):
            if is_ground(term) and term in self.ground_cache:
                return self.ground_cache[term]

            t2 = self.rewrite_term(term)
            if t2 is term:
                break
            term = t2

        if is_ground(original):
            self.ground_cache[original] = term
        if is_ground(term):
            self.ground_cache[term] = term
        return term

    def register_scheme(self, scheme: "InductionScheme"):
        self.schemes[scheme.name] = scheme

    def get_scheme(self, name: str) -> Optional["InductionScheme"]:
        return self.schemes.get(name)

    def get_scheme_for_sort(self, sort: str) -> Optional["InductionScheme"]:
        for scheme in self.schemes.values():
            if scheme.sort == sort:
                return scheme
        return None

    def reset_rules(self, rules: list[Rule]):
        self.rules = list(rules)
        self.index = RuleIndex(self.rules)
        self.memo = {}
        self.eq_classes = None
        if self.ground_cache is not None:
            self.ground_cache.clear()

    def get_theory(self) -> "TheoremEnvironment":
        if self.theory is None:
            self.theory = TheoremEnvironment(self, self.rules)
        return self.theory


def make_engine(
    rules,
    ctx: Context = Context(),
    trace=None,
    fuel: int = 1000,
    config: Optional[EngineConfig] = None,
    ground_cache: Optional[Dict[Term, Term]] = None,
    schemes: Optional[Dict[str, "InductionScheme"]] = None,
) -> Engine:
    return Engine(
        rules=rules,
        ctx=ctx,
        trace=trace,
        fuel=fuel,
        config=config,
        ground_cache=ground_cache,
        schemes=schemes,
    )


def normalize(term, engine: Engine):
    return engine.normalize(term)


# -----------------------------------------------------------------------------
# Clause reasoning
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class Clause:
    assumptions: Tuple[Tuple[Term, Term], ...]
    goal: Term


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


def register_induction_scheme(engine: Engine, scheme: InductionScheme):
    engine.register_scheme(scheme)


def get_induction_scheme(engine: Engine, name: str) -> Optional[InductionScheme]:
    return engine.get_scheme(name)


def get_induction_scheme_for_sort(engine: Engine, sort: str) -> Optional[InductionScheme]:
    return engine.get_scheme_for_sort(sort)


def get_theorem_environment(engine: Engine) -> "TheoremEnvironment":
    return engine.get_theory()


def var_matches_scheme(var: Var, scheme: InductionScheme) -> bool:
    return var.sort is None or var.sort == scheme.sort


def vars_in_term(term: Term) -> set[str]:
    match term:
        case Var(n):
            return {n}
        case Fun(_, args):
            out: set[str] = set()
            for a in args:
                out |= vars_in_term(a)
            return out


def vars_in_clause(clause: Clause) -> set[str]:
    out = vars_in_term(clause.goal)
    for l, r in clause.assumptions:
        out |= vars_in_term(l)
        out |= vars_in_term(r)
    return out


def instantiate_clause(clause: Clause, subst: Subst) -> Clause:
    assumptions = tuple((apply_subst(l, subst), apply_subst(r, subst)) for l, r in clause.assumptions)
    goal = apply_subst(clause.goal, subst)
    return Clause(assumptions, goal)


def goal_equality(goal: Term) -> Optional[Tuple[Term, Term]]:
    match goal:
        case Fun("eq", (l, r)):
            return (l, r)
    return None


def fresh_var(base: str, used_names: set[str], sort: Optional[str] = None) -> Var:
    i = 0
    while True:
        name = f"{base}_{i}"
        if name not in used_names:
            used_names.add(name)
            return V(name, sort)
        i += 1


def induction_branches(clause: Clause, var: Var, scheme: InductionScheme) -> list[Clause]:
    if not var_matches_scheme(var, scheme):
        return []

    used = vars_in_clause(clause).copy()
    branches: list[Clause] = []

    for b in scheme.base_terms:
        branches.append(instantiate_clause(clause, {var: b}))

    for cons in scheme.constructors:
        rec_vars = [fresh_var(f"{var.name}_ih", used, scheme.sort) for _ in cons.recursive_positions]
        ih_assumptions: list[Tuple[Term, Term]] = []
        for rv in rec_vars:
            ih_goal = instantiate_clause(clause, {var: rv}).goal
            eq = goal_equality(ih_goal)
            if eq is None:
                return []
            ih_assumptions.append(eq)

        args: list[Term] = [fresh_var(f"{var.name}_{cons.symbol}_arg", used) for _ in range(cons.arity)]
        for pos, rv in zip(cons.recursive_positions, rec_vars):
            args[pos] = rv

        step_term = App(cons.symbol, *args)
        step_clause = instantiate_clause(clause, {var: step_term})
        branches.append(Clause(step_clause.assumptions + tuple(ih_assumptions), step_clause.goal))

    return branches


def simplify_clause(clause: Clause, engine: Engine):
    local_engine = make_engine(
        rules=engine.rules,
        ctx=Context(clause.assumptions),
        trace=engine.trace,
        fuel=engine.fuel,
        config=engine.config,
        ground_cache=engine.ground_cache,
        schemes=engine.schemes,
    )
    new_goal = normalize(clause.goal, local_engine)
    return Clause(clause.assumptions, new_goal)


# def clause_solved(clause: Clause) -> bool:
#     match clause.goal:
#         case Fun("eq", (l, r)):
#             return l is r
#     return False


def clause_solved(clause: Clause) -> bool:
    return clause.goal == true


def split_clause(clause: Clause) -> list[Clause]:
    """Split an if-goal into proof branches."""
    match clause.goal:
        case Fun("if", (cond, then_branch, else_branch)):
            match cond:
                case Fun("eq", (left, right)):
                    then_assumptions = clause.assumptions + ((left, right),)
                    return [
                        Clause(then_assumptions, then_branch),
                        Clause(clause.assumptions, else_branch),
                    ]
                case _:
                    return [
                        Clause(clause.assumptions, then_branch),
                        Clause(clause.assumptions, else_branch),
                    ]
        case _:
            return [clause]


def _prove_kernel(
    clause: Clause,
    engine: Engine,
    depth: int,
    induction_handler=None,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    if proof_node is not None:
        proof_node.note = f"depth={depth}"
    if depth <= 0:
        if proof_node is not None:
            proof_node.solved = False
        return False

    simplified = simplify_clause(clause, engine)
    if proof_node is not None:
        proof_node.children.append(_new_node("simplify", simplified))
    if clause_solved(simplified):
        if proof_node is not None:
            proof_node.solved = True
        return True

    branches = split_clause(simplified)
    if len(branches) == 1:
        if induction_handler is not None:
            induced = induction_handler(simplified, depth, proof_node)
            if induced is not None:
                if proof_node is not None:
                    proof_node.solved = induced
                return induced
        if proof_node is not None:
            proof_node.solved = False
        return False

    next_depth = depth - 1
    branch_results = []
    for i, branch in enumerate(branches):
        child = _new_node("branch", branch, note=f"index={i}")
        if proof_node is not None:
            proof_node.children.append(child)
        branch_results.append(_prove_kernel(branch, engine, next_depth, induction_handler, child))
    out = all(branch_results)
    if proof_node is not None:
        proof_node.solved = out
    return out


def prove(clause: Clause, engine: Engine, depth: int = 5, proof_node: Optional[ProofNode] = None) -> bool:
    return _prove_kernel(clause, engine, depth, proof_node=proof_node)


def prove_with_induction(
    clause: Clause,
    engine: Engine,
    var: Var,
    scheme: InductionScheme,
    depth: int = 5,
    induction_depth: int = 1,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    if not var_matches_scheme(var, scheme):
        if proof_node is not None:
            proof_node.solved = False
            proof_node.note = f"sort mismatch for scheme {scheme.name}"
        return False

    def induction_handler(simplified_clause: Clause, current_depth: int, current_node: Optional[ProofNode]):
        if induction_depth <= 0:
            return False
        branches = induction_branches(simplified_clause, var, scheme)
        if not branches:
            return False
        induction_node = _new_node("induction", simplified_clause, note=f"var={var.name}, scheme={scheme.name}")
        if current_node is not None:
            current_node.children.append(induction_node)
        next_induction = induction_depth - 1
        branch_results = []
        for i, branch in enumerate(branches):
            child = _new_node("induction-branch", branch, note=f"index={i}")
            induction_node.children.append(child)
            branch_results.append(
                prove_with_induction(branch, engine, var, scheme, current_depth, next_induction, child)
            )
        induction_node.solved = all(branch_results)
        return induction_node.solved

    return _prove_kernel(clause, engine, depth, induction_handler, proof_node)


def prove_with_registered_induction(
    clause: Clause,
    engine: Engine,
    var: Var,
    scheme_name: str,
    depth: int = 5,
    induction_depth: int = 1,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    scheme = get_induction_scheme(engine, scheme_name)
    if scheme is None:
        if proof_node is not None:
            proof_node.solved = False
            proof_node.note = f"unknown scheme {scheme_name}"
        return False
    return prove_with_induction(clause, engine, var, scheme, depth, induction_depth, proof_node)


def prove_with_trace(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    var: Optional[Var] = None,
    scheme: Optional[InductionScheme] = None,
    scheme_name: Optional[str] = None,
    induction_depth: int = 1,
) -> tuple[bool, ProofTrace]:
    trace = ProofTrace()
    root = _new_node("prove", clause)
    trace.roots.append(root)

    if var is None:
        ok = prove(clause, engine, depth=depth, proof_node=root)
        return ok, trace
    if scheme is not None:
        ok = prove_with_induction(
            clause, engine, var, scheme, depth=depth, induction_depth=induction_depth, proof_node=root
        )
        return ok, trace
    if scheme_name is not None:
        ok = prove_with_registered_induction(
            clause, engine, var, scheme_name, depth=depth, induction_depth=induction_depth, proof_node=root
        )
        return ok, trace

    root.note = "missing scheme for induction trace"
    root.solved = False
    return False, trace


# -----------------------------------------------------------------------------
# Trusted proof checking + certificates
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class ProofCertificate:
    clause: Clause
    simplified: Clause
    step: str  # solved | split | induction
    children: Tuple["ProofCertificate", ...] = ()
    var: Optional[Var] = None
    scheme_name: Optional[str] = None


def _local_engine_for_clause(clause: Clause, engine: Engine) -> Engine:
    return make_engine(
        rules=engine.rules,
        ctx=Context(clause.assumptions, ()),
        trace=engine.trace,
        fuel=engine.fuel,
        config=engine.config,
        ground_cache=engine.ground_cache,
        schemes=engine.schemes,
    )


def _check_simplify_step(clause: Clause, engine: Engine) -> Clause:
    return simplify_clause(clause, engine)


def _check_split_step(clause: Clause) -> list[Clause]:
    return split_clause(clause)


def _check_induction_step(clause: Clause, var: Var, scheme: InductionScheme) -> list[Clause]:
    branches = induction_branches(clause, var, scheme)
    if not branches:
        raise ValueError("Induction does not apply to this goal/scheme.")
    return branches


def _goal_holds_in_assumptions(clause: Clause, engine: Engine) -> bool:
    eq_goal = goal_equality(clause.goal)
    if eq_goal is None:
        return False
    l, r = eq_goal
    local = _local_engine_for_clause(clause, engine)
    return local.holds(l, r)


def _check_exact_step(clause: Clause, engine: Engine) -> Clause:
    if clause_solved(clause) or _goal_holds_in_assumptions(clause, engine):
        return Clause(clause.assumptions, true)
    raise ValueError("Goal is not solved and does not follow from assumptions.")


def _check_rewrite_step(clause: Clause, rule: Rule, engine: Engine) -> Clause:
    local = _local_engine_for_clause(clause, engine)
    rewritten = local.rewrite_once(clause.goal, rule)
    if rewritten is None:
        raise ValueError("Rewrite rule does not apply to current goal.")
    return Clause(clause.assumptions, rewritten)


def _prove_certificate_kernel(
    clause: Clause,
    engine: Engine,
    depth: int,
    var: Optional[Var],
    scheme: Optional[InductionScheme],
    induction_depth: int,
) -> Optional[ProofCertificate]:
    if depth <= 0:
        return None

    simplified = _check_simplify_step(clause, engine)
    if clause_solved(simplified):
        return ProofCertificate(clause=clause, simplified=simplified, step="solved")

    branches = _check_split_step(simplified)
    if len(branches) > 1:
        children: list[ProofCertificate] = []
        for branch in branches:
            child = _prove_certificate_kernel(branch, engine, depth - 1, var, scheme, induction_depth)
            if child is None:
                return None
            children.append(child)
        return ProofCertificate(clause=clause, simplified=simplified, step="split", children=tuple(children))

    if var is not None and scheme is not None and induction_depth > 0:
        induction_goals = induction_branches(simplified, var, scheme)
        if induction_goals:
            children = []
            for branch in induction_goals:
                child = _prove_certificate_kernel(branch, engine, depth, var, scheme, induction_depth - 1)
                if child is None:
                    return None
                children.append(child)
            return ProofCertificate(
                clause=clause,
                simplified=simplified,
                step="induction",
                children=tuple(children),
                var=var,
                scheme_name=scheme.name,
            )

    return None


def prove_checked(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    var: Optional[Var] = None,
    scheme: Optional[InductionScheme] = None,
    scheme_name: Optional[str] = None,
    induction_depth: int = 1,
) -> tuple[bool, Optional[ProofCertificate]]:
    if var is not None and scheme is None and scheme_name is not None:
        scheme = get_induction_scheme(engine, scheme_name)
    if var is not None and scheme is None:
        return False, None
    if var is not None and scheme is not None and not var_matches_scheme(var, scheme):
        return False, None

    cert = _prove_certificate_kernel(clause, engine, depth, var, scheme, induction_depth)
    return cert is not None, cert


def _check_certificate_node(
    cert: ProofCertificate,
    engine: Engine,
    depth: int,
    induction_depth: int,
) -> bool:
    if depth <= 0:
        return False

    expected_simplified = _check_simplify_step(cert.clause, engine)
    if expected_simplified != cert.simplified:
        return False

    if cert.step == "solved":
        return clause_solved(cert.simplified) and not cert.children

    if cert.step == "split":
        branches = _check_split_step(cert.simplified)
        if len(branches) <= 1 or len(branches) != len(cert.children):
            return False
        if any(child.clause != branch for child, branch in zip(cert.children, branches)):
            return False
        return all(_check_certificate_node(child, engine, depth - 1, induction_depth) for child in cert.children)

    if cert.step == "induction":
        if cert.var is None or cert.scheme_name is None or induction_depth <= 0:
            return False
        scheme = get_induction_scheme(engine, cert.scheme_name)
        if scheme is None or not var_matches_scheme(cert.var, scheme):
            return False
        branches = induction_branches(cert.simplified, cert.var, scheme)
        if len(branches) != len(cert.children):
            return False
        if any(child.clause != branch for child, branch in zip(cert.children, branches)):
            return False
        return all(_check_certificate_node(child, engine, depth, induction_depth - 1) for child in cert.children)

    return False


def check_certificate(
    cert: ProofCertificate,
    engine: Engine,
    depth: int = 5,
    induction_depth: int = 1,
) -> bool:
    return _check_certificate_node(cert, engine, depth, induction_depth)


def _certificate_to_proof_node(cert: ProofCertificate) -> ProofNode:
    note = ""
    if cert.step == "induction":
        note = f"var={cert.var.name if cert.var is not None else '?'}, scheme={cert.scheme_name}"
    node = _new_node(f"checked-{cert.step}", cert.clause, note=note)
    node.children.append(_new_node("checked-simplify", cert.simplified))
    for child in cert.children:
        node.children.append(_certificate_to_proof_node(child))
    if cert.step == "solved":
        node.solved = True
    else:
        node.solved = all(c.solved is True for c in node.children[1:]) if cert.children else False
    return node


def certificate_to_proof_trace(cert: ProofCertificate) -> ProofTrace:
    trace = ProofTrace()
    trace.roots.append(_certificate_to_proof_node(cert))
    return trace


@dataclass(frozen=True)
class Lemma:
    name: str
    clause: Clause
    certificate: ProofCertificate


def _contains_symbol(term: Term, symbol: str) -> bool:
    match term:
        case Var():
            return False
        case Fun(sym, args):
            if sym == symbol:
                return True
            return any(_contains_symbol(a, symbol) for a in args)


class TheoremEnvironment:
    def __init__(self, engine: Engine, base_rules: list[Rule]):
        self.engine = engine
        self.base_rules: list[Rule] = list(base_rules)
        self.lemmas: Dict[str, Lemma] = {}
        self.definitions: Dict[str, Rule] = {}
        self.lemma_rewrites: Dict[str, Rule] = {}
        self.scoped_rule_sets: Dict[str, list[Rule]] = {}
        self.active_scopes: set[str] = set()

    def _sync_engine_rules(self):
        active_rules = list(self.base_rules)
        for scope, rules in self.scoped_rule_sets.items():
            if scope in self.active_scopes:
                active_rules.extend(rules)
        self.engine.reset_rules(active_rules)

    def create_scope(self, name: str):
        self.scoped_rule_sets.setdefault(name, [])

    def activate_scope(self, name: str):
        if name not in self.scoped_rule_sets:
            raise ValueError(f"Unknown scope: {name}")
        self.active_scopes.add(name)
        self._sync_engine_rules()

    def deactivate_scope(self, name: str):
        self.active_scopes.discard(name)
        self._sync_engine_rules()

    def register_lemma(self, lemma: Lemma, depth: int = 12, induction_depth: int = 2):
        if lemma.clause.assumptions:
            raise ValueError("Only assumption-free lemmas can be registered in this minimal environment.")
        if goal_equality(lemma.clause.goal) is None:
            raise ValueError("Lemma goal must be an equality.")
        if lemma.certificate.clause != lemma.clause:
            raise ValueError("Lemma certificate root does not match lemma clause.")
        if not check_certificate(lemma.certificate, self.engine, depth=depth, induction_depth=induction_depth):
            raise ValueError("Lemma certificate failed validation.")
        self.lemmas[lemma.name] = lemma

    def register_definition(self, name: str, lhs: Term, rhs: Term, scope: str = "definitions"):
        match lhs:
            case Fun(sym, _):
                if _contains_symbol(rhs, sym):
                    raise ValueError("Recursive definitions are not supported in this phase.")
                assert self.engine.config is not None
                if sym not in self.engine.config.precedence:
                    base = max(self.engine.config.precedence.values(), default=0)
                    self.engine.config.precedence[sym] = base + 1
            case _:
                raise ValueError("Definition lhs must be a function application.")
        rule = Rule(lhs, rhs)
        self.definitions[name] = rule
        self.scoped_rule_sets.setdefault(scope, []).append(rule)
        if scope in self.active_scopes:
            self._sync_engine_rules()

    def register_lemma_rewrite(
        self,
        lemma_name: str,
        scope: str = "lemmas",
        orientation: str = "auto",
    ) -> Rule:
        lemma = self.lemmas.get(lemma_name)
        if lemma is None:
            raise ValueError(f"Unknown lemma: {lemma_name}")
        eq_goal = goal_equality(lemma.clause.goal)
        if eq_goal is None:
            raise ValueError("Lemma goal must be an equality.")
        lhs, rhs = eq_goal
        assert self.engine.config is not None

        if orientation == "auto":
            if _decreases(self.engine.config, lhs, rhs):
                rule = Rule(lhs, rhs)
            elif _decreases(self.engine.config, rhs, lhs):
                rule = Rule(rhs, lhs)
            else:
                raise ValueError("Lemma cannot be oriented into a decreasing rewrite rule.")
        elif orientation == "lhs_to_rhs":
            if not _decreases(self.engine.config, lhs, rhs):
                raise ValueError("Requested orientation lhs_to_rhs is not decreasing.")
            rule = Rule(lhs, rhs)
        elif orientation == "rhs_to_lhs":
            if not _decreases(self.engine.config, rhs, lhs):
                raise ValueError("Requested orientation rhs_to_lhs is not decreasing.")
            rule = Rule(rhs, lhs)
        else:
            raise ValueError(f"Unknown orientation: {orientation}")

        self.lemma_rewrites[lemma_name] = rule
        self.scoped_rule_sets.setdefault(scope, []).append(rule)
        if scope in self.active_scopes:
            self._sync_engine_rules()
        return rule


class ProofSession:
    def __init__(self, clause: Clause, engine: Engine):
        self.engine = engine
        self.goals: list[Clause] = [clause]
        self.theory = get_theorem_environment(engine)
        self.lemmas = self.theory.lemmas
        self.trace = ProofTrace()
        self._trace_root = _new_node("session", clause, note="interactive")
        self.trace.roots.append(self._trace_root)

    def _record(self, kind: str, clause: Clause, note: str = "", solved: Optional[bool] = None, children: Optional[list[ProofNode]] = None):
        node = _new_node(kind, clause, note=note)
        if children:
            node.children.extend(children)
        node.solved = solved
        self._trace_root.children.append(node)

    def current_goal(self) -> Optional[Clause]:
        if not self.goals:
            return None
        return self.goals[0]

    def _replace_current(self, new_goals: list[Clause]):
        self.goals = new_goals + self.goals[1:]

    def simp(self):
        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        simplified = _check_simplify_step(original, self.engine)
        if clause_solved(simplified):
            self._record("session-simp", original, note="discharged", solved=True, children=[_new_node("goal", simplified)])
            self.goals = self.goals[1:]
            return
        self._record("session-simp", original, solved=False, children=[_new_node("goal", simplified)])
        self.goals[0] = simplified

    def split(self):
        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        branches = _check_split_step(original)
        kids = [_new_node("session-branch", b, note=f"index={i}") for i, b in enumerate(branches)]
        self._record("session-split", original, note=f"branches={len(branches)}", children=kids)
        self._replace_current(branches)

    def induct(self, var: Var, scheme: Optional[InductionScheme] = None, scheme_name: Optional[str] = None):
        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        chosen = scheme
        if chosen is None and scheme_name is not None:
            chosen = get_induction_scheme(self.engine, scheme_name)
        if chosen is None:
            raise ValueError("No induction scheme provided.")
        branches = _check_induction_step(original, var, chosen)
        kids = [_new_node("induction-branch", b, note=f"index={i}") for i, b in enumerate(branches)]
        self._record("session-induct", original, note=f"var={var.name}, scheme={chosen.name}", children=kids)
        self._replace_current(branches)

    def rewrite(self, rule: Rule):
        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        rewritten = _check_rewrite_step(original, rule, self.engine)
        self._record("session-rewrite", original, note=f"{rule.lhs} -> {rule.rhs}", children=[_new_node("goal", rewritten)])
        self.goals[0] = rewritten

    def exact(self):
        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        solved = _check_exact_step(original, self.engine)
        self._record("session-exact", original, solved=True, children=[_new_node("goal", solved)])
        self.goals = self.goals[1:]

    def register_lemma(self, lemma: Lemma, depth: int = 12, induction_depth: int = 2):
        self.theory.register_lemma(lemma, depth=depth, induction_depth=induction_depth)

    def apply_lemma(self, name: str):
        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        lemma = self.theory.lemmas.get(name)
        if lemma is None:
            raise ValueError(f"Unknown lemma: {name}")
        eq_goal = goal_equality(lemma.clause.goal)
        assert eq_goal is not None
        cur = original
        assumptions = cur.assumptions + (eq_goal,)
        next_goal = Clause(assumptions, cur.goal)
        self._record("session-apply-lemma", original, note=name, children=[_new_node("goal", next_goal)])
        self.goals[0] = next_goal

    def register_definition(self, name: str, lhs: Term, rhs: Term, scope: str = "definitions"):
        self.theory.register_definition(name, lhs, rhs, scope=scope)

    def register_lemma_rewrite(self, lemma_name: str, scope: str = "lemmas", orientation: str = "auto"):
        self.theory.register_lemma_rewrite(lemma_name, scope=scope, orientation=orientation)

    def activate_scope(self, name: str):
        self.theory.activate_scope(name)
        self._record("session-activate-scope", self.current_goal() or Clause((), true), note=name)

    def deactivate_scope(self, name: str):
        self.theory.deactivate_scope(name)
        self._record("session-deactivate-scope", self.current_goal() or Clause((), true), note=name)

    def qed(self) -> bool:
        done = not self.goals
        current = self.current_goal() or Clause((), true)
        self._record("session-qed", current, solved=done)
        return done


# -----------------------------------------------------------------------------
# Tests
# -----------------------------------------------------------------------------

if __name__ == "__main__":
    reset_var_interner()
    x = V("x")
    y = V("y")
    z = V("z")
    x_nat = V("xn", "Nat")
    xs = V("xs", "List")
    h = V("h")
    t = V("t")

    zero = Const("0")
    one = Const("1")
    
    S = lambda t: App("S", t)
    add = lambda a, b: App("add", a, b)
    nil = Const("nil")
    cons = lambda a, b: App("cons", a, b)
    app = lambda a, b: App("append", a, b)
    length = lambda a: App("length", a)
    eq = lambda a, b: App("eq", a, b)
    neq = lambda a,b:App("neq",a,b)
    f = lambda a: App("f", a)
    ite = lambda c,t,e:App("if",c,t,e)

    r1 = Rule(add(zero, y), y)
    r2 = Rule(add(S(x), y), S(add(x, y)))
    r3 = Rule(f(x), one, conditions=((x, zero),))

    r4 = Rule(app(nil, xs), xs)
    r5 = Rule(app(cons(h, t), xs), cons(h, app(t, xs)))
    r6 = Rule(length(nil), zero)
    r7 = Rule(length(cons(h, t)), S(length(t)))
    r8 = Rule(add(x, zero), x)
    r9 = Rule(add(x, S(y)), S(add(x, y)))

    rules = builtin_rules() + [r1, r2, r3, r4, r5, r6, r7, r8, r9]
    shared_cache: Dict[Term, Term] = {}
    shared_schemes: Dict[str, InductionScheme] = {}
    shared_config = default_engine_config()
    engine = make_engine(rules=rules, config=shared_config, ground_cache=shared_cache, schemes=shared_schemes)

    # Test 1
    t = add(S(S(zero)), S(zero))
    res = normalize(t, engine)
    print("Result:", res)
    assert str(res) == "S(S(S(0)))"

    # Test 2
    assert App("f", x) is App("f", x)

    # Test 3
    assert str(apply_subst(add(x, y), {x: zero})) == "add(0, y)"

    # Test 4
    m = match(add(x, y), add(zero, S(zero)))
    assert m[x] is zero

    # Test 5
    assert str(normalize(add(y, add(x, z)), engine)) == "add(x, add(y, z))"

    # Test 6
    tr = Trace()
    tr_engine = make_engine(rules=rules, trace=tr, config=shared_config, ground_cache=shared_cache, schemes=shared_schemes)
    normalize(add(S(zero), zero), tr_engine)
    assert len(tr.steps) > 0

    # Test 7
    clause = Clause(((x, zero),), add(x, S(zero)))
    simplified = simplify_clause(clause, engine)
    assert str(simplified.goal) == "S(0)"

    # Test 8
    clause2 = Clause((), eq(zero, zero))
    print(simplify_clause(clause2, engine))
    assert clause_solved(simplify_clause(clause2, engine))

    # Test 9
    t = add(zero, zero)
    r = normalize(t, engine)
    assert t in shared_cache
    assert shared_cache[t] is r

    # Test 10
    t = add(zero, zero)
    r1n = normalize(t, engine)
    r2n = normalize(t, engine)
    assert r1n is r2n

    # Test 11
    assert str(normalize(f(zero), engine)) == "1"
    assert str(normalize(f(S(zero)), engine)) == "f(S(0))"

    # Test 12
    assert normalize(eq(zero,zero), engine) == true
    assert normalize(neq(zero,zero), engine) == false

    # Test 13: equality closure x = y, y = 0 => x = 0
    clause3 = Clause(((x, y), (y, zero)), eq(x, zero))
    assert clause_solved(simplify_clause(clause3, engine))

    # Test 14: induction obligations for nat produce base + step (with IH)
    nat_scheme = nat_induction_scheme(zero)
    list_scheme = list_induction_scheme()
    clause4 = Clause((), eq(add(x, zero), x))
    branches = induction_branches(clause4, x, nat_scheme)
    assert len(branches) == 2
    assert str(branches[0].goal) == "eq(add(0, 0), 0)"
    assert str(branches[1].goal) == "eq(add(S(x_ih_0), 0), S(x_ih_0))"
    assert len(branches[1].assumptions) == 1
    ih_l, ih_r = branches[1].assumptions[0]
    assert str(ih_l) == "add(x_ih_0, 0)"
    assert str(ih_r) == "x_ih_0"

    # Test 15: prove add(x, 0) = x by explicit nat induction
    assert prove_with_induction(clause4, engine, x, nat_scheme, depth=8, induction_depth=1)

    # Test 16: a clearly false ground goal is not proven
    bad = Clause((), eq(add(zero, one), zero))
    assert not prove(bad, engine, depth=8)

    # Test 17: sort mismatch blocks induction
    assert not prove_with_induction(clause4, engine, xs, nat_scheme, depth=8, induction_depth=1)
    assert not induction_branches(clause4, xs, nat_scheme)

    # Test 18: scheme registry lookup and proof
    register_induction_scheme(engine, nat_scheme)
    register_induction_scheme(engine, list_scheme)
    assert get_induction_scheme(engine, "nat") is nat_scheme
    assert get_induction_scheme_for_sort(engine, "List") is list_scheme
    assert prove_with_registered_induction(clause4, engine, x_nat, "nat", depth=8, induction_depth=1)
    assert not prove_with_registered_induction(clause4, engine, x_nat, "list", depth=8, induction_depth=1)

    # Test 19: list induction branch shape
    list_goal = Clause((), eq(app(xs, nil), xs))
    list_branches = induction_branches(list_goal, xs, list_scheme)
    assert len(list_branches) == 2
    assert str(list_branches[0].goal) == "eq(append(nil, nil), nil)"
    assert str(list_branches[1].goal) == "eq(append(cons(xs_cons_arg_0, xs_ih_0), nil), cons(xs_cons_arg_0, xs_ih_0))"
    assert len(list_branches[1].assumptions) == 1
    ih_l2, ih_r2 = list_branches[1].assumptions[0]
    assert str(ih_l2) == "append(xs_ih_0, nil)"
    assert str(ih_r2) == "xs_ih_0"

    # Test 20: prove append(xs, nil) = xs by explicit list induction
    assert prove_with_induction(list_goal, engine, xs, list_scheme, depth=10, induction_depth=1)

    # Test 21: prove append associativity by list induction
    ys = V("ys", "List")
    zs = V("zs", "List")
    assoc_goal = Clause((), eq(app(app(xs, ys), zs), app(xs, app(ys, zs))))
    assert prove_with_induction(assoc_goal, engine, xs, list_scheme, depth=12, induction_depth=1)

    # Test 22: prove length(append(xs, nil)) = length(xs) by list induction
    len_append_nil_goal = Clause((), eq(length(app(xs, nil)), length(xs)))
    assert prove_with_induction(len_append_nil_goal, engine, xs, list_scheme, depth=12, induction_depth=1)

    # Test 23: prove length(append(xs, ys)) = add(length(xs), length(ys))
    len_append_goal = Clause((), eq(length(app(xs, ys)), add(length(xs), length(ys))))
    assert prove_with_induction(len_append_goal, engine, xs, list_scheme, depth=14, induction_depth=1)

    # Test 24: shared cache can be reused across engines
    term_shared = add(zero, zero)
    a = make_engine(rules=rules, config=shared_config, ground_cache=shared_cache, schemes=shared_schemes)
    b = make_engine(rules=rules, config=shared_config, ground_cache=shared_cache, schemes=shared_schemes)
    normalize(term_shared, a)
    assert term_shared in shared_cache
    assert normalize(term_shared, b) is shared_cache[term_shared]

    # Test 25: isolated caches are independent
    iso_a_cache: Dict[Term, Term] = {}
    iso_b_cache: Dict[Term, Term] = {}
    iso_a = make_engine(rules=rules, config=shared_config, ground_cache=iso_a_cache, schemes=shared_schemes)
    iso_b = make_engine(rules=rules, config=shared_config, ground_cache=iso_b_cache, schemes=shared_schemes)
    normalize(term_shared, iso_a)
    assert term_shared in iso_a_cache
    assert term_shared not in iso_b_cache

    # Test 26: per-engine config isolation (AC metadata)
    no_ac_config = EngineConfig(precedence=shared_config.precedence, assoc=set(), comm=set())
    no_ac_engine = make_engine(rules=rules, config=no_ac_config, ground_cache={}, schemes={})
    assert str(normalize(add(y, add(x, z)), no_ac_engine)) == "add(y, add(x, z))"
    assert str(normalize(add(y, add(x, z)), engine)) == "add(x, add(y, z))"

    # Test 27: variable interning returns canonical identities
    vx1 = V("vx")
    vx2 = V("vx")
    assert vx1 is vx2
    vn1 = V("vn", "Nat")
    vn2 = V("vn", "Nat")
    assert vn1 is vn2

    # Test 28: strict same-name sort conflicts raise immediately
    reset_var_interner()
    _ = V("u")
    try:
        V("u", "Nat")
        assert False
    except ValueError:
        pass
    reset_var_interner()
    _ = V("u", "Nat")
    try:
        V("u", "List")
        assert False
    except ValueError:
        pass

    # Re-establish interned vars used in prior prover tests if extended below
    reset_var_interner()
    x = V("x")
    y = V("y")
    z = V("z")
    x_nat = V("xn", "Nat")
    xs = V("xs", "List")
    h = V("h")
    t = V("t")

    # Test 29: proof trace captures induction events and renders nicely
    ok_trace, ptrace = prove_with_trace(assoc_goal, engine, depth=12, var=xs, scheme=list_scheme, induction_depth=1)
    assert ok_trace
    rendered = render_proof_trace(ptrace)
    assert "induction" in rendered
    assert "scheme=list" in rendered
    assert "induction-branch" in rendered

    # Test 30: checked proof certificate can be produced and replay-validated
    ok_cert, cert = prove_checked(clause4, engine, depth=8, var=x, scheme=nat_scheme, induction_depth=1)
    assert ok_cert and cert is not None
    assert check_certificate(cert, engine, depth=8, induction_depth=1)

    # Test 31: tampered certificates are rejected by checker
    bad_cert = ProofCertificate(
        clause=cert.clause,
        simplified=Clause(cert.simplified.assumptions, false),
        step=cert.step,
        children=cert.children,
        var=cert.var,
        scheme_name=cert.scheme_name,
    )
    assert not check_certificate(bad_cert, engine, depth=8, induction_depth=1)

    # Test 32: interactive session can prove add(x, 0) = x by induction
    sess = ProofSession(clause4, engine)
    sess.induct(x, scheme=nat_scheme)
    while sess.goals:
        sess.simp()
        if sess.goals:
            sess.exact()
    assert sess.qed()

    # Test 33: interactive session supports checked lemma registration/application
    lemma = Lemma("add_right_id", clause4, cert)
    sess2 = ProofSession(Clause((), eq(add(S(zero), zero), S(zero))), engine)
    sess2.register_lemma(lemma, depth=8, induction_depth=1)
    sess2.apply_lemma("add_right_id")
    sess2.simp()
    if sess2.goals:
        sess2.exact()
    assert sess2.qed()

    # Test 34: certificates can be rendered through proof-trace adapter
    ok_assoc_cert, assoc_cert = prove_checked(assoc_goal, engine, depth=12, var=xs, scheme=list_scheme, induction_depth=1)
    assert ok_assoc_cert and assoc_cert is not None
    cert_trace = certificate_to_proof_trace(assoc_cert)
    cert_rendered = render_proof_trace(cert_trace)
    assert "checked-induction" in cert_rendered
    assert "checked-simplify" in cert_rendered

    # Test 35: interactive session produces a readable proof trace
    sess_trace_rendered = render_proof_trace(sess.trace)
    assert "session-induct" in sess_trace_rendered
    assert "session-simp" in sess_trace_rendered
    assert "session-exact" in sess_trace_rendered

    # Test 36: theorem environment supports scoped lemma rewrites
    scoped_rules = builtin_rules() + [r1, r2, r4, r5]
    scoped_engine = make_engine(rules=scoped_rules, config=shared_config, ground_cache={}, schemes={})
    scoped_theory = get_theorem_environment(scoped_engine)
    scoped_list = list_induction_scheme()
    register_induction_scheme(scoped_engine, scoped_list)
    scoped_clause = Clause((), eq(app(xs, nil), xs))
    ok_scoped_cert, scoped_cert = prove_checked(
        scoped_clause, scoped_engine, depth=10, var=xs, scheme=scoped_list, induction_depth=1
    )
    assert ok_scoped_cert and scoped_cert is not None
    scoped_lemma = Lemma("append_right_id_scoped", scoped_clause, scoped_cert)
    scoped_theory.register_lemma(scoped_lemma, depth=10, induction_depth=1)
    scoped_theory.register_lemma_rewrite("append_right_id_scoped", scope="list_scope", orientation="auto")
    assert str(normalize(app(xs, nil), scoped_engine)) == "append(xs, nil)"
    scoped_theory.activate_scope("list_scope")
    assert str(normalize(app(xs, nil), scoped_engine)) == "xs"
    scoped_theory.deactivate_scope("list_scope")
    assert str(normalize(app(xs, nil), scoped_engine)) == "append(xs, nil)"

    # Test 37: theorem environment supports non-recursive definitions in scopes
    scoped_theory.register_definition("double", App("double", x), add(x, x), scope="def_scope")
    scoped_theory.activate_scope("def_scope")
    assert str(normalize(App("double", S(zero)), scoped_engine)) == "S(S(0))"
    try:
        scoped_theory.register_definition("bad_recursive", App("fdef", x), App("fdef", x), scope="def_scope")
        assert False
    except ValueError:
        pass
    scoped_theory.deactivate_scope("def_scope")

    # Test 38: non-orientable lemma rewrites are rejected
    reflexive_clause = Clause((), eq(add(x, y), add(x, y)))
    ok_refl, refl_cert = prove_checked(reflexive_clause, engine, depth=6)
    assert ok_refl and refl_cert is not None
    refl_lemma = Lemma("add_refl", reflexive_clause, refl_cert)
    scoped_theory.register_lemma(refl_lemma, depth=6, induction_depth=1)
    try:
        scoped_theory.register_lemma_rewrite("add_refl", scope="list_scope", orientation="auto")
        assert False
    except ValueError:
        pass

    # Test 39: ProofSession can drive scope activation/deactivation
    sess3 = ProofSession(Clause((), eq(app(xs, nil), xs)), scoped_engine)
    sess3.activate_scope("list_scope")
    sess3.simp()
    assert sess3.qed()
    sess3.deactivate_scope("list_scope")

    print("\nAppend associativity proof trace:")
    print(rendered)

    print("All tests passed.")
