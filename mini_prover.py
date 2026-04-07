from __future__ import annotations

"""
mini_prover.py
==============

A compact first-order prover with rewriting, congruence closure, and induction.

The main workflow is:
1. Build terms with `V`, `Const`, and `App`.
2. Configure the prover with `configure_prover(...)`.
3. Normalize terms with `normalize(...)`.
4. Prove clauses with `prove(...)` or `prove_with_induction(...)`.
5. Render proof structure with `render_proof_trace(...)` when needed.
"""

from dataclasses import dataclass, field
from typing import Callable, Dict, Iterator, Optional, Sequence, Tuple, TypeAlias


class Term:
    """Base marker type for all term nodes."""

    pass


@dataclass(frozen=True, slots=True)
class Var(Term):
    """A logical variable with an optional sort tag."""

    name: str
    sort: Optional[str] = None

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True, slots=True)
class Fun(Term):
    """A function symbol applied to zero or more argument terms."""

    symbol: str
    args: Tuple[Term, ...]

    def __str__(self) -> str:
        if not self.args:
            return self.symbol
        return f"{self.symbol}({', '.join(map(str, self.args))})"


_VAR_NAME_SORT: Dict[str, Optional[str]] = {}


def reset_var_declarations() -> None:
    """Clear global variable-name sort declarations."""
    _VAR_NAME_SORT.clear()


def reset_var_interner() -> None:
    """Reset declared variable names and sorts."""
    reset_var_declarations()


def V(name: str, sort: Optional[str] = None) -> Var:
    """
     Construct a variable while enforcing consistent sort declarations per name.

    Reusing a name with a different sort raises `ValueError`.
    """
    existing_sort = _VAR_NAME_SORT.get(name)
    if existing_sort is None and name in _VAR_NAME_SORT:
        if sort is not None:
            raise ValueError(
                f"Variable '{name}' already declared with sort None; cannot redeclare with sort '{sort}'."
            )
    elif existing_sort is not None and existing_sort != sort:
        raise ValueError(
            f"Variable '{name}' already declared with sort '{existing_sort}'; cannot redeclare with sort '{sort}'."
        )
    _VAR_NAME_SORT[name] = sort
    return Var(name, sort)


def Const(n: str) -> Fun:
    """Create an arity-0 function term (a constant)."""
    return Fun(n, ())


def App(f: str, *a: Term) -> Fun:
    """Create a function application term."""
    return Fun(f, a)


true = Const("true")
false = Const("false")


Subst = Dict[Var, Term]
TermKey: TypeAlias = tuple[int, str, int, tuple["TermKey", ...]] | tuple[int, str]
RepPriority: TypeAlias = tuple[int, TermKey]


def apply_subst(term: Term, subst: Subst) -> Term:
    """Recursively apply a substitution mapping variables to terms."""
    match term:
        case Var() as v:
            return subst.get(v, v)
        case Fun(f, args):
            return Fun(f, tuple(apply_subst(a, subst) for a in args))
    raise TypeError(f"Unsupported term: {term!r}")


def match(
    pattern: Term, target: Term, subst: Optional[Subst] = None
) -> Optional[Subst]:
    """
    First-order pattern matching.

    Returns a substitution if `pattern` can match `target`, otherwise `None`.
    """
    if subst is None:
        subst = {}

    if pattern == target:
        return subst

    match pattern, target:
        case Var() as v, t:
            if v in subst:
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


@dataclass(frozen=True)
class Rule:
    """A rewrite rule, optionally guarded by equality conditions."""

    lhs: Term
    rhs: Term
    conditions: Tuple[Tuple[Term, Term], ...] = ()
    skip_decrease_check: bool = False


class RuleIndex:
    """Index rules by top symbol to avoid scanning all rules on every rewrite step."""

    def __init__(self, rules: Sequence[Rule]) -> None:
        """Build symbol -> rules mapping; variable-lhs rules live under `None`."""
        self.by_symbol: Dict[Optional[str], list[Rule]] = {}
        for r in rules:
            match r.lhs:
                case Fun(sym, _):
                    self.by_symbol.setdefault(sym, []).append(r)
                case Var():
                    self.by_symbol.setdefault(None, []).append(r)

    def get(self, term: Term) -> list[Rule]:
        """Return candidate rules for this term's head symbol."""
        match term:
            case Fun(sym, _):
                return self.by_symbol.get(sym, []) + self.by_symbol.get(None, [])
            case Var():
                return self.by_symbol.get(None, [])
        raise TypeError(f"Unsupported term: {term!r}")


@dataclass(frozen=True)
class Context:
    """Local assumptions: equalities and disequalities available during normalization.

    Equalities are split into three categories:
    - substitutions: equalities where at least one side is a bare variable (x = t)
    - ground_equalities: equalities with no variables, for EqClasses congruence closure
    - rewrite_equalities: equalities requiring matching (f(x) = g(x), IH-style), for rules
    """

    substitutions: Tuple[Tuple[Term, Term], ...] = ()
    ground_equalities: Tuple[Tuple[Term, Term], ...] = ()
    rewrite_equalities: Tuple[Tuple[Term, Term], ...] = ()
    disequalities: Tuple[Tuple[Term, Term], ...] = ()


@dataclass(frozen=True)
class EngineConfig:
    """Configuration for ordering and AC normalization behavior."""

    precedence: Dict[str, int]
    assoc: set[str]
    comm: set[str]


def default_engine_config() -> EngineConfig:
    """Return default symbol precedence plus AC metadata for arithmetic-style rewrites."""
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


def _prec(config: EngineConfig, f: str) -> int:
    """Lookup precedence for a symbol (default 0 for unknown symbols)."""
    return config.precedence.get(f, 0)


def _lpo_greater(config: EngineConfig, s: Term, t: Term) -> bool:
    """
    Lightweight LPO-style ordering used to orient unconditional rewrites.

    Rewrites are only allowed when they decrease by this order.
    """
    if s == t:
        return False

    match s, t:
        case _, Var():
            return True
        case Var(), Fun():
            return False
        case Fun(f, s_args), Fun(g, t_args):
            if any(_lpo_greater(config, si, t) or si == t for si in s_args):
                return True
            if _prec(config, f) > _prec(config, g) and all(
                _lpo_greater(config, s, ti) for ti in t_args
            ):
                return True
            if f == g:
                for si, ti in zip(s_args, t_args):
                    if si == ti:
                        continue
                    if _lpo_greater(config, si, ti):
                        return True
                    if _lpo_greater(config, ti, si):
                        return False
    return False


def _decreases(config: EngineConfig, a: Term, b: Term) -> bool:
    """Convenience wrapper: true when `a -> b` is a decreasing orientation."""
    return _lpo_greater(config, a, b)


def _term_key(t: Term) -> TermKey:
    """Deterministic structural sort key for terms."""
    match t:
        case Fun(f, args):
            return (0, f, len(args), tuple(_term_key(a) for a in args))
        case Var(n, _):
            return (1, n)
    raise TypeError(f"Unsupported term: {t!r}")


def _rep_priority(t: Term) -> RepPriority:
    """Priority key for choosing class representatives in equality classes."""
    match t:
        case Fun(_, args) if not args:
            return (0, _term_key(t))
        case Var():
            return (1, _term_key(t))
        case Fun():
            return (2, _term_key(t))
    raise TypeError(f"Unsupported term: {t!r}")


def _ac_normalize(config: EngineConfig, t: Term) -> Term:
    """
    Normalize associative/commutative terms into a deterministic shape.

    For symbols marked associative, nested binary trees are flattened/rebuilt.
    For commutative symbols, flattened arguments are sorted first.
    """
    match t:
        case Fun(f, (a, b)) if f in config.assoc:
            flat: list[Term] = []

            def collect(x: Term) -> None:
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


class EqClasses:
    """
    Union-find + congruence closure over observed terms.

    This allows context equalities to imply equalities under function application.
    """

    def __init__(self) -> None:
        """Create empty equivalence-class structures."""
        self.parent: Dict[Term, Term] = {}
        self.rank: Dict[Term, int] = {}
        self.terms: set[Term] = set()
        self.rep: Dict[Term, Term] = {}

    def _ensure(self, t: Term) -> None:
        """Ensure a term is present in the union-find structures."""
        if t not in self.parent:
            self.parent[t] = t
            self.rank[t] = 0
            self.terms.add(t)
            self.rep[t] = t

    def _register(self, t: Term) -> None:
        """Register a term and recursively register all subterms."""
        self._ensure(t)
        match t:
            case Fun(_, args):
                for a in args:
                    self._register(a)

    def find(self, t: Term) -> Term:
        """Find canonical union-find parent with path compression."""
        self._ensure(t)
        p = self.parent[t]
        if p != t:
            self.parent[t] = self.find(p)
        return self.parent[t]

    def union(self, a: Term, b: Term) -> bool:
        """Union two classes; return True iff this merged previously separate classes."""
        self._register(a)
        self._register(b)
        ra = self.find(a)
        rb = self.find(b)
        if ra == rb:
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

    def close_congruence(self) -> None:
        """Close classes under congruence: equal args imply equal function applications."""
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
        """Return the current canonical representative of a term."""
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
        raise TypeError(f"Unsupported term: {t!r}")

    def are_equal(self, a: Term, b: Term) -> bool:
        """Check whether two terms are equal under the current closure."""
        return self.canonical(a) == self.canonical(b)


def _build_eq_classes(ctx: Context, extra_terms: Tuple[Term, ...] = ()) -> EqClasses:
    """Build equality classes from context assumptions plus optional extra terms."""
    eq = EqClasses()
    for l, r in ctx.substitutions:
        eq._register(l)
        eq._register(r)
        eq.union(l, r)
    for l, r in ctx.ground_equalities:
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


def _schematic_rules(ctx: Context, config: EngineConfig) -> Iterator[Rule]:
    """Yield contextual rewrite rules from complex equalities.

    Induction hypothesis rules and lemmas skip the decrease check since
    the termination heuristic may incorrectly reject them.
    Variable-lhs rules are skipped to avoid over-aggressive rewriting.
    """
    for lhs, rhs in ctx.rewrite_equalities:
        oriented_lhs: Term
        oriented_rhs: Term
        if _decreases(config, lhs, rhs):
            oriented_lhs, oriented_rhs = lhs, rhs
        elif _decreases(config, rhs, lhs):
            oriented_lhs, oriented_rhs = rhs, lhs
        else:
            if _term_key(lhs) <= _term_key(rhs):
                oriented_lhs, oriented_rhs = rhs, lhs
            else:
                oriented_lhs, oriented_rhs = lhs, rhs

        # Keep context rewriting readable and stable: avoid variable-lhs rules that
        # match arbitrary terms and can over-rewrite entire goals.
        if isinstance(oriented_lhs, Var):
            continue
        yield Rule(oriented_lhs, oriented_rhs, skip_decrease_check=True)


def builtin_rules() -> list[Rule]:
    """Boolean/equality core rules used by clause simplification and branching."""
    x = V("builtin_x")
    y = V("builtin_y")
    return [
        Rule(App("eq", x, x), true),
        Rule(App("neq", x, x), false),
        Rule(App("if", true, x, y), x),
        Rule(App("if", false, x, y), y),
    ]


def is_ground(t: Term) -> bool:
    """Return True iff the term contains no variables."""
    match t:
        case Var():
            return False
        case Fun(_, args):
            return all(is_ground(a) for a in args)
    raise TypeError(f"Unsupported term: {t!r}")


def _build_context(
    assumptions: Tuple[Tuple[Term, Term], ...],
    disequalities: Tuple[Tuple[Term, Term], ...],
) -> Context:
    """Classify clause assumptions into substitutions, ground equalities, and rewrite rules.

    - **substitutions**: where at least one side is a bare variable (e.g., x = nil)
    - **ground_equalities**: between ground (variable-free) terms
    - **rewrite_equalities**: complex equalities like induction hypotheses

    Substitutions and ground equalities go into EqClasses for congruence closure.
    Rewrite equalities become contextual rewrite rules.
    """
    substitutions: list[Tuple[Term, Term]] = []
    ground_equalities: list[Tuple[Term, Term]] = []
    rewrite_equalities: list[Tuple[Term, Term]] = []
    for lhs, rhs in assumptions:
        if isinstance(lhs, Var) or isinstance(rhs, Var):
            substitutions.append((lhs, rhs))
        elif is_ground(lhs) and is_ground(rhs):
            ground_equalities.append((lhs, rhs))
        else:
            rewrite_equalities.append((lhs, rhs))
    return Context(
        substitutions=tuple(substitutions),
        ground_equalities=tuple(ground_equalities),
        rewrite_equalities=tuple(rewrite_equalities),
        disequalities=disequalities,
    )


@dataclass
class TraceStep:
    """One low-level rewrite step recorded in the rewrite trace."""

    before: Term
    after: Term
    rule: Rule


class Trace:
    """Container for low-level rewrite-step trace events."""

    def __init__(self) -> None:
        """Start with no rewrite events."""
        self.steps: list[TraceStep] = []

    def add(self, b: Term, a: Term, r: Rule) -> None:
        """Append one rewrite event."""
        self.steps.append(TraceStep(b, a, r))


@dataclass(frozen=True)
class Clause:
    """A proof obligation: assumptions imply a goal term."""

    assumptions: Tuple[Tuple[Term, Term], ...]
    goal: Term
    disequalities: Tuple[Tuple[Term, Term], ...] = ()


@dataclass(frozen=True)
class InductionConstructor:
    """One constructor in an induction scheme plus positions that are recursive."""

    symbol: str
    arity: int
    recursive_positions: Tuple[int, ...] = ()


@dataclass(frozen=True)
class InductionScheme:
    """Induction recipe for a sort: base terms and step constructors."""

    name: str
    sort: str
    base_terms: Tuple[Term, ...]
    constructors: Tuple[InductionConstructor, ...]


@dataclass
class ProofNode:
    """Node in a high-level proof-structure tree."""

    kind: str
    clause: Clause
    note: str = ""
    children: list["ProofNode"] = field(default_factory=list)
    solved: Optional[bool] = None


@dataclass
class ProofTrace:
    """Top-level container for proof trees."""

    roots: list[ProofNode] = field(default_factory=list)


def _new_node(kind: str, clause: Clause, note: str = "") -> ProofNode:
    """Small helper to build proof nodes uniformly."""
    return ProofNode(kind=kind, clause=clause, note=note, children=[])


def render_proof_trace(trace: ProofTrace) -> str:
    """Render a proof tree into a readable indented text outline."""
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
        for c in node.children:
            visit(c, indent + 1)

    for r in trace.roots:
        visit(r, 0)
    return "\n".join(lines)


# Global prover configuration used by `normalize(...)` and the proof-search helpers.
GLOBAL_RULES: list[Rule] = []
GLOBAL_RULE_INDEX: RuleIndex = RuleIndex([])
GLOBAL_CONTEXT = Context()
GLOBAL_TRACE: Optional[Trace] = None
GLOBAL_FUEL = 1000
GLOBAL_CONFIG = default_engine_config()
GLOBAL_SCHEMES: Dict[str, InductionScheme] = {}


def configure_prover(
    rules: list[Rule],
    ctx: Context = Context(),
    trace: Optional[Trace] = None,
    fuel: int = 1000,
    config: Optional[EngineConfig] = None,
    schemes: Optional[Dict[str, InductionScheme]] = None,
) -> None:
    """
    Set the global rules, context, tracing, and induction schemes used by the prover.
    """
    global \
        GLOBAL_RULES, \
        GLOBAL_RULE_INDEX, \
        GLOBAL_CONTEXT, \
        GLOBAL_TRACE, \
        GLOBAL_FUEL, \
        GLOBAL_CONFIG, \
        GLOBAL_SCHEMES
    GLOBAL_RULES = list(rules)
    GLOBAL_RULE_INDEX = RuleIndex(GLOBAL_RULES)
    GLOBAL_CONTEXT = ctx
    GLOBAL_TRACE = trace
    GLOBAL_FUEL = fuel
    GLOBAL_CONFIG = config if config is not None else default_engine_config()
    GLOBAL_SCHEMES = schemes if schemes is not None else {}


def _holds_with(
    l: Term,
    r: Term,
    rules: Sequence[Rule],
    rule_index: RuleIndex,
    ctx: Context,
    trace: Optional[Trace],
    fuel: int,
    config: EngineConfig,
) -> bool:
    """Check whether two terms are equal under a supplied local prover configuration."""
    l2 = _normalize_with(l, rules, rule_index, ctx, trace, fuel, config)
    r2 = _normalize_with(r, rules, rule_index, ctx, trace, fuel, config)
    eq = _build_eq_classes(ctx, (l2, r2))
    if _disequal_with(l2, r2, ctx, eq):
        return False
    return eq.are_equal(l2, r2)


def _disequal_with(left: Term, right: Term, ctx: Context, eq: EqClasses) -> bool:
    for ctx_left, ctx_right in ctx.disequalities:
        if eq.are_equal(left, ctx_left) and eq.are_equal(right, ctx_right):
            return True
        if eq.are_equal(left, ctx_right) and eq.are_equal(right, ctx_left):
            return True
    return False


def _conditions_hold(
    conditions: tuple[tuple[Term, Term], ...],
    subst: Subst,
    rules: Sequence[Rule],
    rule_index: RuleIndex,
    ctx: Context,
    trace: Optional[Trace],
    fuel: int,
    config: EngineConfig,
) -> bool:
    """Evaluate all conditional equalities of a rule under a candidate substitution."""
    for l, r in conditions:
        l2 = apply_subst(l, subst)
        r2 = apply_subst(r, subst)
        if not _holds_with(l2, r2, rules, rule_index, ctx, trace, fuel, config):
            return False
    return True


def _rewrite_once(
    term: Term,
    rule: Rule,
    rules: Sequence[Rule],
    rule_index: RuleIndex,
    ctx: Context,
    trace: Optional[Trace],
    fuel: int,
    config: EngineConfig,
) -> Optional[Term]:
    """Try one specific rule on one specific term; return rewritten term or None."""
    subst = match(rule.lhs, term)
    if subst is None:
        return None
    if rule.conditions and not _conditions_hold(
        rule.conditions, subst, rules, rule_index, ctx, trace, fuel, config
    ):
        return None
    new = apply_subst(rule.rhs, subst)
    if not rule.conditions and not _decreases(config, term, new):
        return None
    if trace:
        trace.add(term, new, rule)
    return new


def _rewrite_term(
    term: Term,
    rules: Sequence[Rule],
    rule_index: RuleIndex,
    ctx: Context,
    trace: Optional[Trace],
    fuel: int,
    config: EngineConfig,
) -> Term:
    """
    Rewrite one term layer:
    1) canonicalize with context equalities,
    2) rewrite subterms recursively,
    3) AC-normalize,
    4) try indexed rules,
    5) try context rules.
    """
    eq = _build_eq_classes(ctx, (term,))
    term = eq.canonical(term)

    match term:
        case Fun(f, args):
            args2 = tuple(
                _rewrite_term(a, rules, rule_index, ctx, trace, fuel, config)
                for a in args
            )
            term = Fun(f, args2)

    term = _ac_normalize(config, term)
    term = eq.canonical(term)

    match term:
        case Fun("eq", (left, right)):
            if eq.are_equal(left, right):
                return true
            if _disequal_with(left, right, ctx, eq):
                return false
        case Fun("neq", (left, right)):
            if eq.are_equal(left, right):
                return false
            if _disequal_with(left, right, ctx, eq):
                return true

    for r in rule_index.get(term):
        t2 = _rewrite_once(term, r, rules, rule_index, ctx, trace, fuel, config)
        if t2 is not None:
            return t2

    for r in _schematic_rules(ctx, config):
        t2 = _rewrite_once(term, r, rules, rule_index, ctx, trace, fuel, config)
        if t2 is not None:
            return t2

    return term


def _normalize_with(
    term: Term,
    rules: Sequence[Rule],
    rule_index: RuleIndex,
    ctx: Context,
    trace: Optional[Trace],
    fuel: int,
    config: EngineConfig,
) -> Term:
    """Repeat `_rewrite_term` to fixpoint (or until fuel is exhausted)."""
    for _ in range(fuel):
        t2 = _rewrite_term(term, rules, rule_index, ctx, trace, fuel, config)
        if t2 == term:
            break
        term = t2
    return term


def normalize(term: Term) -> Term:
    """Public normalization entry point using current global prover configuration."""
    return _normalize_with(
        term,
        GLOBAL_RULES,
        GLOBAL_RULE_INDEX,
        GLOBAL_CONTEXT,
        GLOBAL_TRACE,
        GLOBAL_FUEL,
        GLOBAL_CONFIG,
    )


def nat_induction_scheme(
    zero: Optional[Term] = None, succ_symbol: str = "S"
) -> InductionScheme:
    """Standard unary natural-number induction scheme."""
    if zero is None:
        zero = Const("0")
    return InductionScheme(
        name="nat",
        sort="Nat",
        base_terms=(zero,),
        constructors=(InductionConstructor(succ_symbol, 1, (0,)),),
    )


def list_induction_scheme(
    nil_symbol: str = "nil", cons_symbol: str = "cons"
) -> InductionScheme:
    """Standard list induction scheme (recursive in tail position)."""
    return InductionScheme(
        name="list",
        sort="List",
        base_terms=(Const(nil_symbol),),
        constructors=(InductionConstructor(cons_symbol, 2, (1,)),),
    )


def register_induction_scheme(scheme: InductionScheme) -> None:
    """Register an induction scheme in global scheme registry."""
    GLOBAL_SCHEMES[scheme.name] = scheme


def get_induction_scheme(name: str) -> Optional[InductionScheme]:
    """Lookup an induction scheme by name."""
    return GLOBAL_SCHEMES.get(name)


def get_induction_scheme_for_sort(sort: str) -> Optional[InductionScheme]:
    """Lookup first registered induction scheme for a sort."""
    for scheme in GLOBAL_SCHEMES.values():
        if scheme.sort == sort:
            return scheme
    return None


def var_matches_scheme(var: Var, scheme: InductionScheme) -> bool:
    """Return True when variable sort is compatible with an induction scheme."""
    return var.sort is None or var.sort == scheme.sort


def vars_in_term(term: Term) -> set[str]:
    """Collect variable names appearing in a term."""
    match term:
        case Var(n, _):
            return {n}
        case Fun(_, args):
            out: set[str] = set()
            for a in args:
                out |= vars_in_term(a)
            return out
    raise TypeError(f"Unsupported term: {term!r}")


def vars_in_clause(clause: Clause) -> set[str]:
    """Collect all variable names used anywhere in a clause."""
    out = vars_in_term(clause.goal)
    for l, r in clause.assumptions:
        out |= vars_in_term(l)
        out |= vars_in_term(r)
    for l, r in clause.disequalities:
        out |= vars_in_term(l)
        out |= vars_in_term(r)
    return out


def instantiate_clause(clause: Clause, subst: Subst) -> Clause:
    """Apply a substitution to both assumptions and goal of a clause."""
    assumptions = tuple(
        (apply_subst(l, subst), apply_subst(r, subst)) for l, r in clause.assumptions
    )
    disequalities = tuple(
        (apply_subst(l, subst), apply_subst(r, subst)) for l, r in clause.disequalities
    )
    goal = apply_subst(clause.goal, subst)
    return Clause(assumptions, goal, disequalities)


def goal_equality(goal: Term) -> Optional[Tuple[Term, Term]]:
    """Extract (lhs, rhs) when goal is syntactically `eq(lhs, rhs)`."""
    match goal:
        case Fun("eq", (l, r)):
            return (l, r)
    return None


def fresh_var(base: str, used_names: set[str], sort: Optional[str] = None) -> Var:
    """Generate a fresh variable name from a base stem."""
    i = 0
    while True:
        name = f"{base}_{i}"
        if name not in used_names:
            used_names.add(name)
            return V(name, sort)
        i += 1


def induction_branches(
    clause: Clause, var: Var, scheme: InductionScheme
) -> list[Clause]:
    """
    Expand one induction step into concrete branch clauses.

    Step branches receive induction hypotheses as additional assumptions.
    """
    if not var_matches_scheme(var, scheme):
        return []

    used = vars_in_clause(clause).copy()
    branches: list[Clause] = []

    for b in scheme.base_terms:
        branches.append(instantiate_clause(clause, {var: b}))

    for cons in scheme.constructors:
        rec_vars = [
            fresh_var(f"{var.name}_ih", used, scheme.sort)
            for _ in cons.recursive_positions
        ]
        ih_assumptions: list[Tuple[Term, Term]] = []
        for rv in rec_vars:
            ih_goal = instantiate_clause(clause, {var: rv}).goal
            eq = goal_equality(ih_goal)
            if eq is None:
                return []
            ih_assumptions.append(eq)

        args: list[Term] = [
            fresh_var(f"{var.name}_{cons.symbol}_arg", used) for _ in range(cons.arity)
        ]
        for pos, rv in zip(cons.recursive_positions, rec_vars):
            args[pos] = rv

        step_term = App(cons.symbol, *args)
        step_clause = instantiate_clause(clause, {var: step_term})
        branches.append(
            Clause(
                step_clause.assumptions + tuple(ih_assumptions),
                step_clause.goal,
                step_clause.disequalities,
            )
        )

    return branches


def simplify_clause(clause: Clause) -> Clause:
    """Normalize a clause goal under the clause assumptions as local context."""
    local_ctx = _build_context(clause.assumptions, clause.disequalities)
    new_goal = _normalize_with(
        clause.goal,
        GLOBAL_RULES,
        GLOBAL_RULE_INDEX,
        local_ctx,
        GLOBAL_TRACE,
        GLOBAL_FUEL,
        GLOBAL_CONFIG,
    )
    return Clause(clause.assumptions, new_goal, clause.disequalities)


def clause_solved(clause: Clause) -> bool:
    """Solvedness predicate after simplification."""
    return clause.goal == true


def split_clause(clause: Clause) -> list[Clause]:
    """
    Split conditional goals.

    `if(eq(a,b), t, e)` adds `a=b` on the then branch and `a!=b` on the else branch.
    Other booleans branch with `cond=true` and `cond=false`.
    """
    match clause.goal:
        case Fun("if", (cond, then_branch, else_branch)):
            match cond:
                case Fun("eq", (left, right)):
                    then_assumptions = clause.assumptions + ((left, right),)
                    else_disequalities = clause.disequalities + ((left, right),)
                    return [
                        Clause(then_assumptions, then_branch, clause.disequalities),
                        Clause(clause.assumptions, else_branch, else_disequalities),
                    ]
                case _:
                    return [
                        Clause(
                            clause.assumptions + ((cond, true),),
                            then_branch,
                            clause.disequalities,
                        ),
                        Clause(
                            clause.assumptions + ((cond, false),),
                            else_branch,
                            clause.disequalities,
                        ),
                    ]
        case _:
            return [clause]


InductionHandler: TypeAlias = Callable[
    [Clause, int, Optional[ProofNode]], Optional[bool]
]


def _prove_kernel(
    clause: Clause,
    depth: int,
    induction_handler: Optional[InductionHandler] = None,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    """
    Core proof search:
    simplify -> solved check -> split branches -> recurse.
    Optional induction handler can introduce branch obligations when needed.
    """
    if proof_node is not None:
        proof_node.note = f"depth={depth}"
    if depth <= 0:
        if proof_node is not None:
            proof_node.solved = False
        return False

    simplified = simplify_clause(clause)
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
    branch_results: list[bool] = []
    for i, branch in enumerate(branches):
        child = _new_node("branch", branch, note=f"index={i}")
        if proof_node is not None:
            proof_node.children.append(child)
        branch_results.append(
            _prove_kernel(branch, next_depth, induction_handler, child)
        )
    out = all(branch_results)
    if proof_node is not None:
        proof_node.solved = out
    return out


def prove(
    clause: Clause, depth: int = 5, proof_node: Optional[ProofNode] = None
) -> bool:
    """Plain proof search without induction."""
    return _prove_kernel(clause, depth, proof_node=proof_node)


def prove_with_induction(
    clause: Clause,
    var: Var,
    scheme: InductionScheme,
    depth: int = 5,
    induction_depth: int = 1,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    """Proof search with explicit induction on one variable using one scheme."""
    if not var_matches_scheme(var, scheme):
        if proof_node is not None:
            proof_node.solved = False
            proof_node.note = f"sort mismatch for scheme {scheme.name}"
        return False

    def induction_handler(
        simplified_clause: Clause, current_depth: int, current_node: Optional[ProofNode]
    ) -> Optional[bool]:
        if induction_depth <= 0:
            return False
        branches = induction_branches(simplified_clause, var, scheme)
        if not branches:
            return False
        induction_node = _new_node(
            "induction", simplified_clause, note=f"var={var.name}, scheme={scheme.name}"
        )
        if current_node is not None:
            current_node.children.append(induction_node)
        next_induction = induction_depth - 1
        branch_results: list[bool] = []
        for i, branch in enumerate(branches):
            child = _new_node("induction-branch", branch, note=f"index={i}")
            induction_node.children.append(child)
            branch_results.append(
                prove_with_induction(
                    branch, var, scheme, current_depth, next_induction, child
                )
            )
        induction_node.solved = all(branch_results)
        return induction_node.solved

    return _prove_kernel(clause, depth, induction_handler, proof_node)


def prove_with_registered_induction(
    clause: Clause,
    var: Var,
    scheme_name: str,
    depth: int = 5,
    induction_depth: int = 1,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    """Proof search with induction scheme looked up from global registry."""
    scheme = get_induction_scheme(scheme_name)
    if scheme is None:
        if proof_node is not None:
            proof_node.solved = False
            proof_node.note = f"unknown scheme {scheme_name}"
        return False
    return prove_with_induction(clause, var, scheme, depth, induction_depth, proof_node)


def prove_with_trace(
    clause: Clause,
    depth: int = 5,
    var: Optional[Var] = None,
    scheme: Optional[InductionScheme] = None,
    scheme_name: Optional[str] = None,
    induction_depth: int = 1,
) -> tuple[bool, ProofTrace]:
    """Run a proof attempt and return both success flag and proof-structure trace."""
    trace = ProofTrace()
    root = _new_node("prove", clause)
    trace.roots.append(root)

    if var is None:
        ok = prove(clause, depth=depth, proof_node=root)
        return ok, trace
    if scheme is not None:
        ok = prove_with_induction(
            clause,
            var,
            scheme,
            depth=depth,
            induction_depth=induction_depth,
            proof_node=root,
        )
        return ok, trace
    if scheme_name is not None:
        ok = prove_with_registered_induction(
            clause,
            var,
            scheme_name,
            depth=depth,
            induction_depth=induction_depth,
            proof_node=root,
        )
        return ok, trace

    root.note = "missing scheme for induction trace"
    root.solved = False
    return False, trace


if __name__ == "__main__":
    # Example checks for rewriting, simplification, induction, and proof tracing.
    reset_var_declarations()
    x = V("x")
    y = V("y")
    z = V("z")
    x_nat = V("xn", "Nat")
    xs = V("xs", "List")
    h = V("h")
    t = V("t")

    zero = Const("0")
    one = Const("1")

    def S(t: Term) -> Term:
        return App("S", t)

    def add(a: Term, b: Term) -> Term:
        return App("add", a, b)

    nil = Const("nil")

    def cons(a: Term, b: Term) -> Term:
        return App("cons", a, b)

    def app(a: Term, b: Term) -> Term:
        return App("append", a, b)

    def length(a: Term) -> Term:
        return App("length", a)

    def eq(a: Term, b: Term) -> Term:
        return App("eq", a, b)

    def neq(a: Term, b: Term) -> Term:
        return App("neq", a, b)

    def f(a: Term) -> Term:
        return App("f", a)

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
    schemes: Dict[str, InductionScheme] = {}
    config = default_engine_config()
    configure_prover(rules=rules, config=config, schemes=schemes)

    # Rewriting on natural-number addition.
    term = add(S(S(zero)), S(zero))
    res = normalize(term)
    print("Result:", res)
    assert str(res) == "S(S(S(0)))"

    # Structural equality for terms.
    assert App("f", x) == App("f", x)

    # Substitution.
    assert str(apply_subst(add(x, y), {x: zero})) == "add(0, y)"

    # Pattern matching.
    m = match(add(x, y), add(zero, S(zero)))
    assert m is not None
    assert m[x] == zero

    # AC normalization.
    assert str(normalize(add(y, add(x, z)))) == "add(x, add(y, z))"

    # Low-level rewrite tracing.
    tr = Trace()
    configure_prover(rules=rules, trace=tr, config=config, schemes=schemes)
    normalize(add(S(zero), zero))
    assert len(tr.steps) > 0
    configure_prover(rules=rules, config=config, schemes=schemes)

    # Clause simplification under assumptions.
    clause = Clause(((x, zero),), add(x, S(zero)))
    simplified = simplify_clause(clause)
    assert str(simplified.goal) == "S(0)"

    # Solved equality goals.
    clause2 = Clause((), eq(zero, zero))
    print(simplify_clause(clause2))
    assert clause_solved(simplify_clause(clause2))

    # Stable normalization of a ground term.
    assert normalize(add(zero, zero)) == zero

    # Repeated normalization yields the same result.
    r1n = normalize(add(zero, zero))
    r2n = normalize(add(zero, zero))
    assert r1n == r2n

    # Conditional rewrite rules.
    assert str(normalize(f(zero))) == "1"
    assert str(normalize(f(S(zero)))) == "f(S(0))"

    # Built-in equality and disequality simplification.
    assert normalize(eq(zero, zero)) == true
    assert normalize(neq(zero, zero)) == false

    # Equality closure propagates through assumptions.
    clause3 = Clause(((x, y), (y, zero)), eq(x, zero))
    assert clause_solved(simplify_clause(clause3))

    # Natural-number induction produces base and step branches.
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

    # Addition right-identity by explicit natural-number induction.
    assert prove_with_induction(clause4, x, nat_scheme, depth=8, induction_depth=1)

    # False ground goals remain unproved.
    bad = Clause((), eq(add(zero, one), zero))
    assert not prove(bad, depth=8)

    # Sort mismatches block induction.
    assert not prove_with_induction(clause4, xs, nat_scheme, depth=8, induction_depth=1)
    assert not induction_branches(clause4, xs, nat_scheme)

    # Registered schemes can be looked up by name or sort.
    register_induction_scheme(nat_scheme)
    register_induction_scheme(list_scheme)
    assert get_induction_scheme("nat") is nat_scheme
    assert get_induction_scheme_for_sort("List") is list_scheme
    assert prove_with_registered_induction(
        clause4, x_nat, "nat", depth=8, induction_depth=1
    )
    assert not prove_with_registered_induction(
        clause4, x_nat, "list", depth=8, induction_depth=1
    )

    # List induction branch shape.
    list_goal = Clause((), eq(app(xs, nil), xs))
    list_branches = induction_branches(list_goal, xs, list_scheme)
    assert len(list_branches) == 2
    assert str(list_branches[0].goal) == "eq(append(nil, nil), nil)"
    assert (
        str(list_branches[1].goal)
        == "eq(append(cons(xs_cons_arg_0, xs_ih_0), nil), cons(xs_cons_arg_0, xs_ih_0))"
    )
    assert len(list_branches[1].assumptions) == 1
    ih_l2, ih_r2 = list_branches[1].assumptions[0]
    assert str(ih_l2) == "append(xs_ih_0, nil)"
    assert str(ih_r2) == "xs_ih_0"

    # Append right-identity by explicit list induction.
    assert prove_with_induction(list_goal, xs, list_scheme, depth=10, induction_depth=1)

    # Append associativity by list induction.
    ys = V("ys", "List")
    zs = V("zs", "List")
    assoc_goal = Clause((), eq(app(app(xs, ys), zs), app(xs, app(ys, zs))))
    assert prove_with_induction(
        assoc_goal, xs, list_scheme, depth=12, induction_depth=1
    )

    # Length is preserved by appending `nil`.
    len_append_nil_goal = Clause((), eq(length(app(xs, nil)), length(xs)))
    assert prove_with_induction(
        len_append_nil_goal, xs, list_scheme, depth=12, induction_depth=1
    )

    # Length distributes over append.
    len_append_goal = Clause((), eq(length(app(xs, ys)), add(length(xs), length(ys))))
    assert prove_with_induction(
        len_append_goal, xs, list_scheme, depth=14, induction_depth=1
    )

    # Configuration controls AC normalization behavior.
    no_ac_config = EngineConfig(precedence=config.precedence, assoc=set(), comm=set())
    configure_prover(rules=rules, config=no_ac_config, schemes=schemes)
    assert str(normalize(add(y, add(x, z)))) == "add(y, add(x, z))"
    configure_prover(rules=rules, config=config, schemes=schemes)
    assert str(normalize(add(y, add(x, z)))) == "add(x, add(y, z))"

    # Variables compare structurally by name and sort.
    vx1 = V("vx")
    vx2 = V("vx")
    assert vx1 == vx2
    assert vx1 is not vx2
    vn1 = V("vn", "Nat")
    vn2 = V("vn", "Nat")
    assert vn1 == vn2
    assert vn1 is not vn2

    # Redeclaring a variable name with a different sort raises an error.
    reset_var_declarations()
    _ = V("u")
    try:
        V("u", "Nat")
        assert False
    except ValueError:
        pass
    reset_var_declarations()
    _ = V("u", "Nat")
    try:
        V("u", "List")
        assert False
    except ValueError:
        pass

    # Re-establish variables for the proof-trace example.
    reset_var_declarations()
    x = V("x")
    y = V("y")
    z = V("z")
    xs = V("xs", "List")
    ys = V("ys", "List")
    zs = V("zs", "List")
    assoc_goal = Clause((), eq(app(app(xs, ys), zs), app(xs, app(ys, zs))))

    # Proof traces record induction structure in a readable form.
    ok_trace, ptrace = prove_with_trace(
        assoc_goal, depth=12, var=xs, scheme=list_scheme, induction_depth=1
    )
    assert ok_trace
    rendered = render_proof_trace(ptrace)
    assert "induction" in rendered
    assert "scheme=list" in rendered
    assert "induction-branch" in rendered

    print("\nAppend associativity proof trace:")
    print(rendered)
    print("All tests passed.")
