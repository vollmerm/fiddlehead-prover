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
"""

from dataclasses import dataclass
from typing import Tuple, Dict, Optional
from weakref import WeakValueDictionary

# -----------------------------------------------------------------------------
# Terms (hash-consed)
# -----------------------------------------------------------------------------

class Term:
    pass


@dataclass(frozen=True, slots=True)
class Var(Term):
    name: str

    def __str__(self):
        return self.name


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

PRECEDENCE = {
    "add": 3,
    "S": 2,
    "if": 1,
    "eq": 1,
    "neq": 1,
    "0": 0,
    "1": 0,
    "true": 0,
    "false": 0,
}


def prec(f: str):
    return PRECEDENCE.get(f, 0)


def lpo_greater(s: Term, t: Term) -> bool:
    if s is t:
        return False

    match s, t:
        case _, Var():
            return True
        case Var(), Fun():
            return False
        case Fun(f, s_args), Fun(g, t_args):
            if any(lpo_greater(si, t) or si is t for si in s_args):
                return True
            if prec(f) > prec(g) and all(lpo_greater(s, ti) for ti in t_args):
                return True
            if f == g:
                for si, ti in zip(s_args, t_args):
                    if si is ti:
                        continue
                    if lpo_greater(si, ti):
                        return True
                    if lpo_greater(ti, si):
                        return False
    return False


def decreases(a, b):
    return lpo_greater(a, b)


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
    x=Var("x"); y=Var("y")
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
        elif self.rank[ra] == self.rank[rb] and term_key(rb) < term_key(ra):
            ra, rb = rb, ra

        self.parent[rb] = ra
        if self.rank[ra] == self.rank[rb]:
            self.rank[ra] += 1
        if term_key(self.rep[rb]) < term_key(self.rep[ra]):
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


def build_eq_classes(ctx: Context, extra_terms: Tuple[Term, ...] = ()) -> EqClasses:
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


def context_rules(ctx: Context):
    for lhs, rhs in ctx.equalities:
        if isinstance(lhs, Var):
            continue
        if decreases(lhs, rhs):
            yield Rule(lhs, rhs)
        elif decreases(rhs, lhs):
            yield Rule(rhs, lhs)


# -----------------------------------------------------------------------------
# Conditions
# -----------------------------------------------------------------------------

def holds(l, r, rules, ctx, eq_classes: Optional[EqClasses] = None):
    l2 = normalize(l, rules, ctx)
    r2 = normalize(r, rules, ctx)
    eq = eq_classes if eq_classes is not None else build_eq_classes(ctx, (l2, r2))

    for a, b in ctx.disequalities:
        if eq.are_equal(l2, a) and eq.are_equal(r2, b):
            return False
        if eq.are_equal(l2, b) and eq.are_equal(r2, a):
            return False

    if eq.are_equal(l2, r2):
        return True

    return False


def conditions_hold(conditions, subst, rules, ctx, eq_classes: Optional[EqClasses] = None):
    for l, r in conditions:
        l2 = apply_subst(l, subst)
        r2 = apply_subst(r, subst)
        if not holds(l2, r2, rules, ctx, eq_classes):
            return False
    return True


# -----------------------------------------------------------------------------
# AC normalization
# -----------------------------------------------------------------------------

ASSOC = {"add"}
COMM = {"add"}


def term_key(t: Term):
    match t:
        case Fun(f, args):
            return (0, f, len(args), tuple(term_key(a) for a in args))
        case Var(n):
            return (1, n)


def ac_normalize(t: Term) -> Term:
    match t:
        case Fun(f, (a, b)) if f in ASSOC:
            flat = []

            def collect(x):
                match x:
                    case Fun(f2, (l, r)) if f2 == f:
                        collect(l)
                        collect(r)
                    case _:
                        flat.append(x)

            collect(t)

            if f in COMM:
                flat.sort(key=term_key)

            res = flat[-1]
            for x in reversed(flat[:-1]):
                res = Fun(f, (x, res))
            return res

    return t


# -----------------------------------------------------------------------------
# Ground caching + memo
# -----------------------------------------------------------------------------

GROUND_CACHE: Dict[Term, Term] = {}


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

        
# -----------------------------------------------------------------------------
# Rewriting
# -----------------------------------------------------------------------------


def rewrite_once(term, rule, rules, ctx, trace=None, eq_classes: Optional[EqClasses] = None):
    subst = match(rule.lhs, term)
    if subst is None:
        return None

    if rule.conditions and not conditions_hold(rule.conditions, subst, rules, ctx, eq_classes):
        return None

    new = apply_subst(rule.rhs, subst)

    # FIX: allow conditional rules even if not decreasing
    if not rule.conditions:
        if not decreases(term, new):
            return None

    if trace:
        trace.add(term, new, rule)

    return new


def rewrite(term, index: RuleIndex, rules, ctx: Context, trace=None, memo=None, eq_classes: Optional[EqClasses] = None):
    if memo is not None and term in memo:
        return memo[term]

    if eq_classes is not None:
        term = eq_classes.canonical(term)

    match term:
        case Fun(f, args):
            args = tuple(rewrite(a, index, rules, ctx, trace, memo, eq_classes) for a in args)
            term = Fun(f, args)

    term = ac_normalize(term)
    if eq_classes is not None:
        term = eq_classes.canonical(term)

    for r in index.get(term):
        t2 = rewrite_once(term, r, rules, ctx, trace, eq_classes)
        if t2 is not None:
            if memo is not None:
                memo[term] = t2
            return t2

    for r in context_rules(ctx):
        t2 = rewrite_once(term, r, rules, ctx, trace, eq_classes)
        if t2 is not None:
            if memo is not None:
                memo[term] = t2
            return t2

    if memo is not None:
        memo[term] = term

    return term


# -----------------------------------------------------------------------------
# Normalize
# -----------------------------------------------------------------------------


def normalize(term, rules, ctx: Context = Context(), trace=None, fuel=1000):
    index = RuleIndex(rules)
    memo: Dict[Term, Term] = {}
    original = term
    eq_classes = build_eq_classes(ctx, (term,))

    for _ in range(fuel):
        if is_ground(term) and term in GROUND_CACHE:
            return GROUND_CACHE[term]

        t2 = rewrite(term, index, rules, ctx, trace, memo, eq_classes)

        if t2 is term:
            break

        term = t2

    if is_ground(original):
        GROUND_CACHE[original] = term
    if is_ground(term):
        GROUND_CACHE[term] = term

    return term


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
    base_terms: Tuple[Term, ...]
    constructors: Tuple[InductionConstructor, ...]


def nat_induction_scheme(zero: Optional[Term] = None, succ_symbol: str = "S") -> InductionScheme:
    if zero is None:
        zero = Const("0")
    return InductionScheme(
        name="nat",
        base_terms=(zero,),
        constructors=(InductionConstructor(succ_symbol, 1, (0,)),),
    )


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


def fresh_var(base: str, used_names: set[str]) -> Var:
    i = 0
    while True:
        name = f"{base}_{i}"
        if name not in used_names:
            used_names.add(name)
            return Var(name)
        i += 1


def induction_branches(clause: Clause, var: Var, scheme: InductionScheme) -> list[Clause]:
    used = vars_in_clause(clause).copy()
    branches: list[Clause] = []

    for b in scheme.base_terms:
        branches.append(instantiate_clause(clause, {var: b}))

    for cons in scheme.constructors:
        rec_vars = [fresh_var(f"{var.name}_ih", used) for _ in cons.recursive_positions]
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


def simplify_clause(clause: Clause, rules):
    ctx = Context(clause.assumptions)
    new_goal = normalize(clause.goal, rules, ctx)
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


def prove(clause: Clause, rules, depth: int = 5) -> bool:
    if depth <= 0:
        return False

    simplified = simplify_clause(clause, rules)
    if clause_solved(simplified):
        return True

    branches = split_clause(simplified)
    if len(branches) == 1:
        return False

    next_depth = depth - 1
    return all(prove(branch, rules, next_depth) for branch in branches)


def prove_with_induction(
    clause: Clause,
    rules,
    var: Var,
    scheme: InductionScheme,
    depth: int = 5,
    induction_depth: int = 1,
) -> bool:
    if prove(clause, rules, depth):
        return True
    if induction_depth <= 0:
        return False

    branches = induction_branches(clause, var, scheme)
    if not branches:
        return False

    next_induction = induction_depth - 1
    return all(
        prove_with_induction(branch, rules, var, scheme, depth, next_induction)
        for branch in branches
    )


# -----------------------------------------------------------------------------
# Tests
# -----------------------------------------------------------------------------

if __name__ == "__main__":
    x = Var("x")
    y = Var("y")
    z = Var("z")

    zero = Const("0")
    one = Const("1")
    
    S = lambda t: App("S", t)
    add = lambda a, b: App("add", a, b)
    eq = lambda a, b: App("eq", a, b)
    neq = lambda a,b:App("neq",a,b)
    f = lambda a: App("f", a)
    ite = lambda c,t,e:App("if",c,t,e)

    r1 = Rule(add(zero, y), y)
    r2 = Rule(add(S(x), y), S(add(x, y)))
    r3 = Rule(f(x), one, conditions=((x, zero),))

    rules = builtin_rules() + [r1, r2, r3]

    # Test 1
    t = add(S(S(zero)), S(zero))
    res = normalize(t, rules)
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
    assert str(normalize(add(y, add(x, z)), rules)) == "add(x, add(y, z))"

    # Test 6
    tr = Trace()
    normalize(add(S(zero), zero), rules, trace=tr)
    assert len(tr.steps) > 0

    # Test 7
    clause = Clause(((x, zero),), add(x, S(zero)))
    simplified = simplify_clause(clause, rules)
    assert str(simplified.goal) == "S(0)"

    # Test 8
    clause2 = Clause((), eq(zero, zero))
    print(simplify_clause(clause2, rules))
    assert clause_solved(simplify_clause(clause2, rules))

    # Test 9
    t = add(zero, zero)
    r = normalize(t, rules)
    assert t in GROUND_CACHE
    assert GROUND_CACHE[t] is r

    # Test 10
    t = add(zero, zero)
    r1n = normalize(t, rules)
    r2n = normalize(t, rules)
    assert r1n is r2n

    # Test 11
    assert str(normalize(f(zero), rules)) == "1"
    assert str(normalize(f(S(zero)), rules)) == "f(S(0))"

    # Test 12
    assert normalize(eq(zero,zero),rules) == true
    assert normalize(neq(zero,zero),rules) == false

    # Test 13: equality closure x = y, y = 0 => x = 0
    clause3 = Clause(((x, y), (y, zero)), eq(x, zero))
    assert clause_solved(simplify_clause(clause3, rules))

    # Test 14: induction obligations for nat produce base + step (with IH)
    nat_scheme = nat_induction_scheme(zero)
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
    assert prove_with_induction(clause4, rules, x, nat_scheme, depth=8, induction_depth=1)

    # Test 16: a clearly false ground goal is not proven
    bad = Clause((), eq(add(zero, one), zero))
    assert not prove(bad, rules, depth=8)

    print("All tests passed.")
