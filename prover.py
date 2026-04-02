from __future__ import annotations

"""
A compact, Pythonic core for a Boyer–Moore / ACL2-style rewriting engine.

Fixes included:
- Proper hash-consing without dataclass field interference
- Added tests
"""

# -----------------------------------------------------------------------------
# Imports
# -----------------------------------------------------------------------------

from dataclasses import dataclass
from typing import Tuple, Dict, Optional
from weakref import WeakValueDictionary


# -----------------------------------------------------------------------------
# Term definitions (hash-consed DAG)
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


# Properly attach cache AFTER class definition (not a dataclass field)
Fun._cache = WeakValueDictionary()


# -----------------------------------------------------------------------------
# Substitutions
# -----------------------------------------------------------------------------

Subst = Dict[Var, Term]


def extend(subst: Subst, v: Var, t: Term) -> Subst:
    new = subst.copy()
    new[v] = t
    return new


def apply_subst(term: Term, subst: Subst) -> Term:
    match term:
        case Var() as v:
            return subst.get(v, v)
        case Fun(symbol, args):
            return Fun(symbol, tuple(apply_subst(a, subst) for a in args))


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
                return subst if subst[v] is t else None
            return extend(subst, v, t)

        case Fun(f1, args1), Fun(f2, args2):
            if f1 != f2 or len(args1) != len(args2):
                return None

            for a1, a2 in zip(args1, args2):
                subst = match(a1, a2, subst)
                if subst is None:
                    return None
            return subst

        case _:
            return None


# -----------------------------------------------------------------------------
# Ordering (Minimal LPO)
# -----------------------------------------------------------------------------

# Precedence: higher = greater
PRECEDENCE = {
    "add": 2,
    "S": 1,
    "0": 0,
}


def prec(f: str) -> int:
    return PRECEDENCE.get(f, 0)


def lpo_greater(s: Term, t: Term) -> bool:
    """
    Very small Lexicographic Path Ordering (LPO) approximation.

    s > t if:
    1. s is a Fun and some argument >= t
    2. root(s) > root(t) and s > all args of t
    3. same root and lexicographic argument comparison
    """

    if s is t:
        return False

    match s, t:
        # Variables are minimal
        case _, Var():
            return True
        case Var(), Fun():
            return False

        case Fun(f, s_args), Fun(g, t_args):
            # (1) subterm property
            if any(lpo_geq(si, t) for si in s_args):
                return True

            # (2) precedence
            if prec(f) > prec(g) and all(lpo_greater(s, ti) for ti in t_args):
                return True

            # (3) same symbol → lexicographic
            if f == g:
                for si, ti in zip(s_args, t_args):
                    if si is ti:
                        continue
                    if lpo_greater(si, ti):
                        return True
                    if lpo_greater(ti, si):
                        return False
                return len(s_args) > len(t_args)

    return False


def lpo_geq(s: Term, t: Term) -> bool:
    return s is t or lpo_greater(s, t)


def decreases(old: Term, new: Term) -> bool:
    return lpo_greater(old, new)


# -----------------------------------------------------------------------------
# Rules
# -----------------------------------------------------------------------------
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class Rule:
    lhs: Term
    rhs: Term
    conditions: Tuple[Tuple[Term, Term], ...] = ()


# -----------------------------------------------------------------------------
# Context
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class Context:
    equalities: Tuple[Tuple[Term, Term], ...] = ()

    def extend(self, eq):
        return Context(self.equalities + (eq,))


def orient(lhs: Term, rhs: Term):
    if decreases(lhs, rhs):
        return (rhs, lhs)
    if decreases(rhs, lhs):
        return (lhs, rhs)
    return None


def context_rules(ctx: Context):
    for lhs, rhs in ctx.equalities:
        o = orient(lhs, rhs)
        if o:
            yield Rule(*o)


# -----------------------------------------------------------------------------
# Discrimination tree
# -----------------------------------------------------------------------------

class DTNode:
    def __init__(self):
        self.children = {}
        self.rules = []


class DiscriminationTree:
    """
    Simpler and correct indexing by root symbol.
    (The previous discrimination tree was too strict and failed to retrieve rules.)
    """

    def __init__(self):
        self.by_symbol = {}

    def insert(self, term: Term, rule: Rule):
        match term:
            case Fun(symbol, _):
                self.by_symbol.setdefault(symbol, []).append(rule)
            case Var():
                self.by_symbol.setdefault(None, []).append(rule)

    def retrieve(self, term: Term):
        match term:
            case Fun(symbol, _):
                return self.by_symbol.get(symbol, []) + self.by_symbol.get(None, [])
            case Var():
                return self.by_symbol.get(None, [])


# -----------------------------------------------------------------------------
# Rewriting
# -----------------------------------------------------------------------------


def rewrite_once(term, rule, ctx, index, cache):
    subst = match(rule.lhs, term)
    if subst is None:
        return None

    new_term = apply_subst(rule.rhs, subst)

    if not decreases(term, new_term):
        return None

    return new_term


def rewrite(term: Term, index: DiscriminationTree, ctx: Context, cache) -> Term:
    match term:
        case Fun(symbol, args):
            args = tuple(normalize(a, index, ctx, cache) for a in args)
            term = Fun(symbol, args)

    for rule in index.retrieve(term):
        t2 = rewrite_once(term, rule, ctx, index, cache)
        if t2 is not None:
            return t2

    for rule in context_rules(ctx):
        t2 = rewrite_once(term, rule, ctx, index, cache)
        if t2 is not None:
            return t2

    return term


# -----------------------------------------------------------------------------
# Normalization
# -----------------------------------------------------------------------------

GLOBAL_GROUND_CACHE: Dict[Term, Term] = {}


def is_ground(t: Term) -> bool:
    match t:
        case Var():
            return False
        case Fun(_, args):
            return all(is_ground(a) for a in args)


def normalize(term: Term, index, ctx: Context, cache=None, fuel=1000):
    if cache is None:
        cache = {}

    def norm(t, fuel_left):
        if t in cache:
            return cache[t]

        if is_ground(t) and t in GLOBAL_GROUND_CACHE:
            return GLOBAL_GROUND_CACHE[t]

        if fuel_left <= 0:
            return t

        t2 = rewrite(t, index, ctx, cache)

        if t2 is t:
            cache[t] = t
            if is_ground(t):
                GLOBAL_GROUND_CACHE[t] = t
            return t

        result = norm(t2, fuel_left - 1)
        cache[t] = result

        if is_ground(t):
            GLOBAL_GROUND_CACHE[t] = result

        return result

    return norm(term, fuel)


# -----------------------------------------------------------------------------
# DSL helpers
# -----------------------------------------------------------------------------


def Const(name: str):
    return Fun(name, ())


def App(f: str, *args):
    return Fun(f, args)


# -----------------------------------------------------------------------------
# Tests
# -----------------------------------------------------------------------------

if __name__ == "__main__":
    x = Var("x")
    y = Var("y")

    zero = Const("0")
    S = lambda t: App("S", t)
    add = lambda a, b: App("add", a, b)

    r1 = Rule(add(zero, y), y)
    r2 = Rule(add(S(x), y), S(add(x, y)))

    dt = DiscriminationTree()
    dt.insert(r1.lhs, r1)
    dt.insert(r2.lhs, r2)

    # Test 1: normalization
    term = add(S(S(zero)), S(zero))
    result = normalize(term, dt, Context())
    print("Result:", result)
    assert str(result) == "S(S(S(0)))"

    # Test 2: hash-consing
    t1 = App("f", x)
    t2 = App("f", x)
    assert t1 is t2

    # Test 3: substitution
    subst = {x: zero}
    assert str(apply_subst(add(x, y), subst)) == "add(0, y)"

    # Test 4: matching
    subst2 = match(add(x, y), add(zero, S(zero)))
    assert subst2 is not None
    assert str(subst2[x]) == "0"

    print("All tests passed.")

