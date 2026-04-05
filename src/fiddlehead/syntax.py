from __future__ import annotations

"""Core term and substitution syntax used throughout the prover.

The syntax layer defines hash-consed first-order terms and a lightweight type
term language. It also provides constructors and matching/substitution helpers
used by rewriting, clause simplification, and proof search.
"""

from dataclasses import dataclass
from typing import Dict, Optional, Tuple
from weakref import WeakValueDictionary


class Term:
    """Marker base class for prover terms."""

    pass


class TypeTerm:
    """Marker base class for sort/type terms."""

    pass


@dataclass(frozen=True, slots=True)
class TypeVar(TypeTerm):
    """A type variable used by sort signatures and inference."""

    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True, slots=True)
class TypeConst(TypeTerm):
    """A concrete type constructor, optionally parameterized."""

    name: str
    args: Tuple[TypeTerm, ...] = ()

    def __str__(self) -> str:
        if not self.args:
            return self.name
        return f"{self.name}[{', '.join(map(str, self.args))}]"


def _to_type_term(v: object) -> TypeTerm:
    if isinstance(v, TypeTerm):
        return v
    if isinstance(v, str):
        return TypeConst(v)
    raise ValueError(f"Unsupported type term: {v!r}")


@dataclass(frozen=True, slots=True)
class Var(Term):
    """A first-order variable, optionally annotated with a sort name."""

    name: str
    sort: Optional[str] = None

    def __str__(self) -> str:
        return self.name


_VAR_INTERN: Dict[Tuple[str, Optional[str]], Var] = {}
_VAR_NAME_SORT: Dict[str, Optional[str]] = {}


def reset_var_interner() -> None:
    """Reset global variable interning state.

    Useful in tests to ensure deterministic reuse and sort checks.
    """

    _VAR_INTERN.clear()
    _VAR_NAME_SORT.clear()


def V(name: str, sort: Optional[str] = None) -> Var:
    """Create (or reuse) an interned variable.

    Variables with the same name must use the same sort annotation across a
    run; conflicting declarations raise ``ValueError``.
    """

    existing_sort = _VAR_NAME_SORT.get(name)
    if existing_sort is None and name in _VAR_NAME_SORT:
        if sort is not None:
            raise ValueError(
                f"Variable '{name}' already declared with sort None; "
                f"cannot redeclare with sort '{sort}'."
            )
    elif existing_sort is not None and existing_sort != sort:
        raise ValueError(
            f"Variable '{name}' already declared with sort '{existing_sort}'; "
            f"cannot redeclare with sort '{sort}'."
        )

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
    """A hash-consed function symbol application."""

    symbol: str
    args: Tuple[Term, ...]

    def __new__(cls, symbol: str, args: Tuple[Term, ...]) -> Fun:
        key = (symbol, args)
        existing = cls._cache.get(key)
        if existing is not None:
            return existing

        self = object.__new__(cls)
        object.__setattr__(self, "symbol", symbol)
        object.__setattr__(self, "args", args)
        cls._cache[key] = self
        return self

    def __str__(self) -> str:
        if not self.args:
            return self.symbol
        return f"{self.symbol}({', '.join(map(str, self.args))})"


Fun._cache = WeakValueDictionary()


def Const(name: str) -> Fun:
    """Build a nullary function (constant) term."""

    return Fun(name, ())


def App(symbol: str, *args: Term) -> Fun:
    """Build a function application term."""

    return Fun(symbol, args)


true = Const("true")
false = Const("false")

Subst = Dict[Var, Term]


def apply_subst(term: Term, subst: Subst) -> Term:
    """Apply a substitution to a term."""

    match term:
        case Var() as v:
            return subst.get(v, v)
        case Fun(symbol, args):
            return Fun(symbol, tuple(apply_subst(arg, subst) for arg in args))


def match(pattern: Term, target: Term, subst: Optional[Subst] = None) -> Optional[Subst]:
    """First-order pattern matching from ``pattern`` onto ``target``.

    Returns a substitution on success, or ``None`` when matching fails.
    """

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
            for left, right in zip(a1, a2):
                subst = match(left, right, subst)
                if subst is None:
                    return None
            return subst

    return None
