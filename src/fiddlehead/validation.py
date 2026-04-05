from __future__ import annotations

"""Sort signatures, type inference, and well-typedness validation.

This module enforces inference-first typing for terms, rewrite rules, and
clauses. It is shared by kernel/proof/theory code to reject ill-typed inputs
early and consistently.
"""

from dataclasses import dataclass
from typing import Dict, Protocol, Tuple

from .syntax import Fun, Term, TypeConst, TypeTerm, TypeVar, Var, _to_type_term


@dataclass(frozen=True)
class SortSignature:
    """Type signature for a symbol: argument sorts and result sort."""

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
    """Return built-in sort signatures for core symbols."""

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


class EngineLike(Protocol):
    sort_signatures: Dict[str, SortSignature]
    sort_arities: Dict[str, int]


class RuleLike(Protocol):
    @property
    def lhs(self) -> Term: ...

    @property
    def rhs(self) -> Term: ...

    @property
    def conditions(self) -> Tuple[Tuple[Term, Term], ...]: ...


class ClauseLike(Protocol):
    @property
    def assumptions(self) -> Tuple[Tuple[Term, Term], ...]: ...

    @property
    def goal(self) -> Term: ...


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
    raise TypeError(f"Unsupported type term: {type(term)!r}")


def _occurs_in_type(type_var: TypeVar, term: TypeTerm, subst: Dict[TypeVar, TypeTerm]) -> bool:
    term = _apply_type_subst(term, subst)
    match term:
        case TypeVar() as other:
            return other == type_var
        case TypeConst(_, args):
            return any(_occurs_in_type(type_var, arg, subst) for arg in args)
    raise TypeError(f"Unsupported type term: {type(term)!r}")


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


def _type_from_sort_annotation(sort: str, engine: EngineLike, counter: list[int]) -> TypeTerm:
    arity = engine.sort_arities.get(sort)
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
        raise TypeError(f"Unsupported type term: {type(term)!r}")

    return tuple(freshen(arg) for arg in signature.arg_sorts), freshen(signature.result_sort)


def _infer_type_inner(
    term: Term,
    engine: EngineLike,
    var_env: Dict[Var, TypeTerm],
    subst: Dict[TypeVar, TypeTerm],
    counter: list[int],
) -> TypeTerm:
    match term:
        case Var(_, sort) as var:
            existing = var_env.get(var)
            if existing is not None:
                return _apply_type_subst(existing, subst)
            inferred = (
                _type_from_sort_annotation(sort, engine, counter)
                if sort is not None
                else _fresh_type_var("v", counter)
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
    raise TypeError(f"Unsupported term type: {type(term)!r}")


def infer_type(term: Term, engine: EngineLike) -> TypeTerm:
    """Infer a principal type term for ``term`` under engine signatures."""

    subst: Dict[TypeVar, TypeTerm] = {}
    inferred = _infer_type_inner(term, engine, {}, subst, [0])
    return _apply_type_subst(inferred, subst)


def _contains_type_vars(term: TypeTerm) -> bool:
    match term:
        case TypeVar():
            return True
        case TypeConst(_, args):
            return any(_contains_type_vars(arg) for arg in args)
    raise TypeError(f"Unsupported type term: {type(term)!r}")


def infer_sort(term: Term, engine: EngineLike) -> str:
    """Infer a concrete sort name for ``term``.

    Raises when inference remains polymorphic/ambiguous.
    """

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
    engine: EngineLike,
    where: str,
) -> tuple[TypeTerm, TypeTerm, Dict[TypeVar, TypeTerm]]:
    subst: Dict[TypeVar, TypeTerm] = {}
    counter = [0]
    env: Dict[Var, TypeTerm] = {}
    left_type = _infer_type_inner(lhs, engine, env, subst, counter)
    right_type = _infer_type_inner(rhs, engine, env, subst, counter)
    _unify_types(left_type, right_type, subst, where)
    return _apply_type_subst(left_type, subst), _apply_type_subst(right_type, subst), subst


def _validate_equality_pair(lhs: Term, rhs: Term, engine: EngineLike, where: str) -> None:
    _infer_pair_with_shared_env(lhs, rhs, engine, where)


def _validate_rule_sorts(rule: RuleLike, engine: EngineLike, where: str) -> None:
    _validate_equality_pair(rule.lhs, rule.rhs, engine, where)
    for index, (left, right) in enumerate(rule.conditions):
        _validate_equality_pair(left, right, engine, f"{where} condition[{index}]")


def _validate_clause_sorts(clause: ClauseLike, engine: EngineLike, where: str) -> None:
    infer_type(clause.goal, engine)
    for index, (left, right) in enumerate(clause.assumptions):
        _validate_equality_pair(left, right, engine, f"{where} assumption[{index}]")
