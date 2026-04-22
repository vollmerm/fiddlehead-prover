"""Automatic induction variable selection heuristics.

This module provides preliminary support for automatically choosing induction
variables, letting users opt-in to auto-induction when they want the system to
pick the best variable.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Set

from .kernel import Engine, InductionScheme, get_induction_scheme_for_sort
from .syntax import Fun, Term, Var, contains_var

if TYPE_CHECKING:
    from .proof import Clause


def choose_induction_var(clause: Clause, engine: Engine) -> Var:
    """Choose the best induction variable for a clause.

    Args:
        clause: The clause to analyze.
        engine: The proving engine (for scheme lookup).

    Returns:
        The best variable to use for induction.

    Raises:
        ValueError: If no suitable induction variable can be found.
    """
    candidates = _collect_candidates(clause, engine)
    if not candidates:
        raise ValueError(
            "No suitable induction variable found. Ensure your goal contains "
            "variables of a sort with a registered induction scheme (Nat, List, Map, Tree)."
        )

    scored = [(var, _score_variable(var, clause, engine)) for var in candidates]
    scored.sort(key=lambda x: x[1], reverse=True)
    return scored[0][0]


def _collect_candidates(clause: Clause, engine: Engine) -> list[Var]:
    """Collect all variables that could be induction candidates.

    A variable is a candidate if:
    1. Its sort has a registered induction scheme in the engine
    2. It appears in the clause
    """
    candidates: list[Var] = []
    seen: Set[str] = set()

    for var in _vars_in_clause(clause):
        if var.name in seen:
            continue
        if var.sort is None:
            continue
        if get_induction_scheme_for_sort(engine, var.sort) is None:
            continue
        seen.add(var.name)
        candidates.append(var)

    return candidates


def _vars_in_clause(clause: Clause) -> list[Var]:
    """Collect all variables appearing in a clause."""
    result: list[Var] = []
    _collect_vars(clause.goal, result)
    for lhs, rhs in clause.assumptions:
        _collect_vars(lhs, result)
        _collect_vars(rhs, result)
    for lhs, rhs in clause.disequalities:
        _collect_vars(lhs, result)
        _collect_vars(rhs, result)
    return result


def _collect_vars(term: Term, result: list[Var]) -> None:
    """Collect variables from a term into result."""
    match term:
        case Var() as v:
            result.append(v)
        case Fun(_, args):
            for arg in args:
                _collect_vars(arg, result)


def _score_variable(var: Var, clause: Clause, engine: Engine) -> int:
    """Score a variable based on induction heuristics. Higher = better."""
    score = 0

    if _appears_in_conclusion(var, clause):
        score += 10

    if _is_at_recursive_position(var, clause, engine):
        score += 8

    if _appears_in_measure_function(var, clause):
        score += 5

    if _var_is_not_in_assumptions_only(var, clause):
        score += 3

    return score


def _appears_in_conclusion(var: Var, clause: Clause) -> bool:
    """Check if variable appears in the top-level conclusion (goal)."""
    return contains_var(clause.goal, var)


_MEASURE_SYMBOLS: Set[str] = {"length", "size", "add", "depth", "count"}


def _appears_in_measure_function(var: Var, clause: Clause) -> bool:
    """Check if variable appears inside a measure function like length, size, etc."""
    calls: list[Fun] = []
    _collect_measure_calls(clause.goal, calls)
    for lhs, rhs in clause.assumptions:
        _collect_measure_calls(lhs, calls)
        _collect_measure_calls(rhs, calls)
    for lhs, rhs in clause.disequalities:
        _collect_measure_calls(lhs, calls)
        _collect_measure_calls(rhs, calls)

    for call in calls:
        for arg in call.args:
            if contains_var(arg, var):
                return True
    return False


def _collect_measure_calls(term: Term, result: list[Fun]) -> None:
    """Collect measure function applications from a term."""
    match term:
        case Var():
            return
        case Fun(symbol, args) as f:
            if symbol in _MEASURE_SYMBOLS:
                result.append(f)
            for arg in args:
                _collect_measure_calls(arg, result)


def _is_at_recursive_position(var: Var, clause: Clause, engine: Engine) -> bool:
    """Check if variable appears at a recursive destructor position in the goal.

    A variable scores higher when it appears as the principal argument to
    a recursive function in the goal, as registered via scheme constructors.
    """
    goal = clause.goal
    match goal:
        case Fun(symbol, args):
            for scheme in engine.schemes.values():
                for constructor in scheme.constructors:
                    if constructor.symbol == symbol:
                        for pos in constructor.recursive_positions:
                            if pos < len(args) and contains_var(args[pos], var):
                                return True
    return False


def _var_is_not_in_assumptions_only(var: Var, clause: Clause) -> bool:
    """Check if variable appears somewhere other than just assumptions."""
    if contains_var(clause.goal, var):
        return True
    for lhs, rhs in clause.disequalities:
        if contains_var(lhs, var) or contains_var(rhs, var):
            return True
    return False
