"""Pre-induction generalization: replace rigid terms with fresh variables.

ACL2-style generalization that runs before induction to make goals more
amenable to proof. When the prover is stuck and about to apply induction,
we generalize "rigid" terms (ground terms, repeated subterms) into fresh
variables to strengthen induction hypotheses.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Dict, Optional, Set, Tuple

from .kernel import Engine, InductionScheme, is_ground
from .syntax import Fun, Term, V, Var, _VAR_NAME_SORT, apply_subst, contains_var

if TYPE_CHECKING:
    from .proof import Clause


@dataclass(frozen=True)
class GeneralizationMap:
    """Tracks term -> variable substitutions made during generalization.

    term_to_var: Maps original rigid term to the fresh variable representing it.
    var_to_term: Maps fresh variable back to original term (for recovery).
    """

    term_to_var: Tuple[Tuple[Term, Var], ...]
    var_to_term: Tuple[Tuple[Var, Term], ...]


def generalize_clause(
    clause: Clause, engine: Engine, induction_var: Optional[Var] = None
) -> Optional[Tuple[Clause, GeneralizationMap]]:
    """Generalize a clause by replacing rigid terms with fresh variables.

    Returns None if no generalization is needed (clause is not "rigid" enough
    to benefit from generalization).

    Generalization heuristics:
    - Ground (variable-free) terms are replaced with fresh variables
    - Repeated subterms are replaced with a single variable
    - The induction variable and its context are NOT generalized

    Args:
        clause: The clause to generalize.
        engine: The proving engine (for sort inference and freshness).
        induction_var: Optional variable that will be used for induction;
                      this variable and terms containing it are not generalized.

    Returns:
        A tuple of (generalized_clause, generalization_map) if generalization
        was performed, or None if no generalization was needed.
    """
    from .proof import Clause

    used_names: Set[Term] = set()
    collect_rigid_terms(clause, engine, used_names, induction_var)

    if not used_names:
        return None

    rigid_terms = sorted(used_names, key=lambda t: (str(t),))

    term_to_var: Dict[Term, Var] = {}
    var_to_term: Dict[Var, Term] = {}

    for term in rigid_terms:
        fresh = _fresh_var_for_term(term, engine)
        term_to_var[term] = fresh
        var_to_term[fresh] = term

    generalized_assumptions = tuple(
        (_replace_terms(lhs, term_to_var), _replace_terms(rhs, term_to_var))
        for lhs, rhs in clause.assumptions
    )
    generalized_goal = _replace_terms(clause.goal, term_to_var)
    generalized_disequalities = tuple(
        (_replace_terms(lhs, term_to_var), _replace_terms(rhs, term_to_var))
        for lhs, rhs in clause.disequalities
    )

    new_equality_assumptions: list[Tuple[Term, Term]] = []
    for original_term, fresh_var in term_to_var.items():
        new_equality_assumptions.append((fresh_var, original_term))

    all_assumptions = generalized_assumptions + tuple(new_equality_assumptions)

    generalized_clause = Clause(
        all_assumptions,
        generalized_goal,
        generalized_disequalities,
    )

    gen_map = GeneralizationMap(
        term_to_var=tuple(term_to_var.items()),
        var_to_term=tuple(var_to_term.items()),
    )

    return (generalized_clause, gen_map)


def _fresh_var_for_term(term: Term, engine: Engine) -> Var:
    """Create a fresh variable to replace a term during generalization."""
    from .syntax import V

    sort = _infer_term_sort_unsafe(term, engine)
    counter = 0
    base_name = "g"
    while True:
        name = f"{base_name}_{counter}"
        if not _name_used(name, engine):
            return V(name, sort)
        counter += 1


def _name_used(name: str, engine: Engine) -> bool:
    """Check if a variable name is already in use in the global var interner."""
    return name in _VAR_NAME_SORT


def _infer_term_sort_unsafe(term: Term, engine: Engine) -> Optional[str]:
    """Infer the sort of a term, returning None if it cannot be determined."""
    try:
        from .validation import infer_sort

        return infer_sort(term, engine)
    except Exception:
        return None


def collect_rigid_terms(
    clause: Clause,
    engine: Engine,
    result: Set[Term],
    induction_var: Optional[Var] = None,
) -> None:
    """Collect all rigid (generalizable) subterms in a clause.

    A term is considered rigid if:
    - It appears multiple times (count >= 2) and is a compound term
    - It is a ground compound term (base constructor applications are excluded)

    The goal and assumption terms themselves are NOT collected - only their
    proper subterms are considered.

    Terms containing the induction variable are NOT considered rigid, to avoid
    interfering with the induction itself.

    Args:
        clause: The clause to analyze.
        engine: The proving engine.
        result: Set to accumulate rigid terms into.
        induction_var: Optional variable that will be used for induction;
                      terms containing this variable are skipped.
    """
    subterm_counts: Dict[Term, int] = {}

    _count_proper_subterms(clause.goal, subterm_counts)

    for lhs, rhs in clause.assumptions:
        _count_proper_subterms(lhs, subterm_counts)
        _count_proper_subterms(rhs, subterm_counts)

    for lhs, rhs in clause.disequalities:
        _count_proper_subterms(lhs, subterm_counts)
        _count_proper_subterms(rhs, subterm_counts)

    for term, count in subterm_counts.items():
        if induction_var is not None and contains_var(term, induction_var):
            continue
        if _is_base_constructor(term):
            continue
        if count >= 2:
            result.add(term)
        elif _is_rigid_ground(term):
            result.add(term)


def _count_subterms(term: Term, counts: Dict[Term, int]) -> None:
    """Count this term and all its subterms recursively."""
    match term:
        case Var():
            return
        case Fun(_, args):
            counts[term] = counts.get(term, 0) + 1
            for arg in args:
                _count_subterms(arg, counts)
            return
    raise TypeError(f"Unsupported term type: {type(term)!r}")


def _count_proper_subterms(term: Term, counts: Dict[Term, int]) -> None:
    """Count proper subterms (excluding the term itself).

    Only proper subterms of the given term are counted, not the term itself.
    This is used to avoid collecting the goal/assumption terms themselves.
    """
    match term:
        case Var():
            return
        case Fun(_, args):
            for arg in args:
                _count_subterms(arg, counts)
            return
    raise TypeError(f"Unsupported term type: {type(term)!r}")


def _is_rigid_ground(term: Term) -> bool:
    """Check if a term is a rigid ground term.

    A term is rigid ground if it contains no variables and is not a
    base constructor (nullary function).
    """
    if _is_base_constructor(term):
        return False
    return is_ground(term)


def _is_base_constructor(term: Term) -> bool:
    """Check if a term is a base constructor (nullary function).

    Base constructors like '0', 'nil', 'true', 'false' are not generalized
    because they represent base values in the induction structure.
    """
    match term:
        case Fun(_, ()):
            return True
        case _:
            return False


def _replace_terms(term: Term, term_to_var: Dict[Term, Var]) -> Term:
    """Replace occurrences of terms with their corresponding fresh variables.

    Args:
        term: The term to transform.
        term_to_var: Mapping from original terms to fresh variables.

    Returns:
        The term with all occurrences of terms in term_to_var replaced by vars.
    """
    if term in term_to_var:
        return term_to_var[term]

    match term:
        case Var():
            return term
        case Fun(symbol, args):
            new_args = tuple(_replace_terms(arg, term_to_var) for arg in args)
            return Fun(symbol, new_args)
    raise TypeError(f"Unsupported term type: {type(term)!r}")


def destructor_elim_clause(
    clause: "Clause",
    var: Var,
    scheme: "InductionScheme",
    engine: Engine,
) -> Optional["Clause"]:
    """Eliminate destructor applications to the induction variable.

    Finds all direct applications of non-constructor functions to ``var``
    (i.e., terms of the form ``f(var, ...)`` or ``f(..., var, ...)``) that
    appear in the clause, replaces each with a fresh variable, and adds
    ``eq(fresh, original)`` assumptions.

    This is analogous to ACL2's destructor elimination.  It makes induction
    hypotheses more directly applicable by replacing opaque selector
    expressions (``head(xs)``, ``tail(xs)``, ``length(xs)``, …) with plain
    variables whose values are pinned by the new assumptions.

    Returns the updated clause, or ``None`` if no eliminations were made.
    """
    from .proof import Clause, vars_in_clause

    constructor_symbols: set[str] = {c.symbol for c in scheme.constructors}
    base_symbols: set[str] = set()
    for base in scheme.base_terms:
        match base:
            case Fun(sym, _):
                base_symbols.add(sym)

    # Collect all direct destructor-application terms.
    destr_terms: list[Term] = []
    seen: set[Term] = set()

    def _collect(term: Term) -> None:
        match term:
            case Var():
                return
            case Fun(symbol, args):
                if (
                    symbol not in constructor_symbols
                    and symbol not in base_symbols
                    and any(arg == var for arg in args)
                    and term not in seen
                ):
                    seen.add(term)
                    destr_terms.append(term)
                for arg in args:
                    _collect(arg)

    _collect(clause.goal)
    for lhs, rhs in clause.assumptions:
        _collect(lhs)
        _collect(rhs)
    for lhs, rhs in clause.disequalities:
        _collect(lhs)
        _collect(rhs)

    if not destr_terms:
        return None

    used_names = vars_in_clause(clause)
    term_to_var: Dict[Term, Var] = {}

    for term in destr_terms:
        sort = _infer_term_sort_unsafe(term, engine)
        counter = 0
        while f"d_{counter}" in used_names or f"d_{counter}" in _VAR_NAME_SORT:
            counter += 1
        name = f"d_{counter}"
        used_names.add(name)
        fresh = V(name, sort)
        term_to_var[term] = fresh

    new_goal = _replace_terms(clause.goal, term_to_var)
    new_assumptions = tuple(
        (_replace_terms(lhs, term_to_var), _replace_terms(rhs, term_to_var))
        for lhs, rhs in clause.assumptions
    )
    new_equalities = tuple(
        (fresh_v, term) for term, fresh_v in term_to_var.items()
    )
    new_disequalities = tuple(
        (_replace_terms(lhs, term_to_var), _replace_terms(rhs, term_to_var))
        for lhs, rhs in clause.disequalities
    )

    return Clause(
        new_assumptions + new_equalities,
        new_goal,
        new_disequalities,
    )


def ungeneralize_term(term: Term, gen_map: GeneralizationMap) -> Term:
    """Apply the inverse of a generalization to a term.

    This replaces fresh generalization variables with their original terms.

    Args:
        term: The term to ungeneralize.
        gen_map: The generalization map from generalize_clause.

    Returns:
        The term with generalization variables replaced by original terms.
    """
    subst: Dict[Var, Term] = dict(gen_map.var_to_term)
    return apply_subst(term, subst)


def ungeneralize_clause(clause: Clause, gen_map: GeneralizationMap) -> Clause:
    """Apply the inverse of a generalization to a clause.

    Args:
        clause: The generalized clause.
        gen_map: The generalization map from generalize_clause.

    Returns:
        The clause with generalization variables replaced by original terms.
    """
    from .proof import Clause

    subst: Dict[Var, Term] = dict(gen_map.var_to_term)

    ungeneralized_assumptions = tuple(
        (apply_subst(lhs, subst), apply_subst(rhs, subst))
        for lhs, rhs in clause.assumptions
    )
    ungeneralized_goal = apply_subst(clause.goal, subst)
    ungeneralized_disequalities = tuple(
        (apply_subst(lhs, subst), apply_subst(rhs, subst))
        for lhs, rhs in clause.disequalities
    )

    return Clause(
        ungeneralized_assumptions,
        ungeneralized_goal,
        ungeneralized_disequalities,
    )
