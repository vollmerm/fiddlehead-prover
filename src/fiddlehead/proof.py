from __future__ import annotations

"""Clause-level proof search, induction branching, and certificates.

This module turns kernel normalization into a small proof procedure that
simplifies goals, splits conditional branches, optionally performs induction,
and can produce/check compact proof certificates.
"""

from dataclasses import dataclass
from typing import Callable, Optional, Tuple

from .kernel import (
    Context,
    Engine,
    InductionScheme,
    Rule,
    _term_key,
    get_induction_scheme,
    is_ground,
    make_engine,
    normalize,
    var_matches_scheme,
)
from .syntax import App, Fun, Term, V, Var, apply_subst, false, true
from .trace import ProofNode, ProofTrace, _new_node
from .validation import _validate_clause_sorts, _validate_rule_sorts
from .generalize import generalize_clause, ungeneralize_clause, GeneralizationMap
from .select_induction import choose_induction_var


@dataclass(frozen=True)
class Clause:
    """A goal with local equality and disequality assumptions."""

    assumptions: Tuple[Tuple[Term, Term], ...]
    goal: Term
    disequalities: Tuple[Tuple[Term, Term], ...] = ()


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


def vars_in_term(term: Term) -> set[str]:
    """Collect variable names appearing in a term."""

    match term:
        case Var(name, _):
            return {name}
        case Fun(_, _):
            names: set[str] = set()
            for arg in term.args:
                names |= vars_in_term(arg)
            return names
    raise TypeError(f"Unsupported term type: {type(term)!r}")


def vars_in_clause(clause: Clause) -> set[str]:
    """Collect variable names appearing in a clause."""

    names = vars_in_term(clause.goal)
    for left, right in clause.assumptions:
        names |= vars_in_term(left)
        names |= vars_in_term(right)
    for left, right in clause.disequalities:
        names |= vars_in_term(left)
        names |= vars_in_term(right)
    return names


def instantiate_clause(clause: Clause, subst: dict[Var, Term]) -> Clause:
    """Apply a substitution across assumptions and goal."""

    assumptions = tuple(
        (apply_subst(left, subst), apply_subst(right, subst))
        for left, right in clause.assumptions
    )
    disequalities = tuple(
        (apply_subst(left, subst), apply_subst(right, subst))
        for left, right in clause.disequalities
    )
    return Clause(assumptions, apply_subst(clause.goal, subst), disequalities)


def goal_equality(goal: Term) -> Optional[Tuple[Term, Term]]:
    """Extract ``(lhs, rhs)`` from an ``eq(lhs, rhs)`` goal."""

    match goal:
        case Fun("eq", (left, right)):
            return left, right
    return None


def fresh_var(base: str, used_names: set[str], sort: Optional[str] = None) -> Var:
    """Create a fresh variable name not present in ``used_names``."""

    counter = 0
    candidate = f"{base}_{counter}"
    while candidate in used_names:
        counter += 1
        candidate = f"{base}_{counter}"
    used_names.add(candidate)
    return V(candidate, sort)


def induction_branches(
    clause: Clause, var: Var, scheme: InductionScheme
) -> list[Clause]:
    """Generate base and step obligations for an induction application."""

    if not var_matches_scheme(var, scheme):
        return []

    used = vars_in_clause(clause).copy()
    branches: list[Clause] = []

    for base in scheme.base_terms:
        branches.append(instantiate_clause(clause, {var: base}))

    for constructor in scheme.constructors:
        rec_vars = [
            fresh_var(f"{var.name}_ih", used, scheme.sort)
            for _ in constructor.recursive_positions
        ]
        ih_assumptions: list[Tuple[Term, Term]] = []
        for rec_var in rec_vars:
            ih_goal = instantiate_clause(clause, {var: rec_var}).goal
            eq_goal = goal_equality(ih_goal)
            if eq_goal is None:
                return []
            ih_assumptions.append(eq_goal)

        args: list[Term] = [
            fresh_var(f"{var.name}_{constructor.symbol}_arg", used)
            for _ in range(constructor.arity)
        ]
        for position, rec_var in zip(constructor.recursive_positions, rec_vars):
            args[position] = rec_var

        step_term = App(constructor.symbol, *args)
        step_clause = instantiate_clause(clause, {var: step_term})
        branches.append(
            Clause(
                step_clause.assumptions + tuple(ih_assumptions),
                step_clause.goal,
                step_clause.disequalities,
            )
        )

    return branches


def simplify_clause(clause: Clause, engine: Engine) -> Clause:
    """Simplify assumptions and goal in one pass."""

    simplified, _ = simplify_clause_with_stages(clause, engine)
    return simplified


def simplify_clause_with_stages(
    clause: Clause, engine: Engine
) -> tuple[Clause, list[tuple[str, Clause]]]:
    """Simplify a clause and return intermediate stage snapshots."""

    stages: list[tuple[str, Clause]] = []
    _validate_clause_sorts(clause, engine, "clause")

    assumptions = _simplify_assumptions(clause.assumptions, engine)
    disequalities = _simplify_disequalities(clause.disequalities, engine)
    stage_clause = Clause(assumptions, clause.goal, disequalities)
    stages.append(("assumptions", stage_clause))

    base_goal = _normalize_with_rules_only(stage_clause.goal, engine)
    stage_clause = Clause(assumptions, base_goal, disequalities)
    stages.append(("rule-goal", stage_clause))

    local_engine = make_engine(
        rules=engine.rules,
        ctx=_build_context(assumptions, disequalities),
        trace=engine.trace,
        fuel=engine.fuel,
        config=engine.config,
        ground_cache=engine.ground_cache,
        schemes=engine.schemes,
        sort_signatures=engine.sort_signatures,
        sort_arities=engine.sort_arities,
    )
    contextual_goal = normalize(base_goal, local_engine)
    stage_clause = Clause(assumptions, contextual_goal, disequalities)
    stages.append(("context-goal", stage_clause))

    eq_goal = goal_equality(contextual_goal)
    if eq_goal is not None and local_engine.holds(eq_goal[0], eq_goal[1]):
        stage_clause = Clause(assumptions, true, disequalities)
        stages.append(("context-solved", stage_clause))

    return stage_clause, stages


def _normalize_with_rules_only(term: Term, engine: Engine) -> Term:
    base_engine = make_engine(
        rules=engine.rules,
        ctx=Context(),
        trace=engine.trace,
        fuel=engine.fuel,
        config=engine.config,
        ground_cache=engine.ground_cache,
        schemes=engine.schemes,
        sort_signatures=engine.sort_signatures,
        sort_arities=engine.sort_arities,
    )
    return normalize(term, base_engine)


def _simplify_assumptions(
    assumptions: Tuple[Tuple[Term, Term], ...],
    engine: Engine,
) -> Tuple[Tuple[Term, Term], ...]:
    seen: set[tuple[Term, Term]] = set()
    out: list[tuple[Term, Term]] = []
    for left, right in assumptions:
        left_norm = _normalize_with_rules_only(left, engine)
        right_norm = _normalize_with_rules_only(right, engine)
        if left_norm == right_norm:
            continue
        pair = (
            (left_norm, right_norm)
            if _term_key(left_norm) <= _term_key(right_norm)
            else (right_norm, left_norm)
        )
        if pair in seen:
            continue
        seen.add(pair)
        out.append(pair)
    return tuple(out)


def _simplify_disequalities(
    disequalities: Tuple[Tuple[Term, Term], ...],
    engine: Engine,
) -> Tuple[Tuple[Term, Term], ...]:
    seen: set[tuple[Term, Term]] = set()
    out: list[tuple[Term, Term]] = []
    for left, right in disequalities:
        left_norm = _normalize_with_rules_only(left, engine)
        right_norm = _normalize_with_rules_only(right, engine)
        pair = (
            (left_norm, right_norm)
            if _term_key(left_norm) <= _term_key(right_norm)
            else (right_norm, left_norm)
        )
        if pair in seen:
            continue
        seen.add(pair)
        out.append(pair)
    return tuple(out)


def clause_solved(clause: Clause) -> bool:
    """Return whether the clause is discharged (goal is ``true``)."""

    return clause.goal == true


def clause_is_unsatisfiable(clause: Clause, engine: Engine) -> bool:
    """Return True if clause contains a contradiction between assumptions and disequalities.

    A contradiction occurs when a disequality (lhs ≠ rhs) is provably true
    under the contextual equalities from assumptions.
    """
    local = _local_engine_for_clause(clause, engine)
    for dl, dr in clause.disequalities:
        if local.holds(dl, dr):
            return True
    return False


def split_clause(clause: Clause) -> list[Clause]:
    """Split ``if`` goals into branch obligations."""

    match clause.goal:
        case Fun("if", (cond, then_branch, else_branch)):
            match cond:
                case Fun("eq", (left, right)):
                    return [
                        Clause(
                            clause.assumptions + ((left, right),),
                            then_branch,
                            clause.disequalities,
                        ),
                        Clause(
                            clause.assumptions,
                            else_branch,
                            clause.disequalities + ((left, right),),
                        ),
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


def _prove_kernel(
    clause: Clause,
    engine: Engine,
    depth: int,
    induction_handler: Optional[
        Callable[[Clause, int, Optional[ProofNode]], Optional[bool]]
    ] = None,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    with engine.var_context():
        return _prove_kernel_impl(clause, engine, depth, induction_handler, proof_node)


def _prove_kernel_impl(
    clause: Clause,
    engine: Engine,
    depth: int,
    induction_handler: Optional[
        Callable[[Clause, int, Optional[ProofNode]], Optional[bool]]
    ] = None,
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
    if clause_is_unsatisfiable(simplified, engine):
        if proof_node is not None:
            proof_node.solved = False
        return False

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
    for index, branch in enumerate(branches):
        child = _new_node("branch", branch, note=f"index={index}")
        if proof_node is not None:
            proof_node.children.append(child)
        branch_results.append(
            _prove_kernel_impl(branch, engine, next_depth, induction_handler, child)
        )
    out = all(branch_results)
    if proof_node is not None:
        proof_node.solved = out
    return out


def prove(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    """Attempt proof by simplify/split recursion up to ``depth``."""

    return _prove_kernel(clause, engine, depth, proof_node=proof_node)


def prove_with_induction(
    clause: Clause,
    engine: Engine,
    var: Var,
    scheme: InductionScheme,
    depth: int = 5,
    induction_depth: int = 1,
    proof_node: Optional[ProofNode] = None,
    generalize: bool = True,
) -> bool:
    """Attempt proof with optional induction when plain recursion stalls.

    Args:
        clause: The clause to prove.
        engine: The proving engine.
        var: The induction variable.
        scheme: The induction scheme.
        depth: Maximum proof search depth.
        induction_depth: Number of nested inductions allowed.
        proof_node: Optional proof tree node for tracing.
        generalize: If True (default), attempt generalization before induction
                   to make the goal more amenable to proof. If False, skip
                   generalization.

    Returns:
        True if the proof succeeded, False otherwise.
    """

    if not var_matches_scheme(var, scheme):
        if proof_node is not None:
            proof_node.solved = False
            proof_node.note = f"sort mismatch for scheme {scheme.name}"
        return False

    generalized_result: Optional[bool] = None
    gen_map: Optional[GeneralizationMap] = None

    if generalize and induction_depth > 0:
        gen_result = generalize_clause(clause, engine, induction_var=var)
        if gen_result is not None:
            generalized_clause, gen_map = gen_result
            if proof_node is not None:
                gen_node = _new_node(
                    "generalize",
                    clause,
                    note=f"var={var.name}, scheme={scheme.name}",
                )
                proof_node.children.append(gen_node)
                proof_node.solved = None
            generalized_result = _prove_induction_on_clause(
                generalized_clause,
                engine,
                var,
                scheme,
                depth,
                induction_depth,
                gen_node if proof_node is not None else None,
                f"var={var.name}, scheme={scheme.name}, generalized",
            )
            if generalized_result:
                return True

    return _prove_induction_on_clause(
        clause,
        engine,
        var,
        scheme,
        depth,
        induction_depth,
        proof_node,
        f"var={var.name}, scheme={scheme.name}",
    )


def _prove_induction_on_clause(
    clause: Clause,
    engine: Engine,
    var: Var,
    scheme: InductionScheme,
    depth: int,
    induction_depth: int,
    proof_node: Optional[ProofNode],
    note: str,
) -> bool:
    """Helper that runs the actual induction proof on a given clause."""

    def induction_handler(
        simplified_clause: Clause,
        current_depth: int,
        current_node: Optional[ProofNode],
    ) -> Optional[bool]:
        if induction_depth <= 0:
            return False
        branches = induction_branches(simplified_clause, var, scheme)
        if not branches:
            return False
        induction_node = _new_node(
            "induction",
            simplified_clause,
            note=note,
        )
        if current_node is not None:
            current_node.children.append(induction_node)
        next_induction = induction_depth - 1
        branch_results = []
        for index, branch in enumerate(branches):
            child = _new_node("induction-branch", branch, note=f"index={index}")
            induction_node.children.append(child)
            branch_results.append(
                prove_with_induction(
                    branch,
                    engine,
                    var,
                    scheme,
                    current_depth,
                    next_induction,
                    child,
                    generalize=False,
                )
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
    generalize: bool = True,
) -> bool:
    """Run induction proof using a scheme looked up by name."""

    scheme = get_induction_scheme(engine, scheme_name)
    if scheme is None:
        if proof_node is not None:
            proof_node.solved = False
            proof_node.note = f"unknown scheme {scheme_name}"
        return False
    return prove_with_induction(
        clause, engine, var, scheme, depth, induction_depth, proof_node, generalize
    )


def prove_with_trace(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    var: Optional[Var] = None,
    scheme: Optional[InductionScheme] = None,
    scheme_name: Optional[str] = None,
    induction_depth: int = 1,
    generalize: bool = True,
) -> tuple[bool, ProofTrace]:
    """Run proof search and return both success flag and trace tree."""

    trace = ProofTrace()
    root = _new_node("prove", clause)
    trace.roots.append(root)

    if var is None:
        return prove(clause, engine, depth=depth, proof_node=root), trace
    if scheme is not None:
        return (
            prove_with_induction(
                clause,
                engine,
                var,
                scheme,
                depth=depth,
                induction_depth=induction_depth,
                proof_node=root,
                generalize=generalize,
            ),
            trace,
        )
    if scheme_name is not None:
        return (
            prove_with_registered_induction(
                clause,
                engine,
                var,
                scheme_name,
                depth=depth,
                induction_depth=induction_depth,
                proof_node=root,
                generalize=generalize,
            ),
            trace,
        )

    root.note = "missing scheme for induction trace"
    root.solved = False
    return False, trace


def prove_with_auto_induction(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    induction_depth: int = 1,
    proof_node: Optional[ProofNode] = None,
    generalize: bool = True,
) -> tuple[bool, ProofTrace]:
    """Run proof search with automatic induction variable selection.

    This function selects the induction variable automatically using
    heuristics (recursive call analysis, measure functions, type filtering).
    If auto-selection fails, raises ValueError.

    Args:
        clause: The clause to prove.
        engine: The proving engine.
        depth: Maximum proof search depth.
        induction_depth: Number of nested inductions allowed.
        proof_node: Optional proof tree node for tracing.
        generalize: If True, attempt generalization before induction.

    Returns:
        A tuple of (success, proof_trace).

    Raises:
        ValueError: If no suitable induction variable can be found.
    """
    auto_var = choose_induction_var(clause, engine)
    sort = auto_var.sort
    if sort is None:
        raise ValueError(
            f"Cannot auto-select induction scheme for variable {auto_var.name}: "
            f"sort is None. Ensure the variable has a declared sort."
        )
    auto_scheme = get_induction_scheme(engine, sort + "-induction")
    if auto_scheme is None:
        auto_scheme = _get_scheme_for_sort(engine, sort)
    if auto_scheme is None:
        raise ValueError(
            f"Cannot auto-select induction scheme for variable {auto_var.name} "
            f"with sort {auto_var.sort}. Ensure a scheme is registered."
        )

    trace = ProofTrace()
    root = proof_node if proof_node is not None else _new_node("prove", clause)
    if proof_node is None:
        trace.roots.append(root)

    auto_node = _new_node(
        "auto-induction-select",
        clause,
        note=f"auto-selected var={auto_var.name} with scheme={auto_scheme.name}",
    )
    root.children.append(auto_node)
    root.solved = None

    success = prove_with_induction(
        clause,
        engine,
        auto_var,
        auto_scheme,
        depth=depth,
        induction_depth=induction_depth,
        proof_node=auto_node,
        generalize=generalize,
    )
    root.solved = success
    return success, trace


def _get_scheme_for_sort(engine: Engine, sort: str) -> Optional[InductionScheme]:
    """Get the induction scheme for a given sort."""
    for scheme in engine.schemes.values():
        if scheme.sort == sort:
            return scheme
    return None


@dataclass(frozen=True)
class ProofCertificate:
    """A checked-proof artifact that records applied proof steps."""

    clause: Clause
    simplified: Clause
    step: str
    children: Tuple["ProofCertificate", ...] = ()
    var: Optional[Var] = None
    scheme_name: Optional[str] = None


def _local_engine_for_clause(clause: Clause, engine: Engine) -> Engine:
    return make_engine(
        rules=engine.rules,
        ctx=_build_context(clause.assumptions, clause.disequalities),
        trace=engine.trace,
        fuel=engine.fuel,
        config=engine.config,
        ground_cache=engine.ground_cache,
        schemes=engine.schemes,
        sort_signatures=engine.sort_signatures,
        sort_arities=engine.sort_arities,
    )


def _check_simplify_step(clause: Clause, engine: Engine) -> Clause:
    return simplify_clause(clause, engine)


def _check_split_step(clause: Clause) -> list[Clause]:
    return split_clause(clause)


def _check_induction_step(
    clause: Clause,
    var: Var,
    scheme: InductionScheme,
    engine: Engine,
) -> list[Clause]:
    branches = induction_branches(clause, var, scheme)
    if not branches:
        raise ValueError("Induction does not apply to this goal/scheme.")
    for index, branch in enumerate(branches):
        _validate_clause_sorts(branch, engine, f"induction branch[{index}]")
    return branches


def _goal_holds_in_assumptions(clause: Clause, engine: Engine) -> bool:
    eq_goal = goal_equality(clause.goal)
    if eq_goal is None:
        return False
    left, right = eq_goal
    local = _local_engine_for_clause(clause, engine)
    return local.holds(left, right)


def _check_exact_step(clause: Clause, engine: Engine) -> Clause:
    if clause_solved(clause) or _goal_holds_in_assumptions(clause, engine):
        return Clause(clause.assumptions, true, clause.disequalities)
    raise ValueError("Goal is not solved and does not follow from assumptions.")


def _check_rewrite_step(clause: Clause, rule: Rule, engine: Engine) -> Clause:
    _validate_rule_sorts(rule, engine, "rewrite step")
    local = _local_engine_for_clause(clause, engine)
    rewritten = local.rewrite_once(clause.goal, rule)
    if rewritten is None:
        raise ValueError("Rewrite rule does not apply to current goal.")
    out = Clause(clause.assumptions, rewritten, clause.disequalities)
    _validate_clause_sorts(out, engine, "rewrite result")
    return out


def _rewrite_term_recursive(term: Term, rule: Rule, engine: Engine) -> Optional[Term]:
    """Try to rewrite term recursively, drilling into subterms.

    Returns (rewritten, changed) where changed indicates if a rewrite occurred.
    """
    from .syntax import Fun

    rewritten = engine.rewrite_once(term, rule)
    if rewritten is not None:
        return rewritten

    match term:
        case Fun(symbol, args) if args:
            new_args = []
            for arg in args:
                result = _rewrite_term_recursive(arg, rule, engine)
                if result is not None:
                    new_args.append(result)
                    return Fun(
                        symbol,
                        tuple(new_args[: len(args)] + list(args[len(new_args) :])),
                    )
                new_args.append(arg)
            return None
        case _:
            return None


def _rewrite_term_all(term: Term, rule: Rule, engine: Engine) -> Term:
    """Rewrite term recursively, applying rule everywhere in subtrees."""
    from .syntax import Fun

    rewritten = engine.rewrite_once(term, rule)
    if rewritten is not None:
        term = rewritten

    match term:
        case Fun(symbol, args) if args:
            new_args = [_rewrite_term_all(arg, rule, engine) for arg in args]
            return Fun(symbol, tuple(new_args))
        case _:
            return term


def _rewrite_first_subterm(term: Term, rule: Rule, engine: Engine) -> Optional[Term]:
    """Apply rule at most once, recursively searching into arguments.

    Returns the rewritten term if successful, None if no rewrite applied.
    """
    from .syntax import Fun

    rewritten = engine.rewrite_once(term, rule)
    if rewritten is not None:
        return rewritten

    match term:
        case Fun(symbol, args) if args:
            new_args = []
            for arg in args:
                result = _rewrite_first_subterm(arg, rule, engine)
                if result is not None:
                    new_args.append(result)
                    new_args.extend(args[len(new_args) :])
                    return Fun(symbol, tuple(new_args))
                new_args.append(arg)
            return None
        case _:
            return None


def _rewrite_all_subterms(term: Term, rule: Rule, engine: Engine) -> Term:
    """Apply rule everywhere in term, recursively drilling into all subterms."""
    from .syntax import Fun

    while True:
        rewritten = engine.rewrite_once(term, rule)
        if rewritten is not None:
            term = rewritten
            continue

        match term:
            case Fun(symbol, args) if args:
                new_args = []
                changed = False
                for arg in args:
                    result = _rewrite_all_subterms(arg, rule, engine)
                    if result != arg:
                        changed = True
                    new_args.append(result)
                if changed:
                    term = Fun(symbol, tuple(new_args))
                    continue
                break
            case _:
                break
        break

    return term


def _check_rewrite_first_step(clause: Clause, rule: Rule, engine: Engine) -> Clause:
    """Rewrite clause goal, drilling into subterms, applying at most once."""
    _validate_rule_sorts(rule, engine, "rewrite step")
    local = _local_engine_for_clause(clause, engine)
    rewritten = _rewrite_first_subterm(clause.goal, rule, local)
    if rewritten is None:
        raise ValueError("Rewrite rule does not apply to current goal or its subterms.")
    out = Clause(clause.assumptions, rewritten, clause.disequalities)
    _validate_clause_sorts(out, engine, "rewrite result")
    return out


def _check_rewrite_many_step(clause: Clause, rule: Rule, engine: Engine) -> Clause:
    """Rewrite clause goal, applying rule everywhere in subterms."""
    _validate_rule_sorts(rule, engine, "rewrite step")
    local = _local_engine_for_clause(clause, engine)
    rewritten = _rewrite_all_subterms(clause.goal, rule, local)
    out = Clause(clause.assumptions, rewritten, clause.disequalities)
    _validate_clause_sorts(out, engine, "rewrite result")
    return out


def _prove_certificate_kernel(
    clause: Clause,
    engine: Engine,
    depth: int,
    var: Optional[Var],
    scheme: Optional[InductionScheme],
    induction_depth: int,
) -> Optional[ProofCertificate]:
    with engine.var_context():
        return _prove_certificate_kernel_impl(
            clause, engine, depth, var, scheme, induction_depth
        )


def _prove_certificate_kernel_impl(
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
            child = _prove_certificate_kernel_impl(
                branch, engine, depth - 1, var, scheme, induction_depth
            )
            if child is None:
                return None
            children.append(child)
        return ProofCertificate(
            clause=clause,
            simplified=simplified,
            step="split",
            children=tuple(children),
        )

    if var is not None and scheme is not None and induction_depth > 0:
        induction_goals = induction_branches(simplified, var, scheme)
        if induction_goals:
            children = []
            for branch in induction_goals:
                child = _prove_certificate_kernel_impl(
                    branch,
                    engine,
                    depth,
                    var,
                    scheme,
                    induction_depth - 1,
                )
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
    """Attempt proof and return a certificate when successful."""

    if var is not None and scheme is None and scheme_name is not None:
        scheme = get_induction_scheme(engine, scheme_name)
    if var is not None and scheme is None:
        return False, None
    if var is not None and scheme is not None and not var_matches_scheme(var, scheme):
        return False, None

    cert = _prove_certificate_kernel(
        clause, engine, depth, var, scheme, induction_depth
    )
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
        if any(
            child.clause != branch for child, branch in zip(cert.children, branches)
        ):
            return False
        return all(
            _check_certificate_node(child, engine, depth - 1, induction_depth)
            for child in cert.children
        )

    if cert.step == "induction":
        if cert.var is None or cert.scheme_name is None or induction_depth <= 0:
            return False
        scheme = get_induction_scheme(engine, cert.scheme_name)
        if scheme is None or not var_matches_scheme(cert.var, scheme):
            return False
        branches = induction_branches(cert.simplified, cert.var, scheme)
        if len(branches) != len(cert.children):
            return False
        if any(
            child.clause != branch for child, branch in zip(cert.children, branches)
        ):
            return False
        return all(
            _check_certificate_node(child, engine, depth, induction_depth - 1)
            for child in cert.children
        )

    return False


def check_certificate(
    cert: ProofCertificate,
    engine: Engine,
    depth: int = 5,
    induction_depth: int = 1,
) -> bool:
    """Validate a certificate against engine semantics."""

    with engine.var_context():
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
        node.solved = (
            all(c.solved is True for c in node.children[1:]) if cert.children else False
        )
    return node


def certificate_to_proof_trace(cert: ProofCertificate) -> ProofTrace:
    """Convert a certificate tree into a renderable ``ProofTrace``."""

    trace = ProofTrace()
    trace.roots.append(_certificate_to_proof_node(cert))
    return trace
