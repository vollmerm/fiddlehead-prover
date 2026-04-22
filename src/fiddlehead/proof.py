from __future__ import annotations

"""Clause-level proof search, induction branching, and certificates.

This module turns kernel normalization into a small proof procedure that
simplifies goals, splits conditional branches, optionally performs induction,
and can produce/check compact proof certificates.
"""

from dataclasses import dataclass
from typing import Optional, Tuple

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
from .syntax import App, Fun, Term, V, Var, apply_subst, false, match, true
from .rule_classes import RuleClass
from .trace import ProofNode, ProofTrace, _new_node
from .validation import _validate_clause_sorts, _validate_rule_sorts
from .generalize import (
    GeneralizationMap,
    destructor_elim_clause,
    generalize_clause,
    ungeneralize_clause,
)
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
    current = clause
    for _ in range(4):
        _validate_clause_sorts(current, engine, "clause")

        assumptions = _simplify_assumptions(current.assumptions, engine)
        disequalities = _simplify_disequalities(current.disequalities, engine)
        stage_clause = Clause(assumptions, current.goal, disequalities)
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

        if clause_solved(stage_clause):
            return stage_clause, stages
        if stage_clause == current:
            return stage_clause, stages
        current = stage_clause

    return current, stages


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


def _term_contains(term: Term, sub: Term) -> bool:
    """Return True if ``sub`` appears structurally anywhere inside ``term``."""
    if term == sub:
        return True
    match term:
        case Fun(_, args):
            return any(_term_contains(arg, sub) for arg in args)
        case _:
            return False


def _subst_term(term: Term, from_term: Term, to_term: Term) -> Term:
    """Replace every structural occurrence of ``from_term`` in ``term`` with ``to_term``."""
    if term == from_term:
        return to_term
    match term:
        case Var():
            return term
        case Fun(symbol, args):
            new_args = tuple(_subst_term(arg, from_term, to_term) for arg in args)
            if new_args == args:
                return term
            return Fun(symbol, new_args)
    raise TypeError(f"Unsupported term type: {type(term)!r}")


def fertilize_clause(clause: Clause, engine: Engine) -> Optional[Clause]:
    """Apply fertilization: substitute a hypothesis equality structurally into the goal.

    For each assumption ``eq(lhs, rhs)``, try replacing every occurrence of
    ``lhs`` with ``rhs`` in the goal (forward), and every occurrence of ``rhs``
    with ``lhs`` (backward).  Returns the first simplified clause where the
    goal changed, or ``None`` if fertilization did not help.

    This complements ``_schematic_rules``-based rewriting, which only orients
    the rule one way and applies it through the normalizer.  Fertilization does
    a one-shot whole-goal structural substitution and is therefore able to
    resolve goals where the rule orientation is wrong or where simultaneous
    replacement of multiple occurrences is needed.
    """
    if goal_equality(clause.goal) is None and clause.goal != true and clause.goal != false:
        return None

    for lhs, rhs in clause.assumptions:
        if lhs == rhs:
            continue
        # Skip pure variable substitutions — already handled by simplification.
        if isinstance(lhs, Var) or isinstance(rhs, Var):
            continue
        for from_term, to_term in ((lhs, rhs), (rhs, lhs)):
            if not _term_contains(clause.goal, from_term):
                continue
            new_goal = _subst_term(clause.goal, from_term, to_term)
            if new_goal == clause.goal:
                continue
            candidate = Clause(clause.assumptions, new_goal, clause.disequalities)
            simplified = simplify_clause(candidate, engine)
            if clause_solved(simplified):
                return simplified
            if simplified.goal != clause.goal:
                return simplified
    return None


def _matching_subterms(
    pattern: Term, term: Term
) -> list[tuple[Term, dict[Var, Term]]]:
    """Return every subterm of ``term`` that matches ``pattern``."""

    matches: list[tuple[Term, dict[Var, Term]]] = []
    subst = match(pattern, term)
    if subst is not None:
        matches.append((term, subst))
    if isinstance(term, Fun):
        for arg in term.args:
            matches.extend(_matching_subterms(pattern, arg))
    return matches


def _forward_chain_conditions_hold(
    rule: Rule, subst: dict[Var, Term], clause: Clause, engine: Engine
) -> bool:
    if not rule.conditions:
        return True
    local = _local_engine_for_clause(clause, engine)
    for left, right in rule.conditions:
        if not local.holds(apply_subst(left, subst), apply_subst(right, subst)):
            return False
    return True


def forward_chain_clause(clause: Clause, engine: Engine) -> Optional[Clause]:
    """Add local equalities from forward-chaining-class rules.

    The initial forward-chaining pass is intentionally simple: when a
    forward-chaining rule's left-hand side matches the goal or any assumption
    subterm, add the corresponding instantiated equality as a new local
    assumption. The clause is not simplified here; callers can feed the result
    back into the normal proof loop.
    """

    theory = engine.theory
    if theory is None:
        return None
    entries = theory.list_named_rule_entries(rule_class=RuleClass.FORWARD_CHAINING)
    if not entries:
        return None

    seen = set(clause.assumptions)
    additions: list[tuple[Term, Term]] = []
    targets = [clause.goal]
    for left, right in clause.assumptions:
        targets.extend((left, right))

    for entry in entries.values():
        rule = entry.rule
        for target in targets:
            for matched_term, subst in _matching_subterms(rule.lhs, target):
                if not _forward_chain_conditions_hold(rule, subst, clause, engine):
                    continue
                derived = apply_subst(rule.rhs, subst)
                pair = (matched_term, derived)
                if pair[0] == pair[1] or pair in seen:
                    continue
                seen.add(pair)
                additions.append(pair)

    if not additions:
        return None
    return Clause(clause.assumptions + tuple(additions), clause.goal, clause.disequalities)


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


def prove(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    """Attempt proof using the waterfall prover without explicit induction."""

    return prove_with_waterfall(clause, engine, depth=depth, proof_node=proof_node)


def prove_with_induction(
    clause: Clause,
    engine: Engine,
    var: Var,
    scheme: InductionScheme,
    depth: int = 5,
    induction_depth: int = 1,
    proof_node: Optional[ProofNode] = None,
    generalize: bool = True,
    destructor_elim: bool = True,
) -> bool:
    """Attempt proof using the waterfall prover with explicit induction."""

    return prove_with_waterfall(
        clause,
        engine,
        depth=depth,
        var=var,
        scheme=scheme,
        induction_depth=induction_depth,
        generalize=generalize,
        destructor_elim=destructor_elim,
        proof_node=proof_node,
    )


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

    return prove_with_waterfall(
        clause,
        engine,
        depth=depth,
        var=var,
        scheme_name=scheme_name,
        induction_depth=induction_depth,
        generalize=generalize,
        proof_node=proof_node,
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
    if var is None:
        return prove_with_waterfall_trace(clause, engine, depth=depth)
    if scheme is None and scheme_name is None:
        trace = ProofTrace()
        root = _new_node("prove", clause)
        trace.roots.append(root)
        root.note = "missing scheme for induction trace"
        root.solved = False
        return False, trace
    return prove_with_waterfall_trace(
        clause,
        engine,
        depth=depth,
        var=var,
        scheme=scheme,
        scheme_name=scheme_name,
        induction_depth=induction_depth,
        generalize=generalize,
    )


def prove_with_auto_induction(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    induction_depth: int = 1,
    proof_node: Optional[ProofNode] = None,
    generalize: bool = True,
) -> tuple[bool, ProofTrace]:
    """Run waterfall proof search with automatic induction variable selection."""
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

    success = prove_with_waterfall(
        clause,
        engine,
        depth=depth,
        var=auto_var,
        scheme=auto_scheme,
        induction_depth=induction_depth,
        generalize=generalize,
        auto_induction=False,
        proof_node=auto_node,
    )
    root.solved = success
    return success, trace


def _resolve_waterfall_induction_target(
    clause: Clause,
    engine: Engine,
    var: Optional[Var],
    scheme: Optional[InductionScheme],
    auto_induction: bool,
    proof_node: Optional[ProofNode],
) -> tuple[Optional[Var], Optional[InductionScheme]]:
    if var is not None and scheme is not None:
        return var, scheme
    if not auto_induction:
        return None, None
    try:
        auto_var = choose_induction_var(clause, engine)
    except ValueError:
        return None, None
    auto_scheme = _get_scheme_for_sort(engine, auto_var.sort or "")
    if auto_scheme is None:
        return None, None
    if proof_node is not None:
        proof_node.children.append(
            _new_node(
                "waterfall-auto-induction-select",
                clause,
                note=f"var={auto_var.name}, scheme={auto_scheme.name}",
            )
        )
    return auto_var, auto_scheme


def _prove_with_waterfall_impl(
    clause: Clause,
    engine: Engine,
    depth: int,
    var: Optional[Var],
    scheme: Optional[InductionScheme],
    induction_depth: int,
    generalize: bool,
    destructor_elim: bool,
    auto_induction: bool,
    proof_node: Optional[ProofNode],
) -> bool:
    if proof_node is not None:
        proof_node.note = f"depth={depth}"
    if depth <= 0:
        if proof_node is not None:
            proof_node.solved = False
        return False

    simplified = simplify_clause(clause, engine)
    if proof_node is not None:
        proof_node.children.append(_new_node("waterfall-simplify", simplified))
    if clause_is_unsatisfiable(simplified, engine):
        if proof_node is not None:
            proof_node.children.append(_new_node("waterfall-prune", simplified))
            proof_node.solved = False
        return False
    if clause_solved(simplified):
        if proof_node is not None:
            proof_node.solved = True
        return True

    branches = split_clause(simplified)
    if len(branches) > 1:
        split_node = _new_node(
            "waterfall-split", simplified, note=f"branches={len(branches)}"
        )
        if proof_node is not None:
            proof_node.children.append(split_node)
        split_results: list[bool] = []
        for index, branch in enumerate(branches):
            child = _new_node("waterfall-branch", branch, note=f"index={index}")
            split_node.children.append(child)
            split_results.append(
                _prove_with_waterfall_impl(
                    branch,
                    engine,
                    depth - 1,
                    var,
                    scheme,
                    induction_depth,
                    generalize,
                    destructor_elim,
                    auto_induction,
                    child,
                )
            )
        split_node.solved = all(split_results)
        if proof_node is not None:
            proof_node.solved = split_node.solved
        return split_node.solved

    forward_chained = forward_chain_clause(simplified, engine)
    if forward_chained is not None and forward_chained != simplified:
        fc_node = _new_node("waterfall-forward-chain", forward_chained)
        if proof_node is not None:
            proof_node.children.append(fc_node)
        if _prove_with_waterfall_impl(
            forward_chained,
            engine,
            depth - 1,
            var,
            scheme,
            induction_depth,
            generalize,
            destructor_elim,
            auto_induction,
            fc_node,
        ):
            if proof_node is not None:
                proof_node.solved = True
            return True

    fertilized = fertilize_clause(simplified, engine)
    if fertilized is not None and fertilized != simplified:
        fert_node = _new_node("waterfall-fertilize", fertilized)
        if proof_node is not None:
            proof_node.children.append(fert_node)
        if _prove_with_waterfall_impl(
            fertilized,
            engine,
            depth - 1,
            var,
            scheme,
            induction_depth,
            generalize,
            destructor_elim,
            auto_induction,
            fert_node,
        ):
            if proof_node is not None:
                proof_node.solved = True
            return True

    chosen_var, chosen_scheme = _resolve_waterfall_induction_target(
        simplified, engine, var, scheme, auto_induction, proof_node
    )
    if chosen_var is not None and chosen_scheme is not None and induction_depth > 0:
        if destructor_elim:
            de_result = destructor_elim_clause(
                simplified, chosen_var, chosen_scheme, engine
            )
            if de_result is not None and de_result != simplified:
                de_node = _new_node(
                    "waterfall-destructor-elim",
                    de_result,
                    note=f"var={chosen_var.name}, scheme={chosen_scheme.name}",
                )
                if proof_node is not None:
                    proof_node.children.append(de_node)
                if _prove_with_waterfall_impl(
                    de_result,
                    engine,
                    depth - 1,
                    chosen_var,
                    chosen_scheme,
                    induction_depth,
                    generalize,
                    False,
                    auto_induction,
                    de_node,
                ):
                    if proof_node is not None:
                        proof_node.solved = True
                    return True

        if generalize:
            gen_result = generalize_clause(simplified, engine, induction_var=chosen_var)
            if gen_result is not None:
                generalized_clause, _ = gen_result
                if generalized_clause != simplified:
                    gen_node = _new_node(
                        "waterfall-generalize",
                        generalized_clause,
                        note=f"var={chosen_var.name}, scheme={chosen_scheme.name}",
                    )
                    if proof_node is not None:
                        proof_node.children.append(gen_node)
                    if _prove_with_waterfall_impl(
                        generalized_clause,
                        engine,
                        depth - 1,
                        chosen_var,
                        chosen_scheme,
                        induction_depth,
                        False,
                        destructor_elim,
                        auto_induction,
                        gen_node,
                    ):
                        if proof_node is not None:
                            proof_node.solved = True
                        return True

        induction_goals = induction_branches(simplified, chosen_var, chosen_scheme)
        if induction_goals:
            induction_node = _new_node(
                "waterfall-induction",
                simplified,
                note=f"var={chosen_var.name}, scheme={chosen_scheme.name}",
            )
            if proof_node is not None:
                proof_node.children.append(induction_node)
            results: list[bool] = []
            for index, branch in enumerate(induction_goals):
                child = _new_node(
                    "waterfall-induction-branch", branch, note=f"index={index}"
                )
                induction_node.children.append(child)
                results.append(
                    _prove_with_waterfall_impl(
                        branch,
                        engine,
                        depth,
                        chosen_var,
                        chosen_scheme,
                        induction_depth - 1,
                        generalize=False,
                        destructor_elim=False,
                        auto_induction=False,
                        proof_node=child,
                    )
                )
            induction_node.solved = all(results)
            if proof_node is not None:
                proof_node.solved = induction_node.solved
            return induction_node.solved

    if proof_node is not None:
        proof_node.solved = False
    return False


def prove_with_waterfall(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    var: Optional[Var] = None,
    scheme: Optional[InductionScheme] = None,
    scheme_name: Optional[str] = None,
    induction_depth: int = 1,
    generalize: bool = True,
    destructor_elim: bool = True,
    auto_induction: bool = False,
    proof_node: Optional[ProofNode] = None,
) -> bool:
    """Run proof search through an explicit waterfall of proof stages."""

    chosen_scheme = scheme
    if chosen_scheme is None and scheme_name is not None:
        chosen_scheme = get_induction_scheme(engine, scheme_name)
    if var is not None and chosen_scheme is not None and not var_matches_scheme(
        var, chosen_scheme
    ):
        if proof_node is not None:
            proof_node.solved = False
            proof_node.note = f"sort mismatch for scheme {chosen_scheme.name}"
        return False
    with engine.var_context():
        return _prove_with_waterfall_impl(
            clause,
            engine,
            depth,
            var,
            chosen_scheme,
            induction_depth,
            generalize,
            destructor_elim,
            auto_induction,
            proof_node,
        )


def prove_with_waterfall_trace(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    var: Optional[Var] = None,
    scheme: Optional[InductionScheme] = None,
    scheme_name: Optional[str] = None,
    induction_depth: int = 1,
    generalize: bool = True,
    destructor_elim: bool = True,
    auto_induction: bool = False,
) -> tuple[bool, ProofTrace]:
    """Run waterfall proof search and return a trace tree."""

    trace = ProofTrace()
    root = _new_node("prove", clause)
    trace.roots.append(root)
    return (
        prove_with_waterfall(
            clause,
            engine,
            depth=depth,
            var=var,
            scheme=scheme,
            scheme_name=scheme_name,
            induction_depth=induction_depth,
            generalize=generalize,
            destructor_elim=destructor_elim,
            auto_induction=auto_induction,
            proof_node=root,
        ),
        trace,
    )


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


def _check_destructor_elim_step(
    clause: Clause,
    var: Var,
    scheme: InductionScheme,
    engine: Engine,
) -> Optional[Clause]:
    return destructor_elim_clause(clause, var, scheme, engine)


def _check_generalize_step(
    clause: Clause, engine: Engine, induction_var: Var
) -> Optional[Clause]:
    result = generalize_clause(clause, engine, induction_var=induction_var)
    if result is None:
        return None
    generalized_clause, _ = result
    return generalized_clause


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


def _prove_waterfall_certificate_impl(
    clause: Clause,
    engine: Engine,
    depth: int,
    var: Optional[Var],
    scheme: Optional[InductionScheme],
    induction_depth: int,
    generalize: bool,
    destructor_elim: bool,
    auto_induction: bool,
) -> Optional[ProofCertificate]:
    if depth <= 0:
        return None

    simplified = simplify_clause(clause, engine)
    if clause_solved(simplified):
        return ProofCertificate(clause=clause, simplified=simplified, step="solved")

    branches = split_clause(simplified)
    if len(branches) > 1:
        children: list[ProofCertificate] = []
        for branch in branches:
            child = _prove_waterfall_certificate_impl(
                branch,
                engine,
                depth - 1,
                var,
                scheme,
                induction_depth,
                generalize,
                destructor_elim,
                auto_induction,
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

    forward_chained = forward_chain_clause(simplified, engine)
    if forward_chained is not None and forward_chained != simplified:
        child = _prove_waterfall_certificate_impl(
            forward_chained,
            engine,
            depth - 1,
            var,
            scheme,
            induction_depth,
            generalize,
            destructor_elim,
            auto_induction,
        )
        if child is not None:
            return ProofCertificate(
                clause=clause,
                simplified=simplified,
                step="forward-chain",
                children=(child,),
            )

    fertilized = fertilize_clause(simplified, engine)
    if fertilized is not None and fertilized != simplified:
        child = _prove_waterfall_certificate_impl(
            fertilized,
            engine,
            depth - 1,
            var,
            scheme,
            induction_depth,
            generalize,
            destructor_elim,
            auto_induction,
        )
        if child is not None:
            return ProofCertificate(
                clause=clause,
                simplified=simplified,
                step="fertilize",
                children=(child,),
            )

    chosen_var, chosen_scheme = _resolve_waterfall_induction_target(
        simplified, engine, var, scheme, auto_induction, proof_node=None
    )
    if chosen_var is not None and chosen_scheme is not None and induction_depth > 0:
        if destructor_elim:
            de_result = _check_destructor_elim_step(
                simplified, chosen_var, chosen_scheme, engine
            )
            if de_result is not None and de_result != simplified:
                child = _prove_waterfall_certificate_impl(
                    de_result,
                    engine,
                    depth - 1,
                    chosen_var,
                    chosen_scheme,
                    induction_depth,
                    generalize,
                    False,
                    False,
                )
                if child is not None:
                    return ProofCertificate(
                        clause=clause,
                        simplified=simplified,
                        step="destructor-elim",
                        children=(child,),
                        var=chosen_var,
                        scheme_name=chosen_scheme.name,
                    )

        if generalize:
            generalized_clause = _check_generalize_step(simplified, engine, chosen_var)
            if generalized_clause is not None and generalized_clause != simplified:
                child = _prove_waterfall_certificate_impl(
                    generalized_clause,
                    engine,
                    depth - 1,
                    chosen_var,
                    chosen_scheme,
                    induction_depth,
                    False,
                    destructor_elim,
                    False,
                )
                if child is not None:
                    return ProofCertificate(
                        clause=clause,
                        simplified=simplified,
                        step="generalize",
                        children=(child,),
                        var=chosen_var,
                        scheme_name=chosen_scheme.name,
                    )

        induction_goals = induction_branches(simplified, chosen_var, chosen_scheme)
        if induction_goals:
            for index, branch in enumerate(induction_goals):
                _validate_clause_sorts(branch, engine, f"induction branch[{index}]")
            children = []
            for branch in induction_goals:
                child = _prove_waterfall_certificate_impl(
                    branch,
                    engine,
                    depth,
                    chosen_var,
                    chosen_scheme,
                    induction_depth - 1,
                    False,
                    False,
                    False,
                )
                if child is None:
                    return None
                children.append(child)
            return ProofCertificate(
                clause=clause,
                simplified=simplified,
                step="induction",
                children=tuple(children),
                var=chosen_var,
                scheme_name=chosen_scheme.name,
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
    """Attempt checked proof using the waterfall prover."""

    return prove_checked_with_waterfall(
        clause,
        engine,
        depth=depth,
        var=var,
        scheme=scheme,
        scheme_name=scheme_name,
        induction_depth=induction_depth,
    )


def prove_checked_with_waterfall(
    clause: Clause,
    engine: Engine,
    depth: int = 5,
    var: Optional[Var] = None,
    scheme: Optional[InductionScheme] = None,
    scheme_name: Optional[str] = None,
    induction_depth: int = 1,
    generalize: bool = True,
    destructor_elim: bool = True,
    auto_induction: bool = False,
) -> tuple[bool, Optional[ProofCertificate]]:
    """Attempt waterfall proof search and return a certificate when successful."""

    if var is not None and scheme is None and scheme_name is not None:
        scheme = get_induction_scheme(engine, scheme_name)
    if var is not None and scheme is None and not auto_induction:
        return False, None
    if var is not None and scheme is not None and not var_matches_scheme(var, scheme):
        return False, None
    with engine.var_context():
        cert = _prove_waterfall_certificate_impl(
            clause,
            engine,
            depth,
            var,
            scheme,
            induction_depth,
            generalize,
            destructor_elim,
            auto_induction,
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

    expected_simplified = simplify_clause(cert.clause, engine)
    if expected_simplified != cert.simplified:
        return False

    if cert.step == "solved":
        return clause_solved(cert.simplified) and not cert.children

    if cert.step == "split":
        branches = split_clause(cert.simplified)
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

    if cert.step == "forward-chain":
        if len(cert.children) != 1:
            return False
        forward_chained = forward_chain_clause(cert.simplified, engine)
        if forward_chained is None or cert.children[0].clause != forward_chained:
            return False
        return _check_certificate_node(
            cert.children[0], engine, depth - 1, induction_depth
        )

    if cert.step == "fertilize":
        if len(cert.children) != 1:
            return False
        fertilized = fertilize_clause(cert.simplified, engine)
        if fertilized is None or cert.children[0].clause != fertilized:
            return False
        return _check_certificate_node(
            cert.children[0], engine, depth - 1, induction_depth
        )

    if cert.step == "destructor-elim":
        if (
            len(cert.children) != 1
            or cert.var is None
            or cert.scheme_name is None
            or induction_depth <= 0
        ):
            return False
        scheme = get_induction_scheme(engine, cert.scheme_name)
        if scheme is None or not var_matches_scheme(cert.var, scheme):
            return False
        de_result = _check_destructor_elim_step(cert.simplified, cert.var, scheme, engine)
        if de_result is None or cert.children[0].clause != de_result:
            return False
        return _check_certificate_node(
            cert.children[0], engine, depth - 1, induction_depth
        )

    if cert.step == "generalize":
        if len(cert.children) != 1 or cert.var is None or cert.scheme_name is None:
            return False
        scheme = get_induction_scheme(engine, cert.scheme_name)
        if scheme is None or not var_matches_scheme(cert.var, scheme):
            return False
        generalized_clause = _check_generalize_step(cert.simplified, engine, cert.var)
        if generalized_clause is None or cert.children[0].clause != generalized_clause:
            return False
        return _check_certificate_node(
            cert.children[0], engine, depth - 1, induction_depth
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
    if cert.step in {"induction", "destructor-elim", "generalize"}:
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
