from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from .kernel import (
    Context,
    Engine,
    InductionScheme,
    ProofNode,
    ProofTrace,
    Rule,
    _new_node,
    _term_key,
    _validate_clause_sorts,
    get_induction_scheme,
    make_engine,
    normalize,
    var_matches_scheme,
)
from .syntax import App, Term, Var, apply_subst, true


@dataclass(frozen=True)
class Clause:
    assumptions: Tuple[Tuple[Term, Term], ...]
    goal: Term


def vars_in_term(term: Term) -> set[str]:
    match term:
        case Var(name, _):
            return {name}
        case _:
            names: set[str] = set()
            for arg in getattr(term, "args", ()):
                names |= vars_in_term(arg)
            return names


def vars_in_clause(clause: Clause) -> set[str]:
    names = vars_in_term(clause.goal)
    for left, right in clause.assumptions:
        names |= vars_in_term(left)
        names |= vars_in_term(right)
    return names


def instantiate_clause(clause: Clause, subst: dict[Var, Term]) -> Clause:
    assumptions = tuple((apply_subst(left, subst), apply_subst(right, subst)) for left, right in clause.assumptions)
    return Clause(assumptions, apply_subst(clause.goal, subst))


def goal_equality(goal: Term) -> Optional[Tuple[Term, Term]]:
    match goal:
        case _ if getattr(goal, "symbol", None) == "eq" and len(getattr(goal, "args", ())) == 2:
            left, right = goal.args
            return left, right
    return None


def fresh_var(base: str, used_names: set[str], sort: Optional[str] = None) -> Var:
    counter = 0
    candidate = f"{base}_{counter}"
    while candidate in used_names:
        counter += 1
        candidate = f"{base}_{counter}"
    used_names.add(candidate)
    from .syntax import V

    return V(candidate, sort)


def induction_branches(clause: Clause, var: Var, scheme: InductionScheme) -> list[Clause]:
    if not var_matches_scheme(var, scheme):
        return []

    used = vars_in_clause(clause).copy()
    branches: list[Clause] = []

    for base in scheme.base_terms:
        branches.append(instantiate_clause(clause, {var: base}))

    for constructor in scheme.constructors:
        rec_vars = [fresh_var(f"{var.name}_ih", used, scheme.sort) for _ in constructor.recursive_positions]
        ih_assumptions: list[Tuple[Term, Term]] = []
        for rec_var in rec_vars:
            ih_goal = instantiate_clause(clause, {var: rec_var}).goal
            eq_goal = goal_equality(ih_goal)
            if eq_goal is None:
                return []
            ih_assumptions.append(eq_goal)

        args: list[Term] = [fresh_var(f"{var.name}_{constructor.symbol}_arg", used) for _ in range(constructor.arity)]
        for position, rec_var in zip(constructor.recursive_positions, rec_vars):
            args[position] = rec_var

        step_term = App(constructor.symbol, *args)
        step_clause = instantiate_clause(clause, {var: step_term})
        branches.append(Clause(step_clause.assumptions + tuple(ih_assumptions), step_clause.goal))

    return branches


def simplify_clause(clause: Clause, engine: Engine) -> Clause:
    simplified, _ = simplify_clause_with_stages(clause, engine)
    return simplified


def simplify_clause_with_stages(clause: Clause, engine: Engine) -> tuple[Clause, list[tuple[str, Clause]]]:
    stages: list[tuple[str, Clause]] = []
    _validate_clause_sorts(clause, engine, "clause")

    assumptions = _simplify_assumptions(clause.assumptions, engine)
    stage_clause = Clause(assumptions, clause.goal)
    stages.append(("assumptions", stage_clause))

    base_goal = _normalize_with_rules_only(stage_clause.goal, engine)
    stage_clause = Clause(assumptions, base_goal)
    stages.append(("rule-goal", stage_clause))

    local_engine = make_engine(
        rules=engine.rules,
        ctx=Context(assumptions),
        trace=engine.trace,
        fuel=engine.fuel,
        config=engine.config,
        ground_cache=engine.ground_cache,
        schemes=engine.schemes,
        sort_signatures=engine.sort_signatures,
    )
    contextual_goal = normalize(base_goal, local_engine)
    stage_clause = Clause(assumptions, contextual_goal)
    stages.append(("context-goal", stage_clause))

    eq_goal = goal_equality(contextual_goal)
    if eq_goal is not None and local_engine.holds(eq_goal[0], eq_goal[1]):
        stage_clause = Clause(assumptions, true)
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


def clause_solved(clause: Clause) -> bool:
    return clause.goal == true


def split_clause(clause: Clause) -> list[Clause]:
    goal = clause.goal
    if getattr(goal, "symbol", None) != "if" or len(getattr(goal, "args", ())) != 3:
        return [clause]

    cond, then_branch, else_branch = goal.args
    if getattr(cond, "symbol", None) == "eq" and len(getattr(cond, "args", ())) == 2:
        left, right = cond.args
        return [
            Clause(clause.assumptions + ((left, right),), then_branch),
            Clause(clause.assumptions, else_branch),
        ]
    return [
        Clause(clause.assumptions, then_branch),
        Clause(clause.assumptions, else_branch),
    ]


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
    for index, branch in enumerate(branches):
        child = _new_node("branch", branch, note=f"index={index}")
        if proof_node is not None:
            proof_node.children.append(child)
        branch_results.append(_prove_kernel(branch, engine, next_depth, induction_handler, child))
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
            note=f"var={var.name}, scheme={scheme.name}",
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
            ),
            trace,
        )

    root.note = "missing scheme for induction trace"
    root.solved = False
    return False, trace


@dataclass(frozen=True)
class ProofCertificate:
    clause: Clause
    simplified: Clause
    step: str
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
        sort_signatures=engine.sort_signatures,
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
        return Clause(clause.assumptions, true)
    raise ValueError("Goal is not solved and does not follow from assumptions.")


def _check_rewrite_step(clause: Clause, rule: Rule, engine: Engine) -> Clause:
    from .kernel import _validate_rule_sorts

    _validate_rule_sorts(rule, engine, "rewrite step")
    local = _local_engine_for_clause(clause, engine)
    rewritten = local.rewrite_once(clause.goal, rule)
    if rewritten is None:
        raise ValueError("Rewrite rule does not apply to current goal.")
    out = Clause(clause.assumptions, rewritten)
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
                child = _prove_certificate_kernel(
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
        if any(child.clause != branch for child, branch in zip(cert.children, branches)):
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
