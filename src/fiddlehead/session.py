from __future__ import annotations

"""Interactive proof-session API built on checked proof primitives."""

from typing import Optional, Tuple

from .kernel import Engine, InductionScheme, Rule
from .proof import (
    Clause,
    _check_exact_step,
    _check_induction_step,
    _check_rewrite_step,
    _check_split_step,
    clause_solved,
    goal_equality,
    simplify_clause_with_stages,
)
from .syntax import Term, Var, true
from .theory import Lemma, _select_induction_scheme, get_theorem_environment
from .trace import ProofNode, ProofTrace, _new_node


class ProofSession:
    """Stateful, tactic-style wrapper around proof goals and traces."""

    def __init__(self, clause: Clause, engine: Engine):
        self.engine = engine
        self.goals: list[Clause] = [clause]
        self.theory = get_theorem_environment(engine)
        self.trace = ProofTrace()
        self._trace_root = _new_node("session", clause, note="interactive")
        self.trace.roots.append(self._trace_root)

    def _record(
        self,
        kind: str,
        clause: Clause,
        note: str = "",
        solved: Optional[bool] = None,
        children: Optional[list[ProofNode]] = None,
    ) -> None:
        node = _new_node(kind, clause, note=note)
        if children:
            node.children.extend(children)
        node.solved = solved
        self._trace_root.children.append(node)

    def current_goal(self) -> Optional[Clause]:
        """Return the active goal, or ``None`` when all goals are solved."""

        if not self.goals:
            return None
        return self.goals[0]

    def _replace_current(self, new_goals: list[Clause]) -> None:
        self.goals = new_goals + self.goals[1:]

    def assumptions(self) -> Tuple[Tuple[Term, Term], ...]:
        """Return assumptions of the current goal."""

        goal = self.current_goal()
        if goal is None:
            return ()
        return goal.assumptions

    def keep_assumptions(self, indices: list[int]) -> None:
        """Retain only selected assumptions on the current goal."""

        goal = self.current_goal()
        if goal is None:
            raise ValueError("No goals left.")
        assumptions = list(goal.assumptions)
        chosen: list[Tuple[Term, Term]] = []
        for index in indices:
            if index < 0 or index >= len(assumptions):
                raise ValueError(f"Assumption index out of range: {index}")
            chosen.append(assumptions[index])
        next_goal = Clause(tuple(chosen), goal.goal, goal.disequalities)
        self._record(
            "session-keep-assumptions",
            goal,
            note=f"indices={indices}",
            children=[_new_node("goal", next_goal)],
        )
        self.goals[0] = next_goal

    def simp(self) -> None:
        """Simplify the current goal and discharge it if it becomes solved."""

        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        simplified, stage_data = simplify_clause_with_stages(original, self.engine)
        stage_nodes = [_new_node(f"stage-{name}", clause) for name, clause in stage_data]
        if clause_solved(simplified):
            self._record(
                "session-simp",
                original,
                note="discharged",
                solved=True,
                children=stage_nodes + [_new_node("goal", simplified)],
            )
            self.goals = self.goals[1:]
            return
        self._record(
            "session-simp",
            original,
            solved=False,
            children=stage_nodes + [_new_node("goal", simplified)],
        )
        self.goals[0] = simplified

    def split(self) -> None:
        """Split the current goal into branch subgoals."""

        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        branches = _check_split_step(original)
        kids = [_new_node("session-branch", branch, note=f"index={index}") for index, branch in enumerate(branches)]
        self._record("session-split", original, note=f"branches={len(branches)}", children=kids)
        self._replace_current(branches)

    def induct(
        self,
        var: Var,
        scheme: Optional[InductionScheme] = None,
        scheme_name: Optional[str] = None,
    ) -> None:
        """Apply induction to the current goal for a chosen variable/scheme."""

        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        chosen = _select_induction_scheme(self.engine, var, scheme=scheme, scheme_name=scheme_name)
        branches = _check_induction_step(original, var, chosen, self.engine)
        kids = [_new_node("induction-branch", branch, note=f"index={index}") for index, branch in enumerate(branches)]
        self._record(
            "session-induct",
            original,
            note=f"var={var.name}, scheme={chosen.name}",
            children=kids,
        )
        self._replace_current(branches)

    def induct_many(
        self,
        vars: list[Var],
        schemes: Optional[list[Optional[InductionScheme]]] = None,
        scheme_names: Optional[list[Optional[str]]] = None,
    ) -> None:
        """Apply induction sequentially over multiple variables."""

        if not self.goals:
            raise ValueError("No goals left.")
        if not vars:
            raise ValueError("induct_many requires at least one variable.")
        if schemes is not None and len(schemes) != len(vars):
            raise ValueError("schemes length must match vars length.")
        if scheme_names is not None and len(scheme_names) != len(vars):
            raise ValueError("scheme_names length must match vars length.")

        original = self.goals[0]
        pending = [original]
        plan: list[tuple[str, str]] = []
        for index, var in enumerate(vars):
            chosen = _select_induction_scheme(
                self.engine,
                var,
                scheme=schemes[index] if schemes is not None else None,
                scheme_name=scheme_names[index] if scheme_names is not None else None,
            )
            plan.append((var.name, chosen.name))
            next_pending: list[Clause] = []
            for clause in pending:
                next_pending.extend(_check_induction_step(clause, var, chosen, self.engine))
            pending = next_pending

        kids = [_new_node("induction-branch", branch, note=f"index={index}") for index, branch in enumerate(pending)]
        note = ", ".join(f"{name}:{scheme_name}" for name, scheme_name in plan)
        self._record("session-induct-many", original, note=note, children=kids)
        self._replace_current(pending)

    def rewrite(self, rule: Rule) -> None:
        """Rewrite the current goal once using ``rule``."""

        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        rewritten = _check_rewrite_step(original, rule, self.engine)
        self._record(
            "session-rewrite",
            original,
            note=f"{rule.lhs} -> {rule.rhs}",
            children=[_new_node("goal", rewritten)],
        )
        self.goals[0] = rewritten

    def exact(self) -> None:
        """Discharge the current goal when it is directly solved."""

        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        solved = _check_exact_step(original, self.engine)
        self._record("session-exact", original, solved=True, children=[_new_node("goal", solved)])
        self.goals = self.goals[1:]

    def register_lemma(self, lemma: Lemma, depth: int = 12, induction_depth: int = 2) -> None:
        """Register a proved lemma in the session theorem environment."""

        self.theory.register_lemma(lemma, depth=depth, induction_depth=induction_depth)

    def apply_lemma(self, name: str) -> None:
        """Add a lemma equality as a new assumption on the current goal."""

        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        lemma = self.theory.lemmas.get(name)
        if lemma is None:
            raise ValueError(f"Unknown lemma: {name}")
        eq_goal = goal_equality(lemma.clause.goal)
        if eq_goal is None:
            raise ValueError(f"Lemma {name} does not have an equality goal.")
        next_goal = Clause(
            original.assumptions + (eq_goal,),
            original.goal,
            original.disequalities,
        )
        self._record(
            "session-apply-lemma",
            original,
            note=name,
            children=[_new_node("goal", next_goal)],
        )
        self.goals[0] = next_goal

    def register_definition(
        self,
        name: str,
        lhs: Term,
        rhs: Term,
        scope: str = "definitions",
    ) -> None:
        """Register a non-recursive definition rule in the theorem environment."""

        self.theory.register_definition(name, lhs, rhs, scope=scope)

    def register_lemma_rewrite(
        self,
        lemma_name: str,
        scope: str = "lemmas",
        orientation: str = "auto",
    ) -> None:
        """Register a lemma as an oriented rewrite rule."""

        self.theory.register_lemma_rewrite(lemma_name, scope=scope, orientation=orientation)

    def activate_scope(self, name: str) -> None:
        """Activate a theorem scope and sync engine rules."""

        self.theory.activate_scope(name)
        self._record(
            "session-activate-scope",
            self.current_goal() or Clause((), true, ()),
            note=name,
        )

    def deactivate_scope(self, name: str) -> None:
        """Deactivate a theorem scope and sync engine rules."""

        self.theory.deactivate_scope(name)
        self._record(
            "session-deactivate-scope",
            self.current_goal() or Clause((), true, ()),
            note=name,
        )

    def qed(self) -> bool:
        """Return whether all goals are discharged."""

        done = not self.goals
        current = self.current_goal() or Clause((), true, ())
        self._record("session-qed", current, solved=done)
        return done
