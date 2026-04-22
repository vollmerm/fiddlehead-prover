from __future__ import annotations

"""Interactive proof-session API built on checked proof primitives."""

from typing import Dict, Optional, Tuple

from .kernel import Engine, InductionScheme, Rule, SortSignature, is_ground
from .proof import (
    Clause,
    _check_exact_step,
    _check_induction_step,
    _check_rewrite_first_step,
    _check_rewrite_many_step,
    _check_rewrite_step,
    clause_solved,
    goal_equality,
    simplify_clause_with_stages,
    split_clause,
)
from .rule_classes import RuleClass
from .select_induction import choose_induction_var
from .syntax import Term, Var, true
from .theory import (
    Lemma,
    RuleSource,
    _select_induction_scheme,
    get_theorem_environment,
)
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
        self._ih_rules: Dict[str, Rule] = {}
        self._sync_ih_rules()

    def _format_clause(self, clause: Optional[Clause] = None) -> str:
        """Render a clause in a compact, REPL-friendly form."""

        current = self.current_goal() if clause is None else clause
        if current is None:
            return "<no goals>"

        lines: list[str] = [f"goal: {current.goal}"]
        if current.assumptions:
            lines.append("assumptions:")
            for index, (lhs, rhs) in enumerate(current.assumptions):
                lines.append(f"  {index}. {lhs} = {rhs}")
        else:
            lines.append("assumptions: <none>")
        if current.disequalities:
            lines.append("disequalities:")
            for index, (lhs, rhs) in enumerate(current.disequalities):
                lines.append(f"  {index}. {lhs} != {rhs}")
        else:
            lines.append("disequalities: <none>")
        return "\n".join(lines)

    def format_goal(self, clause: Optional[Clause] = None) -> str:
        """Public wrapper for rendering a goal or arbitrary clause."""

        return self._format_clause(clause)

    def format_rules(
        self,
        pattern: Optional[str] = None,
        rule_class: Optional[RuleClass] = None,
    ) -> str:
        """Render named rules in a readable list for REPL use."""

        named = self.theory.list_named_rule_entries(pattern, rule_class=rule_class)
        if not named:
            return "<no named rules>"
        lines: list[str] = []
        for name, entry in named.items():
            class_text = ",".join(str(spec) for spec in entry.rule_classes)
            label = entry.source.name.lower()
            if class_text:
                label = f"{label}|{class_text}"
            lines.append(f"- {name} [{label}]: {entry.rule.lhs} -> {entry.rule.rhs}")
        return "\n".join(lines)

    def format_ihs(self) -> str:
        """Render available induction hypotheses in a readable list."""

        if not self._ih_rules:
            return "<no induction hypotheses>"
        lines: list[str] = []
        for name, rule in self._ih_rules.items():
            lines.append(f"- {name}: {rule.lhs} -> {rule.rhs}")
        return "\n".join(lines)

    def _available_named_rules(self) -> str:
        names = list(self.theory.list_named_rules().keys())
        if not names:
            return "<none>"
        preview = ", ".join(names[:8])
        if len(names) > 8:
            preview += ", ..."
        return preview

    def _available_ihs(self) -> str:
        if not self._ih_rules:
            return "<none>"
        names = list(self._ih_rules.keys())
        preview = ", ".join(names[:8])
        if len(names) > 8:
            preview += ", ..."
        return preview

    def _tactic_error(self, tactic: str, error: Exception) -> ValueError:
        """Attach the active goal and useful rewrite context to an error."""

        return ValueError(
            "\n".join(
                [
                    f"{tactic} failed: {error}",
                    self._format_clause(),
                    f"available IHs: {self._available_ihs()}",
                    f"named rules: {self._available_named_rules()}",
                ]
            )
        )

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
        self._sync_ih_rules()

    def _sync_ih_rules(self) -> None:
        """Extract and store IH rules from the current goal's assumptions."""
        if self.goals:
            self._ih_rules = self._extract_ih_rules(self.goals[0])
        else:
            self._ih_rules = {}

    def _extract_ih_rules(self, clause: Clause) -> Dict[str, Rule]:
        """Extract induction hypothesis rules from clause assumptions.

        IH criteria: an assumption is an IH if:
        - Both sides are non-ground (not a ground equality)
        - It's an equality that came from the induction step
        """
        rules: Dict[str, Rule] = {}
        counter = 0
        for lhs, rhs in clause.assumptions:
            if is_ground(lhs) and is_ground(rhs):
                continue
            rule = Rule(lhs, rhs, skip_decrease_check=True)
            rules[f"IH.{counter}"] = rule
            counter += 1
        return rules

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
        try:
            simplified, stage_data = simplify_clause_with_stages(
                original, self.engine
            )
        except ValueError as exc:
            raise self._tactic_error("simp", exc) from exc
        stage_nodes = [
            _new_node(f"stage-{name}", clause) for name, clause in stage_data
        ]
        if clause_solved(simplified):
            self._record(
                "session-simp",
                original,
                note="discharged",
                solved=True,
                children=stage_nodes + [_new_node("goal", simplified)],
            )
            self.goals = self.goals[1:]
            self._sync_ih_rules()
            return
        self._record(
            "session-simp",
            original,
            solved=False,
            children=stage_nodes + [_new_node("goal", simplified)],
        )
        self.goals[0] = simplified
        self._sync_ih_rules()

    def split(self) -> None:
        """Split the current goal into branch subgoals."""

        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        try:
            branches = split_clause(original)
        except ValueError as exc:
            raise self._tactic_error("split", exc) from exc
        kids = [
            _new_node("session-branch", branch, note=f"index={index}")
            for index, branch in enumerate(branches)
        ]
        self._record(
            "session-split", original, note=f"branches={len(branches)}", children=kids
        )
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
        try:
            chosen = _select_induction_scheme(
                self.engine, var, scheme=scheme, scheme_name=scheme_name
            )
            branches = _check_induction_step(original, var, chosen, self.engine)
        except ValueError as exc:
            raise self._tactic_error("induct", exc) from exc
        kids = [
            _new_node("induction-branch", branch, note=f"index={index}")
            for index, branch in enumerate(branches)
        ]
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
        try:
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
                    next_pending.extend(
                        _check_induction_step(clause, var, chosen, self.engine)
                    )
                pending = next_pending
        except ValueError as exc:
            raise self._tactic_error("induct_many", exc) from exc

        kids = [
            _new_node("induction-branch", branch, note=f"index={index}")
            for index, branch in enumerate(pending)
        ]
        note = ", ".join(f"{name}:{scheme_name}" for name, scheme_name in plan)
        self._record("session-induct-many", original, note=note, children=kids)
        self._replace_current(pending)

    def auto_induct(self) -> None:
        """Apply induction with automatic variable selection.

        The variable is chosen using heuristics (recursive call analysis,
        measure functions, type filtering). Raises ValueError if no
        suitable variable can be found.

        Raises:
            ValueError: If no suitable induction variable can be found.
        """
        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        try:
            auto_var = choose_induction_var(original, self.engine)
            scheme = _select_induction_scheme(self.engine, auto_var)
            branches = _check_induction_step(original, auto_var, scheme, self.engine)
        except ValueError as exc:
            raise self._tactic_error("auto_induct", exc) from exc
        kids = [
            _new_node("induction-branch", branch, note=f"index={index}")
            for index, branch in enumerate(branches)
        ]
        self._record(
            "session-auto-induct",
            original,
            note=f"auto-selected var={auto_var.name}, scheme={scheme.name}",
            children=kids,
        )
        self._replace_current(branches)

    def rewrite_by_name(self, name: str) -> None:
        """Rewrite the current goal once using a named rule.

        Checks induction hypotheses first (e.g., 'IH.0'), then falls back
        to theory rules (definitions, lemmas, installed theories).

        Args:
            name: The name of the rule to apply (IH name or theory rule name).

        Raises:
            ValueError: If no goals remain or the named rule is not found.
        """
        if not self.goals:
            raise ValueError("No goals left.")

        if name in self._ih_rules:
            rule = self._ih_rules[name]
            original = self.goals[0]
            try:
                rewritten = _check_rewrite_step(original, rule, self.engine)
            except ValueError as exc:
                raise self._tactic_error(f"rewrite_by_name({name})", exc) from exc
            self._record(
                "session-rewrite-by-name",
                original,
                note=f"{name} (ih)",
                children=[_new_node("goal", rewritten)],
            )
            self.goals[0] = rewritten
            return

        entry = self.theory.get_named_rule_info(name)
        if entry is None:
            raise ValueError(
                f"Unknown named rule: {name}\n"
                f"available IHs: {self._available_ihs()}\n"
                f"named rules: {self._available_named_rules()}"
            )

        rule, source = entry
        original = self.goals[0]
        user_rule = Rule(rule.lhs, rule.rhs, rule.conditions, skip_decrease_check=True)
        try:
            rewritten = _check_rewrite_step(original, user_rule, self.engine)
        except ValueError as exc:
            raise self._tactic_error(f"rewrite_by_name({name})", exc) from exc
        self._record(
            "session-rewrite-by-name",
            original,
            note=f"{name} ({source.name.lower()})",
            children=[_new_node("goal", rewritten)],
        )
        self.goals[0] = rewritten

    def rewrite(self, rule: Rule) -> None:
        """Rewrite the current goal once using ``rule``.

        Note:
            The rule must originate from the theory (definitions, lemmas, or
            installed theories). Arbitrary user-provided rules are not allowed.
            Use rewrite_by_name() to apply named rules from the theory.
        """
        if not self.goals:
            raise ValueError("No goals left.")
        if not self.theory.is_theory_rule(rule):
            raise ValueError(
                "Cannot apply arbitrary rewrite. Use rewrite_by_name() "
                "with a rule from the theory (definitions, lemmas, or installed theories).\n"
                f"{self._format_clause()}"
            )
        original = self.goals[0]
        try:
            rewritten = _check_rewrite_step(original, rule, self.engine)
        except ValueError as exc:
            raise self._tactic_error("rewrite", exc) from exc
        self._record(
            "session-rewrite",
            original,
            note=f"{rule.lhs} -> {rule.rhs}",
            children=[_new_node("goal", rewritten)],
        )
        self.goals[0] = rewritten

    def rewrite_first(self, name: str) -> None:
        """Rewrite the current goal, drilling into subterms, applying at most once.

        Checks induction hypotheses first (e.g., 'IH.0'), then falls back
        to theory rules. Searches recursively into the arguments of function
        applications until the rule matches. Only applies the rewrite once,
        even if it could apply multiple times in different subtrees.

        Args:
            name: The name of the rule to apply (IH name or theory rule name).

        Raises:
            ValueError: If no goals remain or the rule doesn't match.
        """
        if not self.goals:
            raise ValueError("No goals left.")

        if name in self._ih_rules:
            rule = self._ih_rules[name]
            original = self.goals[0]
            try:
                rewritten = _check_rewrite_first_step(original, rule, self.engine)
            except ValueError as exc:
                raise self._tactic_error(f"rewrite_first({name})", exc) from exc
            self._record(
                "session-rewrite-first",
                original,
                note=f"{name} (ih)",
                children=[_new_node("goal", rewritten)],
            )
            self.goals[0] = rewritten
            return

        entry = self.theory.get_named_rule_info(name)
        if entry is None:
            raise ValueError(
                f"Unknown named rule: {name}\n"
                f"available IHs: {self._available_ihs()}\n"
                f"named rules: {self._available_named_rules()}"
            )

        rule, source = entry
        original = self.goals[0]
        user_rule = Rule(rule.lhs, rule.rhs, rule.conditions, skip_decrease_check=True)
        try:
            rewritten = _check_rewrite_first_step(original, user_rule, self.engine)
        except ValueError as exc:
            raise self._tactic_error(f"rewrite_first({name})", exc) from exc
        self._record(
            "session-rewrite-first",
            original,
            note=f"{name} ({source.name.lower()})",
            children=[_new_node("goal", rewritten)],
        )
        self.goals[0] = rewritten

    def rewrite_many(self, name: str) -> None:
        """Rewrite the current goal, applying the rule everywhere in subtrees.

        Checks induction hypotheses first (e.g., 'IH.0'), then falls back
        to theory rules. Recursively drills into all arguments of function
        applications and applies the rule at every matching position until
        no more matches exist.

        Args:
            name: The name of the rule to apply (IH name or theory rule name).

        Raises:
            ValueError: If no goals remain.
        """
        if not self.goals:
            raise ValueError("No goals left.")

        if name in self._ih_rules:
            rule = self._ih_rules[name]
            original = self.goals[0]
            try:
                rewritten = _check_rewrite_many_step(original, rule, self.engine)
            except ValueError as exc:
                raise self._tactic_error(f"rewrite_many({name})", exc) from exc
            self._record(
                "session-rewrite-many",
                original,
                note=f"{name} (ih)",
                children=[_new_node("goal", rewritten)],
            )
            self.goals[0] = rewritten
            return

        entry = self.theory.get_named_rule_info(name)
        if entry is None:
            raise ValueError(
                f"Unknown named rule: {name}\n"
                f"available IHs: {self._available_ihs()}\n"
                f"named rules: {self._available_named_rules()}"
            )

        rule, source = entry
        original = self.goals[0]
        user_rule = Rule(rule.lhs, rule.rhs, rule.conditions, skip_decrease_check=True)
        try:
            rewritten = _check_rewrite_many_step(original, user_rule, self.engine)
        except ValueError as exc:
            raise self._tactic_error(f"rewrite_many({name})", exc) from exc
        self._record(
            "session-rewrite-many",
            original,
            note=f"{name} ({source.name.lower()})",
            children=[_new_node("goal", rewritten)],
        )
        self.goals[0] = rewritten

    def list_rules(
        self,
        pattern: Optional[str] = None,
        rule_class: Optional[RuleClass] = None,
    ) -> Dict[str, Rule]:
        """List named rules from the theory, optionally filtered by pattern.

        Args:
            pattern: Optional glob pattern to filter rule names (e.g., 'add*', '*comm*').
            rule_class: Optional rule class filter.

        Returns:
            Dictionary mapping rule names to their Rule objects.
        """
        named = self.theory.list_named_rule_entries(pattern, rule_class=rule_class)
        return {name: entry.rule for name, entry in named.items()}

    def list_ihs(self) -> Dict[str, Rule]:
        """List induction hypotheses available for the current goal.

        Returns empty dict for base cases or goals without IHs.

        Returns:
            Dictionary mapping IH names (e.g., 'IH.0', 'IH.1') to their Rule objects.
        """
        return dict(self._ih_rules)

    def exact(self) -> None:
        """Discharge the current goal when it is directly solved."""

        if not self.goals:
            raise ValueError("No goals left.")
        original = self.goals[0]
        try:
            solved = _check_exact_step(original, self.engine)
        except ValueError as exc:
            raise self._tactic_error("exact", exc) from exc
        self._record(
            "session-exact", original, solved=True, children=[_new_node("goal", solved)]
        )
        self.goals = self.goals[1:]
        self._sync_ih_rules()

    def register_lemma(
        self, lemma: Lemma, depth: int = 12, induction_depth: int = 2
    ) -> None:
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

    def register_recursive_definition(
        self,
        name: str,
        equations: Tuple[Tuple[Term, Term], ...],
        scope: str = "definitions",
        signature: Optional[SortSignature] = None,
        precedence: Optional[int] = None,
    ) -> None:
        """Register recursive definition equations in the theorem environment."""

        self.theory.register_recursive_definition(
            name,
            equations,
            scope=scope,
            signature=signature,
            precedence=precedence,
        )

    def register_lemma_rewrite(
        self,
        lemma_name: str,
        scope: str = "lemmas",
        orientation: str = "auto",
    ) -> None:
        """Register a lemma as an oriented rewrite rule."""

        self.theory.register_lemma_rewrite(
            lemma_name, scope=scope, orientation=orientation
        )

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

    def describe(self) -> str:
        """Return a human-friendly summary of the session state."""

        return (
            f"goals: {len(self.goals)}\n"
            f"{self._format_clause()}\n"
            f"available IHs: {self._available_ihs()}\n"
            f"named rules: {self._available_named_rules()}"
        )

    def __str__(self) -> str:
        return self.describe()
