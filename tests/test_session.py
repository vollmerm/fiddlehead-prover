from __future__ import annotations

import pytest

from fiddlehead.prover import (
    App,
    Clause,
    Const,
    ProofSession,
    Rule,
    S,
    V,
    add,
    append,
    builtin_rules,
    cons,
    default_engine_config,
    default_sort_signatures,
    eq,
    get_theorem_environment,
    install_theory,
    length,
    list_theory,
    make_engine,
    nat_theory,
    render_proof_trace,
    render_waterfall_trace,
    reset_var_interner,
)


@pytest.fixture
def session_env() -> dict:
    """Standard environment for session tests."""
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    nil = Const("nil")
    zero = Const("0")

    xs = V("xs", "List")
    ys = V("ys", "List")
    x = V("x", "Nat")
    y = V("y", "Nat")

    return {
        "engine": engine,
        "eq": eq,
        "add": add,
        "append": append,
        "length": length,
        "nil": nil,
        "cons": cons,
        "S": S,
        "zero": zero,
        "xs": xs,
        "ys": ys,
        "x": x,
        "y": y,
    }


class TestProofSessionBasics:
    """Tests for basic session functionality."""

    def test_current_goal(self, session_env: dict) -> None:
        """Should return current goal or None when no goals."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]
        y = session_env["y"]

        goal = Clause((), eq(x, y))
        session = ProofSession(goal, engine)

        assert session.current_goal() is not None
        assert session.current_goal().goal == goal.goal

    def test_current_goal_when_solved(self, session_env: dict) -> None:
        """Should return None when all goals are solved."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        zero = session_env["zero"]

        goal = Clause((), eq(zero, zero))
        session = ProofSession(goal, engine)

        session.exact()
        assert session.current_goal() is None

    def test_assumptions(self, session_env: dict) -> None:
        """Should return assumptions of current goal."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]
        y = session_env["y"]

        assump = (x, Const("0"))
        goal = Clause((assump,), eq(x, y))
        session = ProofSession(goal, engine)

        assert session.assumptions() == (assump,)

    def test_assumptions_when_solved(self, session_env: dict) -> None:
        """Should return empty tuple when no goals."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        zero = session_env["zero"]

        goal = Clause((), eq(zero, zero))
        session = ProofSession(goal, engine)
        session.exact()

        assert session.assumptions() == ()


class TestSessionPrettyPrinting:
    """Tests for REPL-friendly session formatting."""

    def test_describe_includes_goal_context(self, session_env: dict) -> None:
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]
        y = session_env["y"]
        zero = session_env["zero"]

        goal = Clause(((x, zero),), eq(x, y), ((y, zero),))
        session = ProofSession(goal, engine)

        text = session.describe()
        assert "goals: 1" in text
        assert "goal: eq(x, y)" in text
        assert "assumptions:" in text
        assert "0. x = 0" in text
        assert "disequalities:" in text
        assert "0. y != 0" in text
        assert "named rules:" in text

    def test_format_rules_and_ihs(self, session_env: dict) -> None:
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        rules = session.format_rules("*core.nat*")
        assert "theory.core.nat" in rules
        assert "->" in rules
        assert session.format_ihs() == "<no induction hypotheses>"


class TestSessionKeepAssumptions:
    """Tests for session.keep_assumptions()."""

    def test_keep_selected_assumptions(self, session_env: dict) -> None:
        """Should keep only the specified assumptions."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]
        y = session_env["y"]
        zero = session_env["zero"]

        assump1 = (x, Const("0"))
        assump2 = (y, Const("0"))
        goal = Clause((assump1, assump2), eq(x, y))
        session = ProofSession(goal, engine)

        session.keep_assumptions([1])

        assert len(session.assumptions()) == 1
        assert session.assumptions()[0] == assump2

    def test_keep_assumptions_invalid_index(self, session_env: dict) -> None:
        """Should raise ValueError for invalid assumption index."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]
        y = session_env["y"]
        zero = session_env["zero"]

        assump = (x, Const("0"))
        goal = Clause((assump,), eq(x, y))
        session = ProofSession(goal, engine)

        with pytest.raises(ValueError, match="Assumption index out of range"):
            session.keep_assumptions([5])

    def test_keep_assumptions_empty_list(self, session_env: dict) -> None:
        """Should keep no assumptions when empty list given."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]
        y = session_env["y"]
        zero = session_env["zero"]

        assump = (x, Const("0"))
        goal = Clause((assump,), eq(x, y))
        session = ProofSession(goal, engine)

        session.keep_assumptions([])

        assert len(session.assumptions()) == 0


class TestSessionExact:
    """Tests for session.exact()."""

    def test_exact_discharges_true_goal(self, session_env: dict) -> None:
        """Should discharge goal that simplifies to true."""
        engine = session_env["engine"]
        zero = session_env["zero"]

        goal = Clause((), App("eq", zero, zero))
        session = ProofSession(goal, engine)

        session.exact()

        assert session.current_goal() is None

    def test_exact_fails_for_unsolved_goal(self, session_env: dict) -> None:
        """Should raise error when goal is not solved."""
        engine = session_env["engine"]
        x = session_env["x"]
        y = session_env["y"]

        goal = Clause((), App("eq", x, y))
        session = ProofSession(goal, engine)

        with pytest.raises(ValueError, match="Goal is not solved"):
            session.exact()


class TestSessionSimp:
    """Tests for session.simp()."""

    def test_simp_solves_trivial_goal(self, session_env: dict) -> None:
        """Should simplify and solve trivial goals."""
        engine = session_env["engine"]
        zero = session_env["zero"]

        goal = Clause((), App("eq", zero, zero))
        session = ProofSession(goal, engine)

        session.simp()

        assert session.current_goal() is None

    def test_simp_preserves_goal_when_not_solved(self, session_env: dict) -> None:
        """Should keep goal when simplification doesn't solve it."""
        engine = session_env["engine"]
        x = session_env["x"]
        y = session_env["y"]

        goal = Clause((), App("eq", x, y))
        session = ProofSession(goal, engine)

        session.simp()

        assert session.current_goal() is not None
        assert session.current_goal().goal == goal.goal


class TestSessionSplit:
    """Tests for session.split()."""

    def test_split_if_goal(self, session_env: dict) -> None:
        """Should split if-goals into branches."""
        engine = session_env["engine"]
        x = session_env["x"]
        y = session_env["y"]

        if_term = App("if", App("eq", x, y), Const("true"), Const("false"))
        goal = Clause((), if_term)
        session = ProofSession(goal, engine)

        session.split()

        assert len(session.goals) == 2

    def test_split_non_if_returns_same_goal(self, session_env: dict) -> None:
        """Should return the same goal when splitting non-if."""
        engine = session_env["engine"]
        x = session_env["x"]
        y = session_env["y"]

        goal = Clause((), App("eq", x, y))
        session = ProofSession(goal, engine)

        session.split()

        assert len(session.goals) == 1
        assert session.goals[0].goal == goal.goal


class TestSessionEdgeCases:
    """Edge case tests for session operations."""

    def test_simp_on_empty_goals_raises(self, session_env: dict) -> None:
        """Should raise error when no goals left."""
        engine = session_env["engine"]
        goal = Clause((), App("eq", Const("0"), Const("0")))
        session = ProofSession(goal, engine)
        session.exact()

        with pytest.raises(ValueError, match="No goals left"):
            session.simp()

    def test_split_on_empty_goals_raises(self, session_env: dict) -> None:
        """Should raise error when no goals left."""
        engine = session_env["engine"]
        goal = Clause((), App("eq", Const("0"), Const("0")))
        session = ProofSession(goal, engine)
        session.exact()

        with pytest.raises(ValueError, match="No goals left"):
            session.split()

    def test_induct_on_empty_goals_raises(self, session_env: dict) -> None:
        """Should raise error when no goals left."""
        engine = session_env["engine"]
        goal = Clause((), App("eq", Const("0"), Const("0")))
        session = ProofSession(goal, engine)
        session.exact()

        x = V("x", "Nat")
        with pytest.raises(ValueError, match="No goals left"):
            session.induct(x)

    def test_rewrite_on_empty_goals_raises(self, session_env: dict) -> None:
        """Should raise error when no goals left."""
        engine = session_env["engine"]
        goal = Clause((), App("eq", Const("0"), Const("0")))
        session = ProofSession(goal, engine)
        session.exact()

        rule = Rule(Const("0"), Const("1"))
        with pytest.raises(ValueError, match="No goals left"):
            session.rewrite(rule)

    def test_exact_on_empty_goals_raises(self, session_env: dict) -> None:
        """Should raise error when no goals left."""
        engine = session_env["engine"]
        goal = Clause((), App("eq", Const("0"), Const("0")))
        session = ProofSession(goal, engine)
        session.exact()

        with pytest.raises(ValueError, match="No goals left"):
            session.exact()

    def test_exact_error_includes_goal_context(self, session_env: dict) -> None:
        """Should include the active goal in exact() failures."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]
        y = session_env["y"]

        goal = Clause((), eq(x, y))
        session = ProofSession(goal, engine)

        with pytest.raises(ValueError) as excinfo:
            session.exact()

        message = str(excinfo.value)
        assert "exact failed" in message
        assert "goal: eq(x, y)" in message
        assert "available IHs:" in message


class TestNamedRewrites:
    """Tests for session.rewrite_by_name() and session.list_rules()."""

    def test_list_rules_returns_theory_rules(self, session_env: dict) -> None:
        """Should return named rules from installed theories."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        rules = session.list_rules()
        assert len(rules) > 0
        assert any("theory.core.nat" in name for name in rules.keys())

    def test_list_rules_with_pattern_filter(self, session_env: dict) -> None:
        """Should filter rules by glob pattern."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        nat_rules = session.list_rules(pattern="*core.nat*")
        assert all("core.nat" in name for name in nat_rules.keys())

        list_rules = session.list_rules(pattern="*core.list*")
        assert all("core.list" in name for name in list_rules.keys())

    def test_list_rules_with_no_matches(self, session_env: dict) -> None:
        """Should return empty dict when pattern matches nothing."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        rules = session.list_rules(pattern="*nonexistent*")
        assert len(rules) == 0

    def test_rewrite_by_name_unknown_rule_raises(self, session_env: dict) -> None:
        """Should raise error for unknown rule names."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        with pytest.raises(ValueError, match="Unknown named rule"):
            session.rewrite_by_name("nonexistent-rule")

    def test_rewrite_rejects_arbitrary_rules(self, session_env: dict) -> None:
        """Should reject non-theory rules passed to rewrite()."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        arbitrary_rule = Rule(Const("0"), Const("1"))
        with pytest.raises(ValueError, match="Cannot apply arbitrary rewrite"):
            session.rewrite(arbitrary_rule)

    def test_get_named_rule_info(self, session_env: dict) -> None:
        """Should return rule with source info from theory."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        rules = session.list_rules()
        assert len(rules) > 0

        first_rule_name = next(iter(rules.keys()))
        rule, source = session.theory.get_named_rule_info(first_rule_name)
        assert rule is not None
        assert source.name == "THEORY"

    def test_named_rules_include_theory_rules(self, session_env: dict) -> None:
        """Named rules should include rules from installed theories."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        named_info = session.theory.list_named_rules()
        assert len(named_info) > 0

        for name, (rule, source) in named_info.items():
            assert rule is not None
            assert source.name in ("THEORY", "DEFINITION", "LEMMA")

    def test_rewrite_first_unknown_rule_raises(self, session_env: dict) -> None:
        """Should raise error for unknown rule names in rewrite_first."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        with pytest.raises(ValueError, match="Unknown named rule"):
            session.rewrite_first("nonexistent-rule")

    def test_rewrite_many_unknown_rule_raises(self, session_env: dict) -> None:
        """Should raise error for unknown rule names in rewrite_many."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        with pytest.raises(ValueError, match="Unknown named rule"):
            session.rewrite_many("nonexistent-rule")


class TestInductionHypotheses:
    """Tests for session.list_ihs() and IH-based rewrites."""

    def test_list_ihs_empty_before_induction(self, session_env: dict) -> None:
        """Should return empty dict before induction."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        x = session_env["x"]

        goal = Clause((), eq(x, x))
        session = ProofSession(goal, engine)

        assert session.list_ihs() == {}

    def test_list_ihs_empty_in_base_case(self, session_env: dict) -> None:
        """Should return empty dict in base case after induction on lists."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        append = session_env["append"]
        nil = session_env["nil"]
        xs = session_env["xs"]

        goal = Clause((), eq(append(xs, nil), xs))
        session = ProofSession(goal, engine)
        session.induct(xs)

        assert session.current_goal() is not None
        assert session.list_ihs() == {}

    def test_list_ihs_available_in_step_case(self, session_env: dict) -> None:
        """Should return IHs in step case after induction on lists."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        append = session_env["append"]
        nil = session_env["nil"]
        xs = session_env["xs"]

        goal = Clause((), eq(append(xs, nil), xs))
        session = ProofSession(goal, engine)
        session.induct(xs)

        session.exact()

        assert session.current_goal() is not None
        ihs = session.list_ihs()
        assert len(ihs) > 0
        assert "IH.0" in ihs

    def test_rewrite_by_ih_name(self, session_env: dict) -> None:
        """Should apply IH by name using rewrite_first (IHs need subterm drilling)."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        append = session_env["append"]
        nil = session_env["nil"]
        xs = session_env["xs"]

        goal = Clause((), eq(append(xs, nil), xs))
        session = ProofSession(goal, engine)
        session.induct(xs)

        session.exact()

        ihs = session.list_ihs()
        assert "IH.0" in ihs

        session.rewrite_first("IH.0")
        assert session.current_goal() is not None

    def test_unknown_ih_raises(self, session_env: dict) -> None:
        """Should raise error for unknown IH name."""
        engine = session_env["engine"]
        eq = session_env["eq"]
        xs = session_env["xs"]

        goal = Clause((), eq(xs, xs))
        session = ProofSession(goal, engine)
        session.induct(xs)
        session.exact()

        with pytest.raises(ValueError, match="Unknown named rule"):
            session.rewrite_by_name("IH.99")
