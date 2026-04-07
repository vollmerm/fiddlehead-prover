from __future__ import annotations

import pytest

from fiddlehead.prover import (
    App,
    Clause,
    Const,
    ProofSession,
    Rule,
    V,
    builtin_rules,
    default_engine_config,
    default_sort_signatures,
    get_theorem_environment,
    install_theory,
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

    eq = lambda a, b: App("eq", a, b)
    add = lambda a, b: App("add", a, b)
    append = lambda a, b: App("append", a, b)
    length = lambda t: App("length", t)
    nil = Const("nil")
    cons = lambda a, b: App("cons", a, b)
    S = lambda t: App("S", t)
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
