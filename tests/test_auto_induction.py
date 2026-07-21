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
    get_induction_scheme,
    install_theory,
    length,
    list_theory,
    make_engine,
    nat_theory,
    prove,
    render_proof_trace,
    reset_var_interner,
)


@pytest.fixture
def auto_env() -> dict:
    """Standard environment for auto-induction tests."""
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    nil = Const("nil")
    zero = Const("0")

    xs = V("xs", "List")
    ys = V("ys", "List")
    zs = V("zs", "List")
    x = V("x", "Nat")
    y = V("y", "Nat")
    n = V("n", "Nat")
    m = V("m", "Nat")

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
        "zs": zs,
        "x": x,
        "y": y,
        "n": n,
        "m": m,
    }


class TestAutoInductionSelection:
    """Tests for automatic induction variable selection."""

    def test_length_append_auto(self, auto_env: dict) -> None:
        """Auto-select should pick xs for length(append(xs, ys)) theorem."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove(goal, engine, depth=14, auto_induction=True)
        assert ok, "Auto induction should succeed for length(append(xs, ys))"

        trace_str = render_proof_trace(ok.trace)
        assert "auto-induction-select" in trace_str
        assert "var=xs" in trace_str
        assert "scheme=list" in trace_str

    def test_append_associativity_auto(self, auto_env: dict) -> None:
        """Auto-select should pick xs for append associativity."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        zs = auto_env["zs"]

        goal = Clause((), eq(append(append(xs, ys), zs), append(xs, append(ys, zs))))

        ok = prove(goal, engine, depth=15, auto_induction=True)
        assert ok, "Auto induction should succeed for append associativity"

        trace_str = render_proof_trace(ok.trace)
        assert "auto-induction-select" in trace_str
        assert "var=xs" in trace_str

    def test_append_nil_auto(self, auto_env: dict) -> None:
        """Auto-select should pick xs for append(xs, nil) = xs."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        nil = auto_env["nil"]

        goal = Clause((), eq(append(xs, nil), xs))

        ok = prove(goal, engine, depth=10, auto_induction=True)
        assert ok, "Auto induction should succeed for append(xs, nil) = xs"

        trace_str = render_proof_trace(ok.trace)
        assert "auto-induction-select" in trace_str
        assert "var=xs" in trace_str

    def test_no_list_vars_falls_back_to_plain(self, auto_env: dict) -> None:
        """When no list variables exist but goal doesn't need induction, should succeed."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        add = auto_env["add"]
        x = auto_env["x"]
        y = auto_env["y"]

        goal = Clause((), eq(add(x, y), add(y, x)))

        ok = prove(goal, engine, depth=5, auto_induction=True)
        assert ok, "Goal that simplifies to true should succeed"
        # Solved by simplification alone, so no induction stage appears.
        assert "auto-induction-select" not in render_proof_trace(ok.trace)

    def test_no_nat_vars_raises_error(self, auto_env: dict) -> None:
        """Auto-induction should raise ValueError when no nat variables exist."""
        reset_var_interner()

        engine = make_engine(rules=builtin_rules())
        install_theory(engine, nat_theory(), activate_scopes=True)

        a = V("a")
        b = V("b")

        goal = Clause((), eq(a, b))

        with pytest.raises(ValueError, match="No suitable induction variable"):
            prove(goal, engine, depth=5, auto_induction=True)

    def test_only_ground_terms_raises_error(self, auto_env: dict) -> None:
        """Auto-induction should raise ValueError when clause has only ground terms."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        zero = auto_env["zero"]

        goal = Clause((), eq(zero, zero))

        with pytest.raises(ValueError, match="No suitable induction variable"):
            prove(goal, engine, depth=5, auto_induction=True)


class TestAutoInductionTrace:
    """Tests for trace output from auto-induction."""

    def test_trace_contains_selection_info(self, auto_env: dict) -> None:
        """Trace should show which variable was auto-selected."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove(goal, engine, depth=14, auto_induction=True)
        assert ok

        trace_str = render_proof_trace(ok.trace)

        assert "auto-induction-select" in trace_str
        assert "auto-selected var=xs" in trace_str or "var=xs" in trace_str
        assert "scheme=list" in trace_str

    def test_trace_hierarchy(self, auto_env: dict) -> None:
        """Trace root is a solved prove node containing an auto-selection node."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove(goal, engine, depth=14, auto_induction=True)
        assert ok
        assert len(ok.trace.roots) == 1

        root = ok.trace.roots[0]
        assert root.kind == "prove"
        assert root.solved is True

        def find(node, kind):
            if kind in node.kind:
                return node
            for child in node.children:
                found = find(child, kind)
                if found is not None:
                    return found
            return None

        assert find(root, "auto-induction-select") is not None


class TestAutoInductionSession:
    """Tests for ProofSession.auto_induct()."""

    def test_session_auto_induct_success(self, auto_env: dict) -> None:
        """Session.auto_induct() should work when variable can be selected."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        session = ProofSession(goal, engine)
        session.auto_induct()

        assert len(session.goals) == 2, "Should have base and step case goals"

        trace_str = render_proof_trace(session.trace)
        assert "session-auto-induct" in trace_str
        assert "auto-selected var=xs" in trace_str

    def test_session_auto_induct_error(self, auto_env: dict) -> None:
        """Session.auto_induct() should raise ValueError when no variable found."""
        reset_var_interner()

        engine = make_engine(rules=builtin_rules())
        install_theory(engine, nat_theory(), activate_scopes=True)

        x = V("x")
        y = V("y")

        goal = Clause((), App("eq", x, y))

        session = ProofSession(goal, engine)

        with pytest.raises(ValueError, match="No suitable induction variable"):
            session.auto_induct()

    def test_session_auto_induct_proof_flow(self, auto_env: dict) -> None:
        """Full proof flow with session.auto_induct()."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        nil = auto_env["nil"]

        goal = Clause((), eq(append(xs, nil), xs))

        session = ProofSession(goal, engine)
        session.auto_induct()

        assert len(session.goals) == 2

        session.simp()
        assert len(session.goals) == 1

        session.simp()
        assert len(session.goals) == 0, "All goals should be solved"


class TestAutoInductionEdgeCases:
    """Edge case tests for auto-induction."""

    def test_multiple_list_vars_picks_best(self, auto_env: dict) -> None:
        """When multiple list vars exist, should pick the best candidate."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(ys), length(xs))))

        ok = prove(goal, engine, depth=15, auto_induction=True)
        assert ok

        trace_str = render_proof_trace(ok.trace)
        assert "var=xs" in trace_str or "var=ys" in trace_str

    def test_variable_in_goal_not_assumptions(self, auto_env: dict) -> None:
        """Variable in goal should be preferred over one only in assumptions."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause(
            ((ys, Const("nil")),),
            eq(length(append(xs, ys)), add(length(xs), length(ys))),
        )

        ok = prove(goal, engine, depth=14, auto_induction=True)
        assert ok

        trace_str = render_proof_trace(ok.trace)
        assert "var=xs" in trace_str, "xs should be preferred (appears in goal)"


class TestAutoInuctionWithScheme:
    """Tests for auto-induction with various schemes."""

    def test_auto_select_list_scheme(self, auto_env: dict) -> None:
        """Auto-selected variable should use correct scheme."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove(goal, engine, depth=14, auto_induction=True)
        assert ok

        list_scheme = get_induction_scheme(engine, "list")
        assert list_scheme is not None

        trace_str = render_proof_trace(ok.trace)
        assert "scheme=list" in trace_str


class TestProveWithAutoInductionVariants:
    """Tests for prove(auto_induction=True) with different parameters."""

    def test_with_induction_depth(self, auto_env: dict) -> None:
        """Should work with custom induction_depth."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove(goal, engine, depth=14, induction_depth=2, auto_induction=True)
        assert ok

    def test_with_generalize_true(self, auto_env: dict) -> None:
        """Should work with generalize=True (default)."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove(goal, engine, depth=14, generalize=True, auto_induction=True)
        assert ok

    def test_with_generalize_false(self, auto_env: dict) -> None:
        """Should work with generalize=False."""
        engine = auto_env["engine"]
        eq = auto_env["eq"]
        length = auto_env["length"]
        append = auto_env["append"]
        xs = auto_env["xs"]
        ys = auto_env["ys"]
        add = auto_env["add"]

        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove(goal, engine, depth=14, generalize=False, auto_induction=True)
        assert ok
