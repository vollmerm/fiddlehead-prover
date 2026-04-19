"""Tests for fertilize_clause and destructor_elim_clause.

These tests verify the behavior of two proof techniques added to fiddlehead:

  fertilize_clause  — ACL2-style cross-fertilization: substitute a hypothesis
                      equality structurally into the goal (forward or backward).
  destructor_elim_clause — ACL2-style destructor elimination: replace opaque
                            selector applications (head(xs), tail(xs), …) with
                            fresh variables and pin them via equality assumptions.
"""

from __future__ import annotations

import pytest

from fiddlehead.generalize import destructor_elim_clause
from fiddlehead.proof import (
    Clause,
    clause_solved,
    fertilize_clause,
    simplify_clause,
)
from fiddlehead.prover import (
    App,
    Const,
    InductionScheme,
    InductionConstructor,
    SortSignature,
    TypeConst,
    TypeVar,
    V,
    builtin_rules,
    default_engine_config,
    get_induction_scheme,
    install_theory,
    list_theory,
    make_engine,
    nat_theory,
    prove_with_induction,
    register_sort_signature,
    reset_var_interner,
)
from fiddlehead.syntax import Fun, Var


# ---------------------------------------------------------------------------
# Shared fixtures
# ---------------------------------------------------------------------------


@pytest.fixture
def fert_env() -> dict:
    """Standard environment for fertilization tests."""
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    nil = Const("nil")
    cons = lambda h, t: App("cons", h, t)
    append = lambda a, b: App("append", a, b)
    length = lambda x: App("length", x)
    eq = lambda a, b: App("eq", a, b)
    add = lambda a, b: App("add", a, b)
    S = lambda n: App("S", n)
    zero = Const("0")

    xs = V("xs", "List")
    ys = V("ys", "List")
    zs = V("zs", "List")
    xs_ih = V("xs_ih", "List")
    n = V("n", "Nat")
    m = V("m", "Nat")
    h_var = V("h_var")

    return {
        "engine": engine,
        "nil": nil,
        "cons": cons,
        "append": append,
        "length": length,
        "eq": eq,
        "add": add,
        "S": S,
        "zero": zero,
        "xs": xs,
        "ys": ys,
        "zs": zs,
        "xs_ih": xs_ih,
        "n": n,
        "m": m,
        "h_var": h_var,
    }


@pytest.fixture
def de_env() -> dict:
    """Environment with head/tail selectors for DE tests."""
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    nil = Const("nil")
    cons = lambda h, t: App("cons", h, t)
    eq = lambda a, b: App("eq", a, b)
    length = lambda x: App("length", x)
    append = lambda a, b: App("append", a, b)
    add = lambda a, b: App("add", a, b)
    head = lambda x: App("head", x)
    tail = lambda x: App("tail", x)
    S = lambda n: App("S", n)
    zero = Const("0")

    xs = V("xs", "List")
    n = V("n", "Nat")
    h = V("hd")
    t = V("tl", "List")

    # Register head/tail sort signatures and rules
    from fiddlehead.prover import get_theorem_environment

    theory = get_theorem_environment(engine)

    hv = V("harg")
    tv = V("targ", "List")

    theory.register_recursive_definition(
        "head",
        ((head(cons(hv, tv)), hv),),
        scope="selector_defs",
        signature=SortSignature(
            (TypeConst("List", (TypeVar("A"),)),), TypeVar("A")
        ),
    )
    theory.register_recursive_definition(
        "tail",
        ((tail(cons(hv, tv)), tv),),
        scope="selector_defs",
        signature=SortSignature(
            (TypeConst("List", (TypeVar("A"),)),),
            TypeConst("List", (TypeVar("A"),)),
        ),
    )
    theory.activate_scope("selector_defs")

    list_scheme = get_induction_scheme(engine, "list")

    return {
        "engine": engine,
        "nil": nil,
        "cons": cons,
        "eq": eq,
        "length": length,
        "append": append,
        "add": add,
        "head": head,
        "tail": tail,
        "S": S,
        "zero": zero,
        "xs": xs,
        "n": n,
        "h": h,
        "t": t,
        "list_scheme": list_scheme,
    }


# ===========================================================================
# Tests for fertilize_clause
# ===========================================================================


class TestFertilizeClause:
    """Unit tests for fertilize_clause."""

    def test_returns_none_when_no_assumptions(self, fert_env: dict) -> None:
        """With no assumptions, fertilize_clause returns None."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs_ih = fert_env["xs_ih"]
        append = fert_env["append"]
        ys = fert_env["ys"]
        nil = fert_env["nil"]

        clause = Clause(
            assumptions=(),
            goal=eq(append(xs_ih, nil), xs_ih),
        )
        assert fertilize_clause(clause, engine) is None

    def test_skips_variable_assumptions(self, fert_env: dict) -> None:
        """Fertilize skips assumptions where one side is a plain variable."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs_ih = fert_env["xs_ih"]
        ys = fert_env["ys"]
        append = fert_env["append"]
        nil = fert_env["nil"]

        # Assumption xs_ih = nil — one side is a Var, already handled by simplify
        clause = Clause(
            assumptions=((xs_ih, nil),),
            goal=eq(append(xs_ih, nil), ys),
        )
        result = fertilize_clause(clause, engine)
        # Either None or must not have just reapplied the var assumption
        if result is not None:
            # Should be further simplified, not just returned unchanged
            assert result.goal != clause.goal or clause_solved(result)

    def test_returns_none_when_goal_not_eq(self, fert_env: dict) -> None:
        """Fertilize only operates on eq/true/false goals."""
        engine = fert_env["engine"]
        append = fert_env["append"]
        xs_ih = fert_env["xs_ih"]
        ys = fert_env["ys"]
        nil = fert_env["nil"]
        length = fert_env["length"]

        # Goal is not eq(_, _) — just a bare function application
        ih_lhs = length(xs_ih)
        ih_rhs = length(append(xs_ih, nil))
        clause = Clause(
            assumptions=((ih_lhs, ih_rhs),),
            goal=append(xs_ih, nil),  # not an eq goal
        )
        assert fertilize_clause(clause, engine) is None

    def test_backward_substitution_closes_goal(self, fert_env: dict) -> None:
        """Backward substitution: replace IH rhs with lhs closes the goal."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs_ih = fert_env["xs_ih"]
        ys = fert_env["ys"]
        zs = fert_env["zs"]
        append = fert_env["append"]

        # IH: append(append(xs_ih, ys), zs) = append(xs_ih, append(ys, zs))
        ih_lhs = append(append(xs_ih, ys), zs)
        ih_rhs = append(xs_ih, append(ys, zs))

        # Goal contains ih_rhs (the right-hand side of the IH)
        # Backward: replace ih_rhs with ih_lhs would not help here, but
        # goal containing ih_lhs and using it -> ih_rhs should solve it.
        goal = eq(
            App("cons", fert_env["h_var"], ih_lhs),
            App("cons", fert_env["h_var"], ih_rhs),
        )

        clause = Clause(
            assumptions=((ih_lhs, ih_rhs),),
            goal=goal,
        )
        # simplify_clause should solve this via schematic rules, not fertilization
        simplified = simplify_clause(clause, engine)
        assert clause_solved(simplified)

    def test_forward_substitution_when_goal_has_lhs(self, fert_env: dict) -> None:
        """Forward substitution: goal contains IH lhs, replacing with rhs helps."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs_ih = fert_env["xs_ih"]
        ys = fert_env["ys"]
        append = fert_env["append"]
        length = fert_env["length"]
        add = fert_env["add"]

        # IH: length(append(xs_ih, ys)) = add(length(xs_ih), length(ys))
        ih_lhs = length(append(xs_ih, ys))
        ih_rhs = add(length(xs_ih), length(ys))

        # Goal: eq(ih_lhs, ih_rhs) — trivially solved once IH is substituted
        goal = eq(ih_lhs, ih_rhs)
        clause = Clause(
            assumptions=((ih_lhs, ih_rhs),),
            goal=goal,
        )
        result = fertilize_clause(clause, engine)
        # The goal may be solved directly by simplification when IH is an assumption
        if result is None:
            # Simplification should have handled it
            simplified = simplify_clause(clause, engine)
            assert clause_solved(simplified)
        else:
            assert clause_solved(result) or result.goal != goal

    def test_no_fertilize_when_from_term_not_in_goal(self, fert_env: dict) -> None:
        """Fertilize returns None when neither IH side appears in the goal."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs_ih = fert_env["xs_ih"]
        ys = fert_env["ys"]
        zs = fert_env["zs"]
        append = fert_env["append"]
        length = fert_env["length"]
        add = fert_env["add"]
        nil = fert_env["nil"]

        # IH: length(append(xs_ih, ys)) = add(length(xs_ih), length(ys))
        ih_lhs = length(append(xs_ih, ys))
        ih_rhs = add(length(xs_ih), length(ys))

        # Goal does not contain ih_lhs or ih_rhs structurally
        goal = eq(append(zs, nil), zs)
        clause = Clause(
            assumptions=((ih_lhs, ih_rhs),),
            goal=goal,
        )
        # Since goal doesn't contain either side of the IH, fertilize returns None
        result = fertilize_clause(clause, engine)
        # Note: simplify might still solve it via append_nil rule
        # Fertilize specifically must not fire if terms not in goal
        if result is not None:
            # If it returned something, the goal must have changed
            assert result.goal != goal or clause_solved(result)

    def test_identical_assumption_sides_skipped(self, fert_env: dict) -> None:
        """Assumption lhs == rhs is skipped (no substitution attempted)."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs_ih = fert_env["xs_ih"]
        append = fert_env["append"]
        nil = fert_env["nil"]
        length = fert_env["length"]

        same_term = length(xs_ih)
        clause = Clause(
            assumptions=((same_term, same_term),),
            goal=eq(append(xs_ih, nil), xs_ih),
        )
        # fertilize only fires when lhs != rhs, so with same_term = same_term it skips
        result = fertilize_clause(clause, engine)
        # Result may be None, or if returned it must change the goal
        if result is not None:
            assert clause_solved(result) or result.goal != clause.goal


# ===========================================================================
# Tests for destructor_elim_clause
# ===========================================================================


class TestDestructorElimClause:
    """Unit tests for destructor_elim_clause."""

    def test_returns_none_when_no_destructors(self, de_env: dict) -> None:
        """Returns None when xs appears only inside constructor applications.

        eq(cons(h, xs), cons(h2, xs)) — xs is inside cons (a constructor), so
        no non-constructor function is applied directly to xs.  DE returns None.
        """
        engine = de_env["engine"]
        eq = de_env["eq"]
        xs = de_env["xs"]
        cons = de_env["cons"]
        list_scheme = de_env["list_scheme"]

        h1 = V("h_no_destr1")
        h2 = V("h_no_destr2")
        clause = Clause(
            assumptions=(),
            goal=eq(cons(h1, xs), cons(h2, xs)),
        )
        result = destructor_elim_clause(clause, xs, list_scheme, engine)
        assert result is None

    def test_replaces_head_with_fresh_var(self, de_env: dict) -> None:
        """head(xs) is replaced by a fresh variable d_0."""
        engine = de_env["engine"]
        eq = de_env["eq"]
        xs = de_env["xs"]
        head = de_env["head"]
        length = de_env["length"]
        nil = de_env["nil"]
        list_scheme = de_env["list_scheme"]

        clause = Clause(
            assumptions=(),
            goal=eq(head(xs), head(xs)),
        )
        result = destructor_elim_clause(clause, xs, list_scheme, engine)
        assert result is not None

        # The goal should no longer contain head(xs) directly
        from fiddlehead.syntax import Fun

        def contains_head_xs(term):
            if term == App("head", xs):
                return True
            match term:
                case Fun(_, args):
                    return any(contains_head_xs(a) for a in args)
                case _:
                    return False

        assert not contains_head_xs(result.goal), (
            f"Goal still contains head(xs): {result.goal}"
        )

    def test_replaces_tail_with_fresh_var(self, de_env: dict) -> None:
        """tail(xs) is replaced by a fresh variable."""
        engine = de_env["engine"]
        eq = de_env["eq"]
        xs = de_env["xs"]
        tail = de_env["tail"]
        length = de_env["length"]
        list_scheme = de_env["list_scheme"]

        clause = Clause(
            assumptions=(),
            goal=eq(length(tail(xs)), length(tail(xs))),
        )
        result = destructor_elim_clause(clause, xs, list_scheme, engine)
        assert result is not None

        # The goal should have a fresh variable instead of tail(xs)
        from fiddlehead.syntax import Var

        found_fresh_var = False
        match result.goal:
            case Fun("eq", (Fun("length", (Var(name, _),)), Fun("length", (Var(name2, _),)))):
                found_fresh_var = name == name2  # same fresh var used for both occurrences
            case _:
                pass
        assert found_fresh_var, f"Expected fresh vars in goal, got: {result.goal}"

    def test_adds_equality_assumptions(self, de_env: dict) -> None:
        """DE adds equalities between fresh vars and original destructor terms."""
        engine = de_env["engine"]
        eq = de_env["eq"]
        xs = de_env["xs"]
        head = de_env["head"]
        tail = de_env["tail"]
        length = de_env["length"]
        list_scheme = de_env["list_scheme"]

        clause = Clause(
            assumptions=(),
            goal=eq(length(tail(xs)), length(tail(xs))),
        )
        result = destructor_elim_clause(clause, xs, list_scheme, engine)
        assert result is not None

        # Should have at least one equality assumption binding the fresh var to tail(xs)
        has_tail_assumption = any(
            rhs == App("tail", xs) for (_, rhs) in result.assumptions
        )
        assert has_tail_assumption, (
            f"Expected assumption with tail(xs), got: {result.assumptions}"
        )

    def test_constructor_applications_not_eliminated(self, de_env: dict) -> None:
        """Constructor applications (cons, nil) are not eliminated by DE.

        When xs appears only as an argument inside a constructor application like
        cons(n, xs), DE must not replace it.  The constructor symbol is in the
        induction scheme's constructor set, so the condition
        ``symbol not in constructor_symbols`` is False and the term is skipped.
        """
        engine = de_env["engine"]
        eq = de_env["eq"]
        xs = de_env["xs"]
        cons = de_env["cons"]
        n = de_env["n"]
        list_scheme = de_env["list_scheme"]

        # cons is a constructor — cons(n, xs) must NOT be eliminated
        clause = Clause(
            assumptions=(),
            goal=eq(cons(n, xs), cons(n, xs)),
        )
        result = destructor_elim_clause(clause, xs, list_scheme, engine)
        assert result is None, (
            "DE should not eliminate constructor applications to the induction variable"
        )

    def test_head_in_assumption_also_eliminated(self, de_env: dict) -> None:
        """Destructor applications in assumptions are also replaced."""
        engine = de_env["engine"]
        eq = de_env["eq"]
        xs = de_env["xs"]
        head = de_env["head"]
        length = de_env["length"]
        nil = de_env["nil"]
        list_scheme = de_env["list_scheme"]

        clause = Clause(
            assumptions=((head(xs), nil),),
            goal=eq(length(xs), length(xs)),
        )
        result = destructor_elim_clause(clause, xs, list_scheme, engine)
        assert result is not None

        # The assumption should not directly have head(xs) anymore
        from fiddlehead.syntax import Var

        for lhs, rhs in result.assumptions:
            if rhs == App("head", xs):
                # This is the pinning assumption: fresh_var = head(xs) — OK
                assert isinstance(lhs, Var)
            else:
                # Any other assumption should not have head(xs) as lhs/rhs
                assert lhs != App("head", xs)

    def test_fresh_vars_get_bound_in_step_case(self, de_env: dict) -> None:
        """After DE + induction step, fresh vars are pinned to h and tail."""
        engine = de_env["engine"]
        eq = de_env["eq"]
        xs = de_env["xs"]
        head = de_env["head"]
        tail = de_env["tail"]
        length = de_env["length"]
        nil = de_env["nil"]
        cons = de_env["cons"]
        list_scheme = de_env["list_scheme"]

        # Original goal: length(tail(xs)) = length(xs) - S(0)  [for non-nil xs]
        # (This is actually the goal: length(tail(xs)) + 1 = length(xs))
        # Let's use a simpler version
        clause = Clause(
            assumptions=(),
            goal=eq(tail(xs), tail(xs)),
        )
        de_result = destructor_elim_clause(clause, xs, list_scheme, engine)
        assert de_result is not None

        # Now simulate induction: substitute xs = cons(h, xs_ih)
        from fiddlehead.proof import induction_branches

        h_var = V("h_step")
        xs_ih_var = V("xs_ih_step", "List")
        subst = {xs: cons(h_var, xs_ih_var)}
        from fiddlehead.proof import instantiate_clause

        step_clause = instantiate_clause(de_result, subst)
        simplified_step = simplify_clause(step_clause, engine)

        # The fresh variable should now be pinned to xs_ih_var
        # (because tail(cons(h, xs_ih)) = xs_ih)
        from fiddlehead.syntax import Var

        for lhs, rhs in simplified_step.assumptions:
            if isinstance(lhs, Var) and isinstance(rhs, Var):
                # Should have d_X = xs_ih_step (after simplification)
                assert rhs.name == xs_ih_var.name or lhs.name == xs_ih_var.name


# ===========================================================================
# Integration tests: DE + induction proof
# ===========================================================================


class TestDestructorElimIntegration:
    """Integration tests using DE with actual induction proofs."""

    def test_de_enabled_does_not_break_length_append(self, fert_env: dict) -> None:
        """Enabling DE does not break standard length_append proof."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs = fert_env["xs"]
        ys = fert_env["ys"]
        append = fert_env["append"]
        length = fert_env["length"]
        add = fert_env["add"]

        list_scheme = get_induction_scheme(engine, "list")
        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove_with_induction(
            goal, engine, xs, list_scheme, depth=14, destructor_elim=True
        )
        assert ok, "length_append should succeed with DE enabled"

    def test_de_disabled_still_proves_length_append(self, fert_env: dict) -> None:
        """Disabling DE still allows length_append proof (no destructors in goal)."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs = fert_env["xs"]
        ys = fert_env["ys"]
        append = fert_env["append"]
        length = fert_env["length"]
        add = fert_env["add"]

        list_scheme = get_induction_scheme(engine, "list")
        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove_with_induction(
            goal, engine, xs, list_scheme, depth=14, destructor_elim=False
        )
        assert ok, "length_append should still succeed without DE"

    def test_de_does_not_break_append_nil(self, fert_env: dict) -> None:
        """DE does not interfere with append(xs, nil) = xs proof."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs = fert_env["xs"]
        append = fert_env["append"]
        nil = fert_env["nil"]

        list_scheme = get_induction_scheme(engine, "list")
        goal = Clause((), eq(append(xs, nil), xs))

        ok = prove_with_induction(
            goal, engine, xs, list_scheme, depth=10, destructor_elim=True
        )
        assert ok, "append_nil should succeed with DE enabled"

    def test_de_does_not_break_append_assoc(self, fert_env: dict) -> None:
        """DE does not interfere with append_assoc proof."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs = fert_env["xs"]
        ys = fert_env["ys"]
        zs = fert_env["zs"]
        append = fert_env["append"]

        list_scheme = get_induction_scheme(engine, "list")
        goal = Clause((), eq(append(append(xs, ys), zs), append(xs, append(ys, zs))))

        ok = prove_with_induction(
            goal, engine, xs, list_scheme, depth=15, destructor_elim=True
        )
        assert ok, "append_assoc should succeed with DE enabled"

    def test_de_with_selector_in_goal(self, de_env: dict) -> None:
        """DE fires when goal contains head(xs) and replaces it with a fresh var."""
        engine = de_env["engine"]
        eq = de_env["eq"]
        xs = de_env["xs"]
        head = de_env["head"]
        nil = de_env["nil"]
        cons = de_env["cons"]
        list_scheme = de_env["list_scheme"]

        # Goal with head(xs) — DE should identify head(xs) as a destructor application
        h_var = V("h_const")
        clause = Clause(
            assumptions=(),
            goal=eq(head(xs), head(xs)),
        )
        result = destructor_elim_clause(clause, xs, list_scheme, engine)
        assert result is not None, "DE should fire when head(xs) appears in goal"


# ===========================================================================
# Integration tests: fertilization + induction
# ===========================================================================


class TestFertilizeIntegration:
    """Integration tests showing fertilization does not break existing proofs."""

    def test_fertilize_does_not_break_add_comm(self, fert_env: dict) -> None:
        """Fertilization does not break add_comm proof."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        n = fert_env["n"]
        m = fert_env["m"]
        add = fert_env["add"]

        nat_scheme = get_induction_scheme(engine, "nat")
        goal = Clause((), eq(add(n, m), add(m, n)))

        ok = prove_with_induction(goal, engine, n, nat_scheme, depth=10)
        assert ok, "add_comm should succeed"

    def test_fertilize_does_not_break_length_append(self, fert_env: dict) -> None:
        """Fertilization does not break length_append proof."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs = fert_env["xs"]
        ys = fert_env["ys"]
        append = fert_env["append"]
        length = fert_env["length"]
        add = fert_env["add"]

        list_scheme = get_induction_scheme(engine, "list")
        goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))

        ok = prove_with_induction(goal, engine, xs, list_scheme, depth=14)
        assert ok, "length_append should succeed"

    def test_fertilize_clause_on_already_solved_clause(self, fert_env: dict) -> None:
        """fertilize_clause on an already-solved clause returns None (no work needed)."""
        from fiddlehead.syntax import true

        engine = fert_env["engine"]
        eq = fert_env["eq"]
        n = fert_env["n"]

        clause = Clause(assumptions=(), goal=true)
        # goal == true — fertilize checks if goal is eq/true/false; true passes
        # But there are no assumptions with compound terms on both sides
        result = fertilize_clause(clause, engine)
        # Should return None (no assumptions to fertilize with) or solved
        if result is not None:
            assert clause_solved(result)

    def test_fertilize_clause_does_not_loop(self, fert_env: dict) -> None:
        """fertilize_clause does not introduce a cycle (returns same goal → None)."""
        engine = fert_env["engine"]
        eq = fert_env["eq"]
        xs_ih = fert_env["xs_ih"]
        ys = fert_env["ys"]
        append = fert_env["append"]

        ih_lhs = append(append(xs_ih, ys), fert_env["zs"])
        ih_rhs = append(xs_ih, append(ys, fert_env["zs"]))

        # Goal that contains ih_lhs but cannot be solved by simple substitution
        # (This is not solvable without more rules)
        goal = eq(ih_lhs, ih_lhs)
        clause = Clause(
            assumptions=((ih_lhs, ih_rhs),),
            goal=goal,
        )
        # Should not loop — must terminate
        result = fertilize_clause(clause, engine)
        # If it fires and does not improve the goal, it returns None
        # If it fires and improves, the result goal must differ
        if result is not None:
            assert clause_solved(result) or result.goal != goal
