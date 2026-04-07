from __future__ import annotations

import pytest

from fiddlehead.generalize import (
    GeneralizationMap,
    collect_rigid_terms,
    generalize_clause,
    ungeneralize_clause,
    ungeneralize_term,
)
from fiddlehead.prover import (
    Const,
    App,
    Clause,
    V,
    default_engine_config,
    make_engine,
    nat_theory,
    install_theory,
    list_theory,
    reset_var_interner,
)
from fiddlehead.syntax import Fun, Term, Var


@pytest.fixture
def gen_env() -> dict:
    reset_var_interner()
    x = V("x", "Nat")
    y = V("y", "Nat")
    xs = V("xs", "List")
    engine = make_engine([], config=default_engine_config())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)
    return {
        "x": x,
        "y": y,
        "xs": xs,
        "engine": engine,
    }


def test_generalize_compound_term_multiple_occurrences(gen_env) -> None:
    """Generalize a compound term that appears multiple times."""
    engine = gen_env["engine"]
    xs = gen_env["xs"]

    repeated = App("length", xs)
    goal = App("eq", repeated, repeated)
    clause = Clause((), goal)

    result = generalize_clause(clause, engine)
    assert result is not None
    generalized_clause, gen_map = result

    assert len(gen_map.term_to_var) == 1
    assert generalized_clause.goal != goal


def test_generalize_no_rigid_compound_terms(gen_env) -> None:
    """Don't generalize when there are no rigid compound terms."""
    engine = gen_env["engine"]
    x = gen_env["x"]

    goal = App("add", x, x)
    clause = Clause((), goal)

    result = generalize_clause(clause, engine)
    assert result is None


def test_generalize_preserves_sort(gen_env) -> None:
    """Generalization creates variables with correct sort."""
    engine = gen_env["engine"]
    xs = gen_env["xs"]

    repeated = App("length", xs)
    goal = App("eq", repeated, repeated)
    clause = Clause((), goal)

    result = generalize_clause(clause, engine)
    assert result is not None
    generalized_clause, gen_map = result

    term, var = gen_map.term_to_var[0]
    assert var.sort == "Nat"


def test_ungeneralize_term(gen_env) -> None:
    """Ungeneralize correctly recovers original terms."""
    engine = gen_env["engine"]
    xs = gen_env["xs"]

    repeated = App("length", xs)
    goal = App("eq", repeated, repeated)
    clause = Clause((), goal)

    result = generalize_clause(clause, engine)
    assert result is not None
    generalized_clause, gen_map = result

    ungeneralized = ungeneralize_clause(generalized_clause, gen_map)
    assert ungeneralized.goal == goal


def test_generalize_skips_induction_var(gen_env) -> None:
    """Don't generalize terms containing the induction variable."""
    engine = gen_env["engine"]
    x = gen_env["x"]

    goal = App("add", x, Const("0"))
    clause = Clause((), goal)

    result = generalize_clause(clause, engine, induction_var=x)
    assert result is None


def test_generalize_skips_base_constructors(gen_env) -> None:
    """Don't generalize base constructors like 0, nil, true, false."""
    engine = gen_env["engine"]

    goal = App("eq", Const("0"), Const("0"))
    clause = Clause((), goal)

    result = generalize_clause(clause, engine)
    assert result is None


def test_collect_rigid_terms_compound_multiple(gen_env) -> None:
    """Collect compound terms appearing multiple times."""
    engine = gen_env["engine"]
    xs = gen_env["xs"]

    repeated = App("length", xs)
    goal = App("eq", repeated, repeated)
    clause = Clause((), goal)

    rigid: set = set()
    collect_rigid_terms(clause, engine, rigid)

    assert repeated in rigid


def test_collect_rigid_terms_skips_base_constructors(gen_env) -> None:
    """Don't collect base constructors as rigid."""
    engine = gen_env["engine"]

    goal = App("eq", Const("0"), Const("0"))
    clause = Clause((), goal)

    rigid: set = set()
    collect_rigid_terms(clause, engine, rigid)

    assert Const("0") not in rigid


def test_collect_rigid_terms_skips_induction_var(gen_env) -> None:
    """Don't collect terms containing the induction variable."""
    engine = gen_env["engine"]
    x = gen_env["x"]

    goal = App("add", x, Const("0"))
    clause = Clause((), goal)

    rigid: set = set()
    collect_rigid_terms(clause, engine, rigid, induction_var=x)

    assert App("add", x, Const("0")) not in rigid
    assert Const("0") not in rigid


def test_generalize_adds_equality_assumption(gen_env) -> None:
    """Generalization adds equality assumptions for recovery."""
    engine = gen_env["engine"]
    xs = gen_env["xs"]

    repeated = App("length", xs)
    goal = App("eq", repeated, repeated)
    clause = Clause((), goal)

    result = generalize_clause(clause, engine)
    assert result is not None
    generalized_clause, gen_map = result

    assert len(generalized_clause.assumptions) == 1
    lhs, rhs = generalized_clause.assumptions[0]
    assert isinstance(lhs, Var)
    assert rhs == repeated
