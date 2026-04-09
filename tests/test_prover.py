from __future__ import annotations

import types
from typing import Dict

import pytest

from fiddlehead.prover import *
from fiddlehead.proof import split_clause


@pytest.fixture
def env() -> Dict[str, object]:
    reset_var_interner()
    x = V("x")
    y = V("y")
    z = V("z")
    x_nat = V("xn", "Nat")
    xs = V("xs", "List")

    zero = Const("0")
    one = Const("1")

    S = lambda t: App("S", t)
    mul = lambda a, b: App("mul", a, b)
    add = lambda a, b: App("add", a, b)
    bnot = lambda a: App("not", a)
    band = lambda a, b: App("and", a, b)
    bor = lambda a, b: App("or", a, b)
    nil = Const("nil")
    cons = lambda a, b: App("cons", a, b)
    app = lambda a, b: App("append", a, b)
    length = lambda a: App("length", a)
    eq = lambda a, b: App("eq", a, b)
    neq = lambda a, b: App("neq", a, b)
    f = lambda a: App("f", a)

    r3 = Rule(f(x), one, conditions=((x, zero),))  # type: ignore
    rules = builtin_rules() + [r3]
    shared_cache: Dict[Term, Term] = {}
    shared_schemes: Dict[str, InductionScheme] = {}
    shared_sort_signatures = default_sort_signatures()
    shared_sort_signatures["f"] = SortSignature((TypeConst("Nat"),), TypeConst("Nat"))
    shared_config = default_engine_config()
    engine = make_engine(
        rules=rules,
        config=shared_config,
        ground_cache=shared_cache,
        schemes=shared_schemes,
        sort_signatures=shared_sort_signatures,
    )
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    return {
        "x": x,
        "y": y,
        "z": z,
        "x_nat": x_nat,
        "xs": xs,
        "zero": zero,
        "one": one,
        "S": S,
        "mul": mul,
        "add": add,
        "bnot": bnot,
        "band": band,
        "bor": bor,
        "nil": nil,
        "cons": cons,
        "app": app,
        "length": length,
        "eq": eq,
        "neq": neq,
        "f": f,
        "rules": rules,
        "shared_cache": shared_cache,
        "shared_schemes": shared_schemes,
        "shared_sort_signatures": shared_sort_signatures,
        "shared_config": shared_config,
        "engine": engine,
    }


def test_term_rewriting_basics(env) -> None:  # type: ignore
    add = env["add"]
    S = env["S"]
    zero = env["zero"]
    one = env["one"]
    x = env["x"]
    y = env["y"]
    z = env["z"]
    f = env["f"]
    eq = env["eq"]
    neq = env["neq"]
    engine = env["engine"]

    t = add(S(S(zero)), S(zero))
    res = normalize(t, engine)
    assert str(res) == "S(S(S(0)))"
    assert App("f", x) is App("f", x)
    assert str(apply_subst(add(x, y), {x: zero})) == "add(0, y)"
    m = match(add(x, y), add(zero, S(zero)))
    assert m is not None
    assert m[x] is zero
    assert str(normalize(add(y, add(x, z)), engine)) == "add(x, add(y, z))"
    assert str(normalize(f(zero), engine)) == "1"
    assert str(normalize(f(S(zero)), engine)) == "f(S(0))"
    assert normalize(eq(zero, zero), engine) == true
    assert normalize(neq(zero, zero), engine) == false
    assert one == Const("1")


def test_trace_clause_and_cache_basics(env) -> None:  # type: ignore
    add = env["add"]
    S = env["S"]
    x = env["x"]
    y = env["y"]
    zero = env["zero"]
    eq = env["eq"]
    rules = env["rules"]
    shared_config = env["shared_config"]
    shared_cache = env["shared_cache"]
    shared_schemes = env["shared_schemes"]
    shared_sort_signatures = env["shared_sort_signatures"]
    engine = env["engine"]

    tr = Trace()
    tr_engine = make_engine(
        rules=rules,
        trace=tr,
        config=shared_config,
        ground_cache=shared_cache,
        schemes=shared_schemes,
        sort_signatures=shared_sort_signatures,
    )
    install_theory(tr_engine, nat_theory(), activate_scopes=True)
    normalize(add(S(zero), zero), tr_engine)
    assert len(tr.steps) > 0

    clause = Clause(((x, zero),), add(x, S(zero)))
    simplified = simplify_clause(clause, engine)
    assert str(simplified.goal) == "S(0)"

    clause2 = Clause((), eq(zero, zero))
    assert clause_solved(simplify_clause(clause2, engine))

    t = add(zero, zero)
    r = normalize(t, engine)
    assert t in shared_cache
    assert shared_cache[t] is r
    r1n = normalize(t, engine)
    r2n = normalize(t, engine)
    assert r1n is r2n

    clause3 = Clause(((x, y), (y, zero)), eq(x, zero))
    assert clause_solved(simplify_clause(clause3, engine))


def test_normalize_reaches_fixpoint_across_child_rewrites(env) -> None:  # type: ignore
    add = env["add"]
    S = env["S"]
    zero = env["zero"]
    one = env["one"]
    eq = env["eq"]
    engine = env["engine"]

    term = App("if", eq(add(S(zero), zero), S(zero)), zero, one)
    assert normalize(term, engine) == zero


def test_ground_cache_not_reused_across_contexts() -> None:
    reset_var_interner()
    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)

    zero = Const("0")
    succ = lambda t: App("S", t)
    goal = App("eq", zero, succ(zero))

    contextual = Context(ground_equalities=((zero, succ(zero)),))
    assert engine.normalize_under_context(goal, contextual) == true
    assert goal not in engine.ground_cache
    assert engine.normalize(goal) != true


def test_disequality_simplification_and_split_branch_contexts(env) -> None:  # type: ignore
    x = env["x"]
    y = env["y"]
    eq = env["eq"]
    neq = env["neq"]
    engine = env["engine"]

    diseq_clause = Clause((), neq(x, y), ((x, y),))
    assert simplify_clause(diseq_clause, engine).goal == true
    eq_clause = Clause((), eq(x, y), ((x, y),))
    assert simplify_clause(eq_clause, engine).goal == false

    eq_cond_clause = Clause((), App("if", eq(x, y), true, false))
    eq_branches = split_clause(eq_cond_clause)
    assert len(eq_branches) == 2
    assert eq_branches[0].assumptions == ((x, y),)
    assert eq_branches[0].disequalities == ()
    assert eq_branches[1].assumptions == ()
    assert eq_branches[1].disequalities == ((x, y),)

    cond = neq(x, y)
    bool_cond_clause = Clause((), App("if", cond, x, y))
    bool_branches = split_clause(bool_cond_clause)
    assert len(bool_branches) == 2
    assert bool_branches[0].assumptions == ((cond, true),)
    assert bool_branches[0].disequalities == ()
    assert bool_branches[1].assumptions == ((cond, false),)
    assert bool_branches[1].disequalities == ()


def test_contextual_if_simplification_uses_assumptions(env) -> None:  # type: ignore
    engine = env["engine"]
    x = env["x"]
    zero = env["zero"]

    goal = App("if", App("eq", x, zero), App("eq", x, zero), true)
    clause = Clause(((App("eq", x, zero), true),), goal)

    simplified = simplify_clause(clause, engine)
    assert simplified.goal == true


def test_builtin_rules_do_not_claim_common_variable_names() -> None:
    reset_var_interner()
    builtin_rules()
    x_nat = V("x", "Nat")
    y_list = V("y", "List")
    assert x_nat.sort == "Nat"
    assert y_list.sort == "List"


def test_induction_branches_and_proofs(env) -> None:  # type: ignore
    add = env["add"]
    app = env["app"]
    length = env["length"]
    S = env["S"]
    x = env["x"]
    y = env["y"]
    x_nat = env["x_nat"]
    xs = env["xs"]
    zero = env["zero"]
    one = env["one"]
    nil = env["nil"]
    eq = env["eq"]
    engine = env["engine"]

    nat_scheme = get_induction_scheme(engine, "nat")
    assert nat_scheme is not None
    list_scheme = get_induction_scheme(engine, "list")
    assert list_scheme is not None
    bool_scheme = InductionScheme(
        name="bool", sort="Bool", base_terms=(true, false), constructors=()
    )

    clause4 = Clause((), eq(add(x, zero), x))
    branches = induction_branches(clause4, x, nat_scheme)
    assert len(branches) == 2
    assert str(branches[0].goal) == "eq(add(0, 0), 0)"
    assert str(branches[1].goal) == "eq(add(S(x_ih_0), 0), S(x_ih_0))"
    assert len(branches[1].assumptions) == 1
    ih_l, ih_r = branches[1].assumptions[0]
    assert str(ih_l) == "add(x_ih_0, 0)"
    assert str(ih_r) == "x_ih_0"

    assert prove_with_induction(
        clause4, engine, x, nat_scheme, depth=8, induction_depth=1
    )
    bad = Clause((), eq(add(zero, one), zero))
    assert not prove(bad, engine, depth=8)
    assert not prove_with_induction(
        clause4, engine, xs, nat_scheme, depth=8, induction_depth=1
    )
    assert not induction_branches(clause4, xs, nat_scheme)

    register_induction_scheme(engine, bool_scheme)
    assert get_induction_scheme(engine, "nat") is nat_scheme
    assert get_induction_scheme_for_sort(engine, "List") is list_scheme
    assert prove_with_registered_induction(
        clause4, engine, x_nat, "nat", depth=8, induction_depth=1
    )
    assert not prove_with_registered_induction(
        clause4, engine, x_nat, "list", depth=8, induction_depth=1
    )

    list_goal = Clause((), eq(app(xs, nil), xs))
    list_branches = induction_branches(list_goal, xs, list_scheme)
    assert len(list_branches) == 2
    assert str(list_branches[0].goal) == "eq(append(nil, nil), nil)"
    assert (
        str(list_branches[1].goal)
        == "eq(append(cons(xs_cons_arg_0, xs_ih_0), nil), cons(xs_cons_arg_0, xs_ih_0))"
    )
    assert len(list_branches[1].assumptions) == 1
    ih_l2, ih_r2 = list_branches[1].assumptions[0]
    assert str(ih_l2) == "append(xs_ih_0, nil)"
    assert str(ih_r2) == "xs_ih_0"

    assert prove_with_induction(
        list_goal, engine, xs, list_scheme, depth=10, induction_depth=1
    )
    ys = V("ys", "List")
    zs = V("zs", "List")
    assoc_goal = Clause((), eq(app(app(xs, ys), zs), app(xs, app(ys, zs))))
    assert prove_with_induction(
        assoc_goal, engine, xs, list_scheme, depth=12, induction_depth=1
    )
    len_append_nil_goal = Clause((), eq(length(app(xs, nil)), length(xs)))
    assert prove_with_induction(
        len_append_nil_goal, engine, xs, list_scheme, depth=12, induction_depth=1
    )
    len_append_goal = Clause((), eq(length(app(xs, ys)), add(length(xs), length(ys))))
    assert prove_with_induction(
        len_append_goal, engine, xs, list_scheme, depth=14, induction_depth=1
    )


def test_inductive_repeat_skip_exec_proves() -> None:
    reset_var_interner()
    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, map_theory(), activate_scopes=True)

    k = TypeVar("K")
    v = TypeVar("V")
    engine.sort_arities["Com"] = 0
    skip = Const("skip")
    s = V("s", "Map")
    n = V("n", "Nat")
    repeat_skip = lambda count: App("repeat_skip", count)
    seq = lambda first, second: App("seq", first, second)
    exec_cmd = lambda cmd, state: App("exec", cmd, state)
    eq = lambda a, b: App("eq", a, b)

    register_sort_signature(engine, "skip", SortSignature((), TypeConst("Com")))
    register_sort_signature(
        engine, "seq", SortSignature((TypeConst("Com"), TypeConst("Com")), TypeConst("Com"))
    )
    register_sort_signature(
        engine,
        "exec",
        SortSignature(
            (TypeConst("Com"), TypeConst("Map", (k, v))),
            TypeConst("Map", (k, v)),
        ),
    )
    register_sort_signature(
        engine, "repeat_skip", SortSignature((TypeConst("Nat"),), TypeConst("Com"))
    )

    env_theory = get_theorem_environment(engine)
    n_rep = V("n_rep", "Nat")
    env_theory.register_definition(
        "repeat_skip_zero", repeat_skip(Const("0")), skip, scope="imp_def"
    )
    register_recursive_definition(
        engine,
        "repeat_skip",
        (
            (
                repeat_skip(App("S", n_rep)),
                seq(skip, repeat_skip(n_rep)),
            ),
        ),
        signature=SortSignature((TypeConst("Nat"),), TypeConst("Com")),
        scope="imp_def",
    )
    c1 = V("c1", "Com")
    c2 = V("c2", "Com")
    s_exec = V("s_exec", "Map")
    env_theory.register_rule(
        Rule(exec_cmd(skip, s_exec), s_exec), "imp_def", name="exec_skip"
    )
    env_theory.register_rule(
        Rule(exec_cmd(seq(c1, c2), s_exec), exec_cmd(c2, exec_cmd(c1, s_exec))),
        "imp_def",
        name="exec_seq",
    )
    env_theory.activate_scope("imp_def")

    goal = Clause((), eq(exec_cmd(repeat_skip(n), s), s), ())

    nat_scheme = get_induction_scheme(engine, "nat")
    assert nat_scheme is not None
    assert prove_with_induction(
        goal,
        engine,
        n,
        nat_scheme,
        depth=20,
        induction_depth=2,
        generalize=False,
    )


def test_cache_and_config_isolation(env) -> None:  # type: ignore
    add = env["add"]
    x = env["x"]
    y = env["y"]
    z = env["z"]
    shared_config = env["shared_config"]
    shared_cache = env["shared_cache"]
    shared_schemes = env["shared_schemes"]
    shared_sort_signatures = env["shared_sort_signatures"]
    rules = env["rules"]
    zero = env["zero"]
    engine = env["engine"]

    term_shared = add(zero, zero)
    a = make_engine(
        rules=rules,
        config=shared_config,
        ground_cache=shared_cache,
        schemes=shared_schemes,
        sort_signatures=shared_sort_signatures,
    )
    b = make_engine(
        rules=rules,
        config=shared_config,
        ground_cache=shared_cache,
        schemes=shared_schemes,
        sort_signatures=shared_sort_signatures,
    )
    normalize(term_shared, a)
    assert term_shared in shared_cache
    assert normalize(term_shared, b) is shared_cache[term_shared]

    iso_a_cache: Dict[Term, Term] = {}
    iso_b_cache: Dict[Term, Term] = {}
    iso_a = make_engine(
        rules=rules,
        config=shared_config,
        ground_cache=iso_a_cache,
        schemes=shared_schemes,
        sort_signatures=shared_sort_signatures,
    )
    iso_b = make_engine(
        rules=rules,
        config=shared_config,
        ground_cache=iso_b_cache,
        schemes=shared_schemes,
        sort_signatures=shared_sort_signatures,
    )
    normalize(term_shared, iso_a)
    assert term_shared in iso_a_cache
    assert term_shared not in iso_b_cache

    no_ac_config = EngineConfig(
        precedence=shared_config.precedence, assoc=set(), comm=set()
    )
    no_ac_engine = make_engine(
        rules=rules,
        config=no_ac_config,
        ground_cache={},
        schemes={},
        sort_signatures=shared_sort_signatures,
    )
    assert str(normalize(add(y, add(x, z)), no_ac_engine)) == "add(y, add(x, z))"
    assert str(normalize(add(y, add(x, z)), engine)) == "add(x, add(y, z))"


def test_variable_interning_and_sort_conflicts() -> None:
    reset_var_interner()
    vx1 = V("vx")
    vx2 = V("vx")
    assert vx1 is vx2
    vn1 = V("vn", "Nat")
    vn2 = V("vn", "Nat")
    assert vn1 is vn2

    reset_var_interner()
    _ = V("u")
    with pytest.raises(ValueError):
        V("u", "Nat")

    reset_var_interner()
    _ = V("u", "Nat")
    with pytest.raises(ValueError):
        V("u", "List")


def test_traces_certificates_and_sessions(env) -> None:  # type: ignore
    add = env["add"]
    app = env["app"]
    x = env["x"]
    xs = env["xs"]
    zero = env["zero"]
    nil = env["nil"]
    eq = env["eq"]
    engine = env["engine"]

    nat_scheme = get_induction_scheme(engine, "nat")
    assert nat_scheme is not None
    list_scheme = get_induction_scheme(engine, "list")
    assert list_scheme is not None

    ys = V("ys", "List")
    zs = V("zs", "List")
    assoc_goal = Clause((), eq(app(app(xs, ys), zs), app(xs, app(ys, zs))))
    ok_trace, ptrace = prove_with_trace(
        assoc_goal, engine, depth=12, var=xs, scheme=list_scheme, induction_depth=1
    )
    assert ok_trace
    rendered = render_proof_trace(ptrace)
    assert "induction" in rendered
    assert "scheme=list" in rendered
    assert "induction-branch" in rendered

    clause4 = Clause((), eq(add(x, zero), x))
    ok_cert, cert = prove_checked(
        clause4, engine, depth=8, var=x, scheme=nat_scheme, induction_depth=1
    )
    assert ok_cert and cert is not None
    assert check_certificate(cert, engine, depth=8, induction_depth=1)

    bad_cert = ProofCertificate(
        clause=cert.clause,
        simplified=Clause(
            cert.simplified.assumptions, false, cert.simplified.disequalities
        ),
        step=cert.step,
        children=cert.children,
        var=cert.var,
        scheme_name=cert.scheme_name,
    )
    assert not check_certificate(bad_cert, engine, depth=8, induction_depth=1)

    sess = ProofSession(clause4, engine)
    sess.induct(x, scheme=nat_scheme)
    while sess.goals:
        sess.simp()
        if sess.goals:
            sess.exact()
    assert sess.qed()

    lemma = Lemma("add_right_id", clause4, cert)
    sess2 = ProofSession(
        Clause((), eq(add(App("S", zero), zero), App("S", zero))), engine
    )
    sess2.register_lemma(lemma, depth=8, induction_depth=1)
    sess2.apply_lemma("add_right_id")
    sess2.simp()
    if sess2.goals:
        sess2.exact()
    assert sess2.qed()

    ok_assoc_cert, assoc_cert = prove_checked(
        assoc_goal, engine, depth=12, var=xs, scheme=list_scheme, induction_depth=1
    )
    assert ok_assoc_cert and assoc_cert is not None
    cert_trace = certificate_to_proof_trace(assoc_cert)
    cert_rendered = render_proof_trace(cert_trace)
    assert "checked-induction" in cert_rendered
    assert "checked-simplify" in cert_rendered

    sess_trace_rendered = render_proof_trace(sess.trace)
    assert "session-induct" in sess_trace_rendered
    assert "session-simp" in sess_trace_rendered
    assert "session-exact" in sess_trace_rendered

    waterfall_rendered = render_waterfall_trace(ptrace)
    assert "simplify" in waterfall_rendered
    assert "induct" in waterfall_rendered
    assert "branch" in waterfall_rendered
    assert "prove ->" in waterfall_rendered


def test_theorem_scopes_and_tactics(env) -> None:  # type: ignore
    add = env["add"]
    app = env["app"]
    x = env["x"]
    x_nat = env["x_nat"]
    xs = env["xs"]
    zero = env["zero"]
    nil = env["nil"]
    eq = env["eq"]
    shared_config = env["shared_config"]

    scoped_rules = builtin_rules()
    scoped_engine = make_engine(
        rules=scoped_rules, config=shared_config, ground_cache={}, schemes={}
    )
    install_theory(scoped_engine, nat_theory(), activate_scopes=True)
    install_theory(scoped_engine, list_theory(), activate_scopes=True)
    scoped_theory = get_theorem_environment(scoped_engine)
    scoped_list = get_induction_scheme(scoped_engine, "list")
    assert scoped_list is not None

    scoped_clause = Clause((), eq(app(xs, nil), xs))
    ok_scoped_cert, scoped_cert = prove_checked(
        scoped_clause,
        scoped_engine,
        depth=10,
        var=xs,
        scheme=scoped_list,
        induction_depth=1,
    )
    assert ok_scoped_cert and scoped_cert is not None
    scoped_lemma = Lemma("append_right_id_scoped", scoped_clause, scoped_cert)
    scoped_theory.register_lemma(scoped_lemma, depth=10, induction_depth=1)
    scoped_theory.register_lemma_rewrite(
        "append_right_id_scoped", scope="list_scope", orientation="auto"
    )
    assert str(normalize(app(xs, nil), scoped_engine)) == "append(xs, nil)"
    scoped_theory.activate_scope("list_scope")
    assert str(normalize(app(xs, nil), scoped_engine)) == "xs"
    scoped_theory.deactivate_scope("list_scope")
    assert str(normalize(app(xs, nil), scoped_engine)) == "append(xs, nil)"

    register_sort_signature(
        scoped_engine, "double", SortSignature((TypeConst("Nat"),), TypeConst("Nat"))
    )
    scoped_theory.register_definition(
        "double", App("double", x), add(x, x), scope="def_scope"
    )
    scoped_theory.activate_scope("def_scope")
    assert str(normalize(App("double", App("S", zero)), scoped_engine)) == "S(S(0))"
    with pytest.raises(ValueError):
        scoped_theory.register_definition(
            "bad_recursive", App("fdef", x), App("fdef", x), scope="def_scope"
        )
    scoped_theory.deactivate_scope("def_scope")

    zero_nat = Const("0")
    succ = lambda t: App("S", t)
    sum_to = lambda t: App("sum_to", t)
    register_recursive_definition(
        scoped_engine,
        "sum_to",
        (
            (sum_to(zero_nat), zero_nat),
            (sum_to(succ(x_nat)), add(succ(x_nat), sum_to(x_nat))),
        ),
        signature=SortSignature((TypeConst("Nat"),), TypeConst("Nat")),
        precedence=5,
        scope="rec_scope",
    )
    assert str(normalize(sum_to(succ(zero_nat)), scoped_engine)) == "sum_to(S(0))"
    scoped_theory.activate_scope("rec_scope")
    assert str(normalize(sum_to(succ(zero_nat)), scoped_engine)) == "S(0)"
    scoped_theory.deactivate_scope("rec_scope")

    sess_defs = ProofSession(Clause((), eq(sum_to(zero_nat), zero_nat)), scoped_engine)
    sess_defs.register_recursive_definition(
        "sum_to_sess",
        (
            (App("sum_to_sess", zero_nat), zero_nat),
            (
                App("sum_to_sess", succ(x_nat)),
                add(succ(x_nat), App("sum_to_sess", x_nat)),
            ),
        ),
        scope="rec_scope_sess",
        signature=SortSignature((TypeConst("Nat"),), TypeConst("Nat")),
        precedence=5,
    )
    scoped_theory.activate_scope("rec_scope_sess")
    assert str(normalize(App("sum_to_sess", succ(zero_nat)), scoped_engine)) == "S(0)"
    scoped_theory.deactivate_scope("rec_scope_sess")

    with pytest.raises(ValueError):
        register_recursive_definition(
            scoped_engine,
            "sum_to",
            (),
            scope="rec_scope",
        )
    with pytest.raises(ValueError):
        register_recursive_definition(
            scoped_engine,
            "sum_to",
            ((App("other_symbol", x_nat), x_nat),),
            scope="rec_scope",
        )
    with pytest.raises(ValueError):
        register_recursive_definition(
            scoped_engine,
            "double",
            ((App("double", x_nat), add(x_nat, x_nat)),),
            scope="rec_scope",
        )
    with pytest.raises(ValueError):
        register_recursive_definition(
            scoped_engine,
            "badrec",
            ((App("badrec", x_nat), App("badrec", succ(x_nat))),),
            signature=SortSignature((TypeConst("Nat"),), TypeConst("Nat")),
            scope="rec_scope",
        )

    reflexive_clause = Clause((), eq(add(x, env["y"]), add(x, env["y"])))
    ok_refl, refl_cert = prove_checked(reflexive_clause, env["engine"], depth=6)
    assert ok_refl and refl_cert is not None
    refl_lemma = Lemma("add_refl", reflexive_clause, refl_cert)
    scoped_theory.register_lemma(refl_lemma, depth=6, induction_depth=1)
    with pytest.raises(ValueError):
        scoped_theory.register_lemma_rewrite(
            "add_refl", scope="list_scope", orientation="auto"
        )

    sess3 = ProofSession(Clause((), eq(app(xs, nil), xs)), scoped_engine)
    sess3.activate_scope("list_scope")
    sess3.simp()
    assert sess3.qed()
    sess3.deactivate_scope("list_scope")

    auto_clause = Clause((), eq(add(x_nat, zero), x_nat))
    sess_auto = ProofSession(auto_clause, env["engine"])
    sess_auto.induct(x_nat)
    assert len(sess_auto.goals) == 2
    sess_auto_fail = ProofSession(Clause((), eq(add(x, zero), x)), env["engine"])
    with pytest.raises(ValueError):
        sess_auto_fail.induct(x)

    y_nat = V("yn", "Nat")
    multi_clause = Clause((), eq(add(x_nat, y_nat), add(x_nat, y_nat)))
    sess_multi = ProofSession(multi_clause, env["engine"])
    sess_multi.induct_many([x_nat, y_nat])
    assert len(sess_multi.goals) == 4

    ys2 = V("ys2", "List")
    zs2 = V("zs2", "List")
    assoc_goal2 = Clause((), eq(app(app(xs, ys2), zs2), app(xs, app(ys2, zs2))))
    list_scheme = get_induction_scheme(env["engine"], "list")
    assert list_scheme is not None
    sess_ih_keep = ProofSession(assoc_goal2, env["engine"])
    sess_ih_keep.induct(xs, scheme=list_scheme)
    sess_ih_keep.simp()
    assert len(sess_ih_keep.assumptions()) >= 1
    sess_ih_keep.simp()
    assert sess_ih_keep.qed()

    sess_ih_drop = ProofSession(assoc_goal2, env["engine"])
    sess_ih_drop.induct(xs, scheme=list_scheme)
    sess_ih_drop.simp()
    assert len(sess_ih_drop.assumptions()) >= 1
    sess_ih_drop.keep_assumptions([])
    sess_ih_drop.simp()
    assert sess_ih_drop.goals is not None
    current = sess_ih_drop.current_goal()
    assert current is not None
    assert current.goal != true

    with pytest.raises(ValueError):
        sess_multi.induct_many(
            [x_nat, y_nat], schemes=[get_induction_scheme(env["engine"], "nat")]
        )

    dup_clause = Clause(((x, env["y"]), (env["y"], x), (x, env["y"])), eq(x, env["y"]))
    dup_simplified = simplify_clause(dup_clause, env["engine"])
    assert len(dup_simplified.assumptions) == 1
    assert dup_simplified.assumptions[0] == (x, env["y"])

    sess_stages = ProofSession(dup_clause, env["engine"])
    sess_stages.simp()
    sess_stages_rendered = render_proof_trace(sess_stages.trace)
    assert "stage-assumptions" in sess_stages_rendered
    assert "stage-rule-goal" in sess_stages_rendered
    assert "stage-context-goal" in sess_stages_rendered


def test_typing_theories_and_installation(env) -> None:  # type: ignore
    add = env["add"]
    mul = env["mul"]
    bnot = env["bnot"]
    band = env["band"]
    bor = env["bor"]
    x = env["x"]
    x_nat = env["x_nat"]
    zero = env["zero"]
    one = env["one"]
    nil = env["nil"]
    engine = env["engine"]
    shared_config = env["shared_config"]

    is_zero_sig = SortSignature((TypeConst("Nat"),), TypeConst("Bool"))
    register_sort_signature(engine, "is_zero", is_zero_sig)
    assert get_sort_signature(engine, "is_zero") == is_zero_sig
    assert infer_sort(App("is_zero", zero), engine) == "Bool"

    with pytest.raises(ValueError):
        infer_sort(add(nil, zero), engine)
    with pytest.raises(ValueError):
        infer_sort(App("mystery", nil), engine)
    with pytest.raises(ValueError):
        make_engine(
            rules=builtin_rules() + [Rule(add(nil, zero), zero)],
            config=shared_config,
            ground_cache={},
            schemes={},
        )

    scoped_theory_engine = make_engine(
        rules=builtin_rules(), config=shared_config, ground_cache={}, schemes={}
    )
    install_theory(scoped_theory_engine, nat_theory(), activate_scopes=True)
    install_theory(scoped_theory_engine, list_theory(), activate_scopes=True)
    scoped_theory = get_theorem_environment(scoped_theory_engine)
    with pytest.raises(ValueError):
        scoped_theory.register_definition(
            "bad_len", App("length", zero), zero, scope="def_scope"
        )

    bad_clause_sort = Clause((), App("eq", add(nil, zero), zero))
    with pytest.raises(ValueError):
        simplify_clause(bad_clause_sort, engine)
    with pytest.raises(ValueError):
        infer_sort(x, engine)

    nat_scheme = get_induction_scheme(engine, "nat")
    assert nat_scheme is not None
    toy_theory = Theory(
        name="toy.arith",
        version="1.0.0",
        depends_on=("core.peano>=1.0.0",),
        sort_signatures={
            "double": SortSignature((TypeConst("Nat"),), TypeConst("Nat"))
        },
        rules=(Rule(App("double", x), add(x, x)),),
        definitions={"double": Rule(App("double", x), add(x, x))},
        schemes=(nat_scheme,),
        default_scopes=("toy_scope",),
    )
    assert toy_theory.name == "toy.arith"
    assert toy_theory.rules[0].lhs == App("double", x)
    assert toy_theory.definitions["double"].rhs == add(x, x)
    _ToyModule = types.ModuleType("_ToyModule")
    _ToyModule.THEORY = toy_theory  # type: ignore
    assert theory_from_module(_ToyModule) is toy_theory
    with pytest.raises(ValueError):
        theory_from_module(object())  # type: ignore

    install_rules = builtin_rules()
    install_engine_a = make_engine(
        rules=install_rules, config=shared_config, ground_cache={}, schemes={}
    )
    install_engine_b = make_engine(
        rules=install_rules, config=shared_config, ground_cache={}, schemes={}
    )
    install_theory(install_engine_a, nat_theory(), activate_scopes=True)
    install_theory(install_engine_b, nat_theory(), activate_scopes=True)
    install_theory_payload = Theory(
        name="toy.install",
        sort_signatures={
            "double": SortSignature((TypeConst("Nat"),), TypeConst("Nat"))
        },
        rules=(Rule(App("double", x), add(x, x)),),
        precedence={"double": 4},
    )
    assert install_theory_payload.name == "toy.install"
    activated_scopes = install_theory(
        install_engine_a, install_theory_payload, activate_scopes=False
    )
    assert activated_scopes == ("theory:toy.install",)
    assert (
        str(normalize(App("double", App("S", zero)), install_engine_a))
        == "double(S(0))"
    )
    get_theorem_environment(install_engine_a).activate_scope("theory:toy.install")
    install_engine_a.ground_cache.clear()
    assert str(normalize(App("double", App("S", zero)), install_engine_a)) == "S(S(0))"
    with pytest.raises(ValueError):
        infer_sort(App("double", App("S", zero)), install_engine_b)

    install_engine_c = make_engine(
        rules=install_rules, config=shared_config, ground_cache={}, schemes={}
    )
    install_theory(install_engine_c, nat_theory(), activate_scopes=True)
    dep_only = Theory(name="toy.dep-only", depends_on=("core.arith>=1.0.0",))
    with pytest.raises(ValueError):
        install_theory(install_engine_c, dep_only)
    core_arith = Theory(name="core.arith", version="1.0.0")
    install_theory(install_engine_c, core_arith, activate_scopes=False)
    install_theory(install_engine_c, dep_only, activate_scopes=False)
    with pytest.raises(ValueError):
        install_theory(
            install_engine_c,
            Theory(name="core.arith", version="2.0.0"),
            activate_scopes=False,
        )
    with pytest.raises(ValueError):
        install_theory(
            install_engine_c,
            Theory(
                name="bad.sig",
                sort_signatures={
                    "add": SortSignature(
                        (TypeConst("Nat"), TypeConst("Bool")), TypeConst("Nat")
                    )
                },
            ),
            activate_scopes=False,
        )
    install_env_c = get_theorem_environment(install_engine_c)
    install_env_c.create_scope("shared_scope")
    install_env_c.register_rule(
        Rule(add(x, zero), x), scope="shared_scope", label="seed.shared"
    )
    with pytest.raises(ValueError):
        install_theory(
            install_engine_c,
            Theory(name="bad.scope", default_scopes=("shared_scope",)),
            activate_scopes=False,
        )

    install_engine_d = make_engine(
        rules=install_rules, config=shared_config, ground_cache={}, schemes={}
    )
    install_theory(install_engine_d, nat_theory(), activate_scopes=True)
    bad_atomic = Theory(
        name="bad.atomic",
        sort_signatures={
            "double": SortSignature((TypeConst("Nat"),), TypeConst("Nat"))
        },
        rules=(Rule(add(nil, zero), zero),),
        default_scopes=("atomic_scope",),
    )
    with pytest.raises(ValueError):
        install_theory(install_engine_d, bad_atomic, activate_scopes=True)
    assert "bad.atomic" not in install_engine_d.installed_theories
    with pytest.raises(ValueError):
        infer_sort(App("double", App("S", zero)), install_engine_d)
    install_env_d = get_theorem_environment(install_engine_d)
    assert "theory:bad.atomic" not in install_env_d.scoped_rule_sets
    assert "atomic_scope" not in install_env_d.scoped_rule_sets

    install_engine_e = make_engine(
        rules=install_rules, config=shared_config, ground_cache={}, schemes={}
    )
    install_theory(install_engine_e, list_theory(), activate_scopes=False)
    with pytest.raises(ValueError):
        install_theory(
            install_engine_e,
            Theory(name="bad.sort-arity", sort_arities={"List": 2}),
            activate_scopes=False,
        )

    mul_zero_goal = Clause((), App("eq", mul(x_nat, zero), zero))
    assert prove_with_registered_induction(
        mul_zero_goal, engine, x_nat, "nat", depth=12, induction_depth=1
    )
    y_nat = V("y_nat", "Nat")
    mul_succ_goal = Clause(
        (), App("eq", mul(x_nat, App("S", y_nat)), add(x_nat, mul(x_nat, y_nat)))
    )
    assert prove_with_registered_induction(
        mul_succ_goal, engine, x_nat, "nat", depth=16, induction_depth=1
    )

    assert normalize(bnot(true), engine) == false
    assert normalize(band(true, false), engine) == false
    assert normalize(bor(false, true), engine) == true

    x_bool = V("xb", "Bool")
    y_bool = V("yb", "Bool")
    register_induction_scheme(
        engine,
        InductionScheme(
            name="bool", sort="Bool", base_terms=(true, false), constructors=()
        ),
    )
    demorgan_goal = Clause(
        (),
        App(
            "eq",
            bnot(band(x_bool, y_bool)),
            bor(bnot(x_bool), bnot(y_bool)),
        ),
    )
    assert prove_with_registered_induction(
        demorgan_goal, engine, x_bool, "bool", depth=12, induction_depth=1
    )

    core_config = default_engine_config()
    core_sigs = default_sort_signatures()
    core_engine = make_engine(
        rules=builtin_rules(), config=core_config, ground_cache={}, schemes={}
    )
    for sym in ("add", "mul", "nil", "cons", "append", "length"):
        assert sym not in core_config.precedence
        assert sym not in core_config.assoc
        assert sym not in core_config.comm
        assert sym not in core_sigs
    assert "List" not in core_engine.sort_arities

    nat_core = nat_theory()
    assert nat_core.precedence["add"] == 3
    assert nat_core.precedence["mul"] == 4
    assert "add" in nat_core.assoc and "add" in nat_core.comm
    list_core = list_theory()
    assert list_core.sort_arities["List"] == 1
    assert list_core.precedence["cons"] == 2
    assert list_core.precedence["append"] == 3
    assert list_core.precedence["length"] == 3
    assert one == Const("1")


def test_map_theory() -> None:
    reset_var_interner()
    m = V("m", "Map")
    k = V("mk")
    k1 = V("mk1")
    k2 = V("mk2")
    v = V("mv")
    v1 = V("mv1")
    v2 = V("mv2")

    empty = Const("empty")
    none = Const("none")
    put = lambda m, k, v: App("put", m, k, v)
    get = lambda m, k: App("get", m, k)
    some = lambda x: App("some", x)
    eq = lambda a, b: App("eq", a, b)

    map_core = map_theory()
    assert map_core.sort_arities["Map"] == 2
    assert map_core.sort_arities["Option"] == 1
    assert map_core.sort_signatures["empty"].result_sort == TypeConst(
        "Map", (TypeVar("K"), TypeVar("V"))
    )
    assert map_core.sort_signatures["get"].result_sort == TypeConst(
        "Option", (TypeVar("V"),)
    )
    assert map_core.precedence["put"] == 2
    assert map_core.precedence["get"] == 2

    map_engine = make_engine(rules=builtin_rules(), ground_cache={}, schemes={})
    install_theory(map_engine, map_theory(), activate_scopes=True)

    get_empty_goal = Clause((), eq(get(empty, k), none), ())  # type: ignore
    assert prove(get_empty_goal, map_engine, depth=8)

    get_put_same_goal = Clause((), eq(get(put(m, k, v), k), some(v)), ())  # type: ignore
    assert prove(get_put_same_goal, map_engine, depth=8)

    get_put_outer_goal = Clause(
        (),
        eq(get(put(put(m, k2, v2), k1, v1), k1), some(v1)),  # type: ignore
        (),
    )
    assert prove(get_put_outer_goal, map_engine, depth=8)

    get_put_inner_diseq_goal = Clause(
        (),
        eq(get(put(put(m, k1, v1), k2, v2), k1), some(v1)),  # type: ignore
        ((k2, k1),),
    )
    assert prove(get_put_inner_diseq_goal, map_engine, depth=8)

    get_put_inner_diseq_simp = simplify_clause(
        Clause((), eq(get(put(put(m, k1, v1), k2, v2), k1), some(v1)), ((k2, k1),)),  # type: ignore
        map_engine,
    )
    assert clause_solved(get_put_inner_diseq_simp)

    get_put_inner_no_cond_goal = Clause(
        (),
        eq(get(put(put(m, k1, v1), k2, v2), k1), some(v1)),  # type: ignore
        (),
    )
    assert not prove(get_put_inner_no_cond_goal, map_engine, depth=8)

    get_put_if_goal = Clause((), eq(get(put(m, k1, v1), k2), some(v1)), ())  # type: ignore
    get_put_simp = simplify_clause(get_put_if_goal, map_engine)
    assert isinstance(get_put_simp.goal, Fun)
    get_put_simp_lhs = get_put_simp.goal.args[0]
    assert get_put_simp_lhs == App("if", eq(k1, k2), some(v1), get(m, k2))  # type: ignore

    if_cond = App("if", eq(k1, k2), some(v1), get(m, k2))  # type: ignore
    split_if_clause = Clause((), if_cond, ())
    branches = split_clause(split_if_clause)
    assert len(branches) == 2
    assert branches[0].assumptions == ((k1, k2),)
    assert branches[1].disequalities == ((k1, k2),)


def test_int_theory() -> None:
    reset_var_interner()
    x = V("zi_x", "Int")
    y = V("zi_y", "Int")
    a = V("zi_a", "Int")
    b = V("zi_b", "Int")
    c = V("zi_c", "Int")
    zero_nat = Const("0")
    S = lambda t: App("S", t)

    z0 = Const("z0")
    z1 = Const("z1")
    zint = lambda p, n: App("zint", p, n)
    zadd = lambda l, r: App("zadd", l, r)
    zmul = lambda l, r: App("zmul", l, r)
    zneg = lambda t: App("zneg", t)
    eq = lambda l, r: App("eq", l, r)

    int_core = int_theory()
    assert int_core.depends_on == ("core.nat",)
    assert int_core.sort_signatures["z0"].result_sort == TypeConst("Int")
    assert int_core.sort_signatures["zadd"].arg_sorts == (
        TypeConst("Int"),
        TypeConst("Int"),
    )
    assert int_core.precedence["zadd"] == 3
    assert int_core.precedence["zmul"] == 4
    assert "zadd" in int_core.assoc and "zadd" in int_core.comm
    assert "zmul" in int_core.assoc and "zmul" in int_core.comm

    missing_dep_engine = make_engine(rules=builtin_rules(), ground_cache={}, schemes={})
    with pytest.raises(ValueError, match="Missing theory dependency: core.nat"):
        install_theory(missing_dep_engine, int_theory(), activate_scopes=True)

    engine = make_engine(rules=builtin_rules(), ground_cache={}, schemes={})
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, int_theory(), activate_scopes=True)

    assert str(normalize(zadd(z1, z0), engine)) == "zint(S(0), 0)"
    assert str(normalize(zadd(z1, zneg(z1)), engine)) == "zint(0, 0)"
    assert str(normalize(zneg(z1), engine)) == "zint(0, S(0))"
    assert str(normalize(zadd(zint(S(S(zero_nat)), zero_nat), zint(zero_nat, S(zero_nat))), engine)) == "zint(S(0), 0)"

    comm_goal = Clause((), eq(zadd(x, y), zadd(y, x)))
    assert prove(comm_goal, engine, depth=8)
    mul_comm_goal = Clause((), eq(zmul(x, y), zmul(y, x)))
    assert prove(mul_comm_goal, engine, depth=8)

    context_goal = Clause(((a, b),), eq(zadd(a, c), zadd(b, c)))
    assert prove(context_goal, engine, depth=8)


def test_lpo_decrease_non_ac_symbol() -> None:
    reset_var_interner()

    x = V("x")
    S = lambda t: App("S", t)
    f = lambda a: App("f", a)

    shared_signatures = default_sort_signatures()
    shared_signatures["f"] = SortSignature((TypeConst("Nat"),), TypeConst("Nat"))

    config = EngineConfig(
        precedence={"S": 2, "f": 1, "0": 0},
        assoc=set(),
        comm=set(),
    )

    dec_rule = Rule(f(S(x)), f(x))
    engine_dec = make_engine(
        rules=[dec_rule],
        config=config,
        ground_cache={},
        sort_signatures=shared_signatures,
    )
    assert str(normalize(f(S(Const("0"))), engine_dec)) == "f(0)"

    non_dec_rule = Rule(f(x), f(S(x)))
    engine_non_dec = make_engine(
        rules=[non_dec_rule],
        config=config,
        ground_cache={},
        sort_signatures=shared_signatures,
    )
    assert str(normalize(f(Const("0")), engine_non_dec)) == "f(0)"


def test_lpo_decrease_skipped_for_ac_symbols() -> None:
    reset_var_interner()

    zero = Const("0")
    S = lambda t: App("S", t)
    add = lambda a, b: App("add", a, b)

    config = EngineConfig(
        precedence={"S": 2, "add": 3, "0": 0},
        assoc={"add"},
        comm={"add"},
    )
    engine = make_engine(rules=builtin_rules(), config=config, ground_cache={})
    install_theory(engine, nat_theory(), activate_scopes=True)

    assert str(normalize(add(S(zero), zero), engine)) == "S(0)"

    assert str(normalize(add(zero, S(zero)), engine)) == "S(0)"


def test_ac_and_non_ac_mixed_normalization() -> None:
    reset_var_interner()

    zero = Const("0")
    S = lambda t: App("S", t)
    add = lambda a, b: App("add", a, b)
    leaf = Const("leaf")
    node = lambda l, v, r: App("node", l, v, r)
    mirror_fn = lambda t: App("mirror", t)

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, tree_theory(), activate_scopes=True)

    register_sort_signature(
        engine,
        "mirror",
        SortSignature(
            (TypeConst("Tree", (TypeVar("A"),)),), TypeConst("Tree", (TypeVar("A"),))
        ),
    )
    engine.config.precedence["mirror"] = 5
    engine.config.assoc.add("add")
    engine.config.comm.add("add")

    l = V("l", "Tree")
    r = V("r", "Tree")
    v = V("v")

    engine.reset_rules(
        engine.rules
        + [Rule(mirror_fn(leaf), leaf)]
        + [Rule(mirror_fn(node(l, v, r)), node(mirror_fn(r), v, mirror_fn(l)))]
    )

    t = node(leaf, v, leaf)
    assert str(normalize(mirror_fn(t), engine)) == "node(leaf, v, leaf)"

    s = add(S(zero), zero)
    assert str(normalize(s, engine)) == "S(0)"

    t2 = add(zero, S(zero))
    assert str(normalize(t2, engine)) == "S(0)"


def test_context_equality_classification() -> None:
    """Test that ground, substitution, and rewrite equalities are properly classified."""
    from fiddlehead.proof import _build_context
    from fiddlehead.kernel import is_ground, _build_eq_classes, _schematic_rules

    reset_var_interner()
    x = V("x")
    y = V("y")
    zero = Const("0")
    succ_x = App("S", x)
    succ_zero = App("S", zero)

    ground_eq = (zero, succ_zero)
    rewrite_eq = (succ_x, App("S", App("S", x)))
    substitution_eq = (x, zero)

    assert is_ground(ground_eq[0]) and is_ground(ground_eq[1])
    assert not is_ground(rewrite_eq[0]) or not is_ground(rewrite_eq[1])
    assert not is_ground(substitution_eq[0]) or not is_ground(substitution_eq[1])

    ctx = _build_context((ground_eq, rewrite_eq, substitution_eq), ())
    assert ctx.substitutions == ((x, zero),)
    assert ctx.ground_equalities == ((zero, succ_zero),)
    assert ctx.rewrite_equalities == ((succ_x, App("S", App("S", x))),)

    ec = _build_eq_classes(ctx)
    assert ec.are_equal(zero, succ_zero)
    assert ec.are_equal(x, zero)

    rules = list(_schematic_rules(ctx, default_engine_config()))
    assert len(rules) == 1
    for rule in rules:
        assert not isinstance(rule.lhs, Var)
    assert all(rule.skip_decrease_check for rule in rules)


def test_contradiction_pruning(env) -> None:  # type: ignore
    x = env["x"]
    y = env["y"]
    z = env["z"]
    S = env["S"]
    zero = env["zero"]
    eq = env["eq"]
    neq = env["neq"]
    engine = env["engine"]

    basic_contradiction = Clause((), eq(x, y), ((x, y),))
    assert not prove(basic_contradiction, engine, depth=5)

    ground_contradiction = Clause((), eq(S(zero), zero), ((S(zero), zero),))
    assert not prove(ground_contradiction, engine, depth=5)

    multiple_diseq_clause = Clause((), eq(x, y), ((x, y), (y, z)))
    assert not prove(multiple_diseq_clause, engine, depth=5)

    if_cond = App("if", eq(x, y), eq(x, y), false)
    split_branches = split_clause(Clause((), if_cond, ()))
    assert len(split_branches) == 2
    assert split_branches[0].assumptions == ((x, y),)
    assert split_branches[1].disequalities == ((x, y),)

    no_contradiction = Clause((), eq(x, y), ((x, z),))
    result = prove(no_contradiction, engine, depth=5)
    assert result is False

    complex_clause = Clause(((y, z),), eq(x, y), ((x, z),))
    assert not prove(complex_clause, engine, depth=5)
