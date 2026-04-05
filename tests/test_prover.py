from __future__ import annotations

from typing import Dict

import pytest

from fiddlehead.prover import *


@pytest.fixture
def env():
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

    r3 = Rule(f(x), one, conditions=((x, zero),))
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


def test_term_rewriting_basics(env):
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
    assert m[x] is zero
    assert str(normalize(add(y, add(x, z)), engine)) == "add(x, add(y, z))"
    assert str(normalize(f(zero), engine)) == "1"
    assert str(normalize(f(S(zero)), engine)) == "f(S(0))"
    assert normalize(eq(zero, zero), engine) == true
    assert normalize(neq(zero, zero), engine) == false
    assert one == Const("1")


def test_trace_clause_and_cache_basics(env):
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


def test_induction_branches_and_proofs(env):
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

    assert prove_with_induction(clause4, engine, x, nat_scheme, depth=8, induction_depth=1)
    bad = Clause((), eq(add(zero, one), zero))
    assert not prove(bad, engine, depth=8)
    assert not prove_with_induction(clause4, engine, xs, nat_scheme, depth=8, induction_depth=1)
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


def test_cache_and_config_isolation(env):
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


def test_variable_interning_and_sort_conflicts():
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


def test_traces_certificates_and_sessions(env):
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
        simplified=Clause(cert.simplified.assumptions, false),
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
    sess2 = ProofSession(Clause((), eq(add(App("S", zero), zero), App("S", zero))), engine)
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


def test_theorem_scopes_and_tactics(env):
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
        scoped_clause, scoped_engine, depth=10, var=xs, scheme=scoped_list, induction_depth=1
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

    register_sort_signature(scoped_engine, "double", SortSignature(("Nat",), "Nat"))
    scoped_theory.register_definition("double", App("double", x), add(x, x), scope="def_scope")
    scoped_theory.activate_scope("def_scope")
    assert str(normalize(App("double", App("S", zero)), scoped_engine)) == "S(S(0))"
    with pytest.raises(ValueError):
        scoped_theory.register_definition(
            "bad_recursive", App("fdef", x), App("fdef", x), scope="def_scope"
        )
    scoped_theory.deactivate_scope("def_scope")

    reflexive_clause = Clause((), eq(add(x, env["y"]), add(x, env["y"])))
    ok_refl, refl_cert = prove_checked(reflexive_clause, env["engine"], depth=6)
    assert ok_refl and refl_cert is not None
    refl_lemma = Lemma("add_refl", reflexive_clause, refl_cert)
    scoped_theory.register_lemma(refl_lemma, depth=6, induction_depth=1)
    with pytest.raises(ValueError):
        scoped_theory.register_lemma_rewrite("add_refl", scope="list_scope", orientation="auto")

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
    assert sess_ih_drop.goals and sess_ih_drop.current_goal().goal != true

    with pytest.raises(ValueError):
        sess_multi.induct_many([x_nat, y_nat], schemes=[get_induction_scheme(env["engine"], "nat")])

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


def test_typing_theories_and_installation(env):
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

    is_zero_sig = SortSignature(("Nat",), "Bool")
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
        scoped_theory.register_definition("bad_len", App("length", zero), zero, scope="def_scope")

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
        sort_signatures={"double": SortSignature(("Nat",), "Nat")},
        rules=(Rule(App("double", x), add(x, x)),),
        definitions={"double": Rule(App("double", x), add(x, x))},
        schemes=(nat_scheme,),
        default_scopes=("toy_scope",),
    )
    assert toy_theory.name == "toy.arith"
    assert toy_theory.rules[0].lhs == App("double", x)
    assert toy_theory.definitions["double"].rhs == add(x, x)
    _ToyModule = type("_ToyModule", (), {"THEORY": toy_theory})
    assert theory_from_module(_ToyModule) is toy_theory
    with pytest.raises(ValueError):
        theory_from_module(object())

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
        sort_signatures={"double": SortSignature(("Nat",), "Nat")},
        rules=(Rule(App("double", x), add(x, x)),),
        precedence={"double": 4},
    )
    activated_scopes = install_theory(
        install_engine_a, install_theory_payload, activate_scopes=False
    )
    assert activated_scopes == ("theory:toy.install",)
    assert str(normalize(App("double", App("S", zero)), install_engine_a)) == "double(S(0))"
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
                sort_signatures={"add": SortSignature(("Nat", "Bool"), "Nat")},
            ),
            activate_scopes=False,
        )
    install_env_c = get_theorem_environment(install_engine_c)
    install_env_c.create_scope("shared_scope")
    install_env_c.register_rule(Rule(add(x, zero), x), scope="shared_scope", label="seed.shared")
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
        sort_signatures={"double": SortSignature(("Nat",), "Nat")},
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
        InductionScheme(name="bool", sort="Bool", base_terms=(true, false), constructors=()),
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
    core_engine = make_engine(rules=builtin_rules(), config=core_config, ground_cache={}, schemes={})
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
