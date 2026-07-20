from __future__ import annotations

from fiddlehead.prover import (
    App,
    Clause,
    Const,
    ProofSession,
    Rule,
    RuleClass,
    SortSignature,
    TypeConst,
    V,
    builtin_rules,
    certificate_to_proof_trace,
    check_certificate,
    forward_chaining_rule_class,
    get_theorem_environment,
    get_induction_scheme,
    install_theory,
    list_theory,
    make_engine,
    nat_theory,
    normalize,
    prove,
    prove_checked,
    render_proof_trace,
    register_sort_signature,
    render_waterfall_trace,
    reset_var_interner,
)


def test_forward_chaining_rules_are_not_implicit_rewrites() -> None:
    reset_var_interner()
    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    theory = get_theorem_environment(engine)

    x = V("x", "Nat")
    zero = Const("0")
    register_sort_signature(engine, "id_nat", SortSignature((TypeConst("Nat"),), TypeConst("Nat")))

    fc_name = theory.register_rule(
        Rule(App("id_nat", x), x),
        scope="fc_scope",
        label="id-nat-fc",
        rule_classes=(forward_chaining_rule_class(),),
    )

    assert theory.get_named_rule_classes(fc_name) == (forward_chaining_rule_class(),)
    assert fc_name in theory.list_named_rules(rule_class=RuleClass.FORWARD_CHAINING)
    assert fc_name not in theory.list_named_rules(rule_class=RuleClass.REWRITE)

    theory.activate_scope("fc_scope")
    assert str(normalize(App("id_nat", zero), engine)) == "id_nat(0)"

    session = ProofSession(Clause((), App("eq", zero, zero)), engine)
    assert fc_name in session.list_rules(rule_class=RuleClass.FORWARD_CHAINING)
    assert fc_name not in session.list_rules(rule_class=RuleClass.REWRITE)


def test_waterfall_uses_forward_chaining_rules() -> None:
    reset_var_interner()
    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    theory = get_theorem_environment(engine)

    x = V("x", "Nat")
    zero = Const("0")
    eq = lambda a, b: App("eq", a, b)
    register_sort_signature(engine, "id_nat", SortSignature((TypeConst("Nat"),), TypeConst("Nat")))

    theory.register_rule(
        Rule(App("id_nat", x), x),
        scope="fc_scope",
        label="id-nat-fc",
        rule_classes=(forward_chaining_rule_class(),),
    )
    theory.activate_scope("fc_scope")

    goal = Clause((), eq(App("id_nat", zero), zero))

    assert prove(goal, engine, depth=4)

    ok = prove(goal, engine, depth=4)
    assert ok

    rendered = render_waterfall_trace(ok.trace)
    assert "forward-chain" in rendered
    assert "simplify" in rendered


def test_prove_checked_uses_waterfall_by_default() -> None:
    reset_var_interner()
    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    theory = get_theorem_environment(engine)

    x = V("x", "Nat")
    zero = Const("0")
    eq = lambda a, b: App("eq", a, b)
    register_sort_signature(
        engine, "id_nat", SortSignature((TypeConst("Nat"),), TypeConst("Nat"))
    )

    theory.register_rule(
        Rule(App("id_nat", x), x),
        scope="fc_scope",
        label="id-nat-fc",
        rule_classes=(forward_chaining_rule_class(),),
    )
    theory.activate_scope("fc_scope")

    ok = prove_checked(Clause((), eq(App("id_nat", zero), zero)), engine, depth=4)
    assert ok and ok.certificate is not None
    assert ok.certificate.step == "forward-chain"
    assert check_certificate(ok.certificate, engine, depth=4)

    rendered = render_proof_trace(certificate_to_proof_trace(ok.certificate))
    assert "checked-forward-chain" in rendered
    # prove_checked pre-populates the same trace on the result.
    assert "checked-forward-chain" in render_proof_trace(ok.trace)


def test_prove_checked_preserves_induction_support() -> None:
    reset_var_interner()
    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    xs = V("xs", "List")
    nil = Const("nil")
    eq = lambda a, b: App("eq", a, b)
    append = lambda a, b: App("append", a, b)

    list_scheme = get_induction_scheme(engine, "list")
    assert list_scheme is not None

    ok = prove_checked(
        Clause((), eq(append(xs, nil), xs)),
        engine,
        depth=10,
        var=xs,
        scheme=list_scheme,
        induction_depth=1,
    )
    assert ok and ok.certificate is not None
    assert ok.certificate.step == "induction"
    assert check_certificate(ok.certificate, engine, depth=10, induction_depth=1)
