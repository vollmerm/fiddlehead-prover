from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *


def _print_language_and_semantics() -> None:
    print("=== Hoare Logic for IMP ===\n")
    print("Language constructors:")
    print("  AExp:  aconst(n), avar(x), aadd(e1,e2), asub(e1,e2)")
    print("  BExp:  bconst(b), beq(e1,e2), blt(e1,e2), band(b1,b2)")
    print("  Com:   skip, assign(x,e), seq(c1,c2), if_cmd(b,c1,c2), while_cmd(b,c)")
    print("\nInterpreter semantics:")
    print("  eval_a(aconst(n), s) -> n")
    print("  eval_a(avar(x), s) -> nat_of(get(s, x))")
    print("  eval_a(aadd(e1,e2), s) -> add(eval_a(e1,s), eval_a(e2,s))")
    print("  eval_b(bconst(b), s) -> b")
    print("  eval_b(blt(e1,e2), s) -> blt_nat(eval_a(e1,s), eval_a(e2,s))")
    print("  exec(skip, s) -> s")
    print("  exec(assign(x,e), s) -> put(s, x, eval_a(e,s))")
    print("  exec(seq(c1,c2), s) -> exec(c2, exec(c1,s))")
    print(
        "  exec(while_cmd(b,c), s) -> if(eval_b(b,s), exec(while_cmd(b,c), exec(c,s)), s)"
    )
    print("\nHoare judgment semantics:")
    print("  hoare(P, c, Q, s) -> if(holds(P, s), holds(Q, exec(c, s)), true)")
    print("  holds(and_a(P,Q), s) -> and(holds(P,s), holds(Q,s))")
    print("  holds(not_a(P), s) -> not(holds(P,s))")
    print("  holds(bassn(b), s) -> eval_b(b, s)")
    print("  holds(aeq(x,n), s) -> eq(get(s, x), some(n))")


def _prove_rewrite(
    theorem_name: str,
    statement: str,
    goal: Clause,
    engine: Engine,
    depth: int,
) -> bool:
    print(f"\n=== {theorem_name} ===")
    print(statement)
    print("Proof by rewriting\n")
    ok, _trace = prove_with_trace(goal, engine, depth=depth)
    print(f"Proved: {ok}")
    if ok:
        print(f"Simplified to: {goal.goal} -> true")
    else:
        print(f"Failed! Goal normalized to: {engine.normalize(goal.goal)}")
    return ok


def _prove_hoare(
    theorem_name: str,
    statement: str,
    goal: Clause,
    engine: Engine,
    depth: int,
) -> bool:
    print(f"\n=== {theorem_name} ===")
    print(statement)
    print("Hoare-style proof by rewriting Hoare judgments\n")
    if goal.assumptions or goal.disequalities:
        ok, _trace = prove_with_trace(goal, engine, depth=depth)
    else:
        ok = engine.normalize(goal.goal) == Const("true")
    print(f"Proved: {ok}")
    if ok:
        print("Hoare judgment simplified to: true")
    else:
        print(f"Failed! Goal normalized to: {engine.normalize(goal.goal)}")
    return ok


def _prove_induction(
    theorem_name: str,
    statement: str,
    goal: Clause,
    engine: Engine,
    var: Var,
    scheme: InductionScheme,
    depth: int,
    induction_depth: int,
) -> bool:
    print(f"\n=== {theorem_name} ===")
    print(statement)
    print(f"Proof by induction on {var.name}\n")
    ok = prove(
        goal,
        engine,
        var=var,
        scheme=scheme,
        depth=depth,
        induction_depth=induction_depth,
    )
    print(f"Proved: {ok}")
    return ok


def main() -> None:
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)
    install_theory(engine, map_theory(), activate_scopes=True)

    a = TypeVar("A")
    k = TypeVar("K")
    v = TypeVar("V")

    x = V("x")
    y = V("y")
    n = V("n", "Nat")
    s = V("s", "Map")
    s1 = V("s1", "Map")
    s2 = V("s2", "Map")
    e1 = V("e1", "AExp")
    e2 = V("e2", "AExp")
    e = V("e", "AExp")
    b = V("b", "BExp")
    c1 = V("c1", "Com")
    c2 = V("c2", "Com")
    c = V("c", "Com")
    p_assert = V("p_assert", "Assert")
    q_assert = V("q_assert", "Assert")
    p_bool = V("p_bool", "Bool")
    bh = V("bh", "BExp")
    ch = V("ch", "Com")
    guard = V("guard", "BExp")

    zero = Const("0")
    true = Const("true")
    false = Const("false")
    skip = Const("skip")
    empty = Const("empty")
    none = Const("none")
    x_id = Const("x_id")

    succ = lambda t: App("S", t)
    add = lambda lhs, rhs: App("add", lhs, rhs)
    eq = lambda lhs, rhs: App("eq", lhs, rhs)
    get = lambda m, key: App("get", m, key)
    put = lambda m, key, val: App("put", m, key, val)
    some = lambda t: App("some", t)
    nat_of = lambda opt: App("nat_of", opt)
    if_term = lambda cond, then_t, else_t: App("if", cond, then_t, else_t)

    aconst = lambda t: App("aconst", t)
    avar = lambda t: App("avar", t)
    aadd = lambda lhs, rhs: App("aadd", lhs, rhs)
    asub = lambda lhs, rhs: App("asub", lhs, rhs)
    repeat_set = lambda value, count: App("repeat_set", value, count)

    bconst = lambda t: App("bconst", t)
    blt = lambda lhs, rhs: App("blt", lhs, rhs)

    assign = lambda var_name, expr: App("assign", var_name, expr)
    seq = lambda first, second: App("seq", first, second)
    if_cmd = lambda cond, then_cmd, else_cmd: App("if_cmd", cond, then_cmd, else_cmd)
    while_cmd = lambda cond, body: App("while_cmd", cond, body)
    bassn = lambda cond: App("bassn", cond)
    and_a = lambda lhs, rhs: App("and_a", lhs, rhs)
    not_a = lambda term: App("not_a", term)
    aeq = lambda key, val: App("aeq", key, val)

    eval_a = lambda expr, state: App("eval_a", expr, state)
    eval_b = lambda expr, state: App("eval_b", expr, state)
    exec_cmd = lambda cmd, state: App("exec", cmd, state)
    blt_nat = lambda lhs, rhs: App("blt_nat", lhs, rhs)
    holds = lambda assertion, state: App("holds", assertion, state)
    hoare = lambda pre, cmd, post, state: App("hoare", pre, cmd, post, state)

    engine.sort_arities["AExp"] = 0
    engine.sort_arities["BExp"] = 0
    engine.sort_arities["Com"] = 0
    engine.sort_arities["Assert"] = 0
    engine.sort_arities["VarId"] = 0

    register_sort_signature(
        engine, "aconst", SortSignature((TypeConst("Nat"),), TypeConst("AExp"))
    )
    register_sort_signature(engine, "avar", SortSignature((a,), TypeConst("AExp")))
    register_sort_signature(
        engine,
        "aadd",
        SortSignature((TypeConst("AExp"), TypeConst("AExp")), TypeConst("AExp")),
    )
    register_sort_signature(
        engine,
        "asub",
        SortSignature((TypeConst("AExp"), TypeConst("AExp")), TypeConst("AExp")),
    )
    register_sort_signature(
        engine, "bconst", SortSignature((TypeConst("Bool"),), TypeConst("BExp"))
    )
    register_sort_signature(
        engine,
        "blt",
        SortSignature((TypeConst("AExp"), TypeConst("AExp")), TypeConst("BExp")),
    )
    register_sort_signature(
        engine,
        "blt_nat",
        SortSignature((TypeConst("Nat"), TypeConst("Nat")), TypeConst("Bool")),
    )
    register_sort_signature(engine, "skip", SortSignature((), TypeConst("Com")))
    register_sort_signature(engine, "x_id", SortSignature((), TypeConst("VarId")))
    register_sort_signature(
        engine,
        "assign",
        SortSignature((a, TypeConst("AExp")), TypeConst("Com")),
    )
    register_sort_signature(
        engine,
        "seq",
        SortSignature((TypeConst("Com"), TypeConst("Com")), TypeConst("Com")),
    )
    register_sort_signature(
        engine,
        "if_cmd",
        SortSignature(
            (TypeConst("BExp"), TypeConst("Com"), TypeConst("Com")), TypeConst("Com")
        ),
    )
    register_sort_signature(
        engine,
        "while_cmd",
        SortSignature((TypeConst("BExp"), TypeConst("Com")), TypeConst("Com")),
    )
    register_sort_signature(
        engine,
        "repeat_set",
        SortSignature((TypeConst("Nat"), TypeConst("Nat")), TypeConst("Com")),
    )
    register_sort_signature(
        engine,
        "eval_a",
        SortSignature((TypeConst("AExp"), TypeConst("Map", (k, v))), TypeConst("Nat")),
    )
    register_sort_signature(
        engine,
        "eval_b",
        SortSignature((TypeConst("BExp"), TypeConst("Map", (k, v))), TypeConst("Bool")),
    )
    register_sort_signature(
        engine,
        "exec",
        SortSignature(
            (TypeConst("Com"), TypeConst("Map", (k, v))), TypeConst("Map", (k, v))
        ),
    )
    register_sort_signature(
        engine,
        "nat_of",
        SortSignature((TypeConst("Option", (TypeConst("Nat"),)),), TypeConst("Nat")),
    )
    register_sort_signature(
        engine, "bassn", SortSignature((TypeConst("BExp"),), TypeConst("Assert"))
    )
    register_sort_signature(
        engine,
        "and_a",
        SortSignature((TypeConst("Assert"), TypeConst("Assert")), TypeConst("Assert")),
    )
    register_sort_signature(
        engine, "not_a", SortSignature((TypeConst("Assert"),), TypeConst("Assert"))
    )
    register_sort_signature(
        engine, "aeq", SortSignature((a, TypeConst("Nat")), TypeConst("Assert"))
    )
    register_sort_signature(
        engine,
        "holds",
        SortSignature(
            (TypeConst("Assert"), TypeConst("Map", (k, v))), TypeConst("Bool")
        ),
    )
    register_sort_signature(
        engine,
        "hoare",
        SortSignature(
            (
                TypeConst("Assert"),
                TypeConst("Com"),
                TypeConst("Assert"),
                TypeConst("Map", (k, v)),
            ),
            TypeConst("Bool"),
        ),
    )

    precedence = {
        "aconst": 5,
        "avar": 5,
        "aadd": 3,
        "asub": 3,
        "bconst": 5,
        "blt": 4,
        "blt_nat": 4,
        "skip": 1,
        "assign": 1,
        "seq": 2,
        "if_cmd": 1,
        "while_cmd": 1,
        "eval_a": 5,
        "eval_b": 5,
        "exec": 5,
        "nat_of": 5,
        "bassn": 4,
        "and_a": 3,
        "not_a": 4,
        "aeq": 5,
        "holds": 5,
        "hoare": 2,
    }
    engine.config.precedence.update(precedence)

    register_recursive_definition(
        engine,
        "eval_a",
        (
            (eval_a(aconst(n), s), n),
            (eval_a(aadd(e1, e2), s), add(eval_a(e1, s), eval_a(e2, s))),
            (eval_a(asub(e1, e2), s), eval_a(e1, s)),
        ),
        signature=SortSignature(
            (TypeConst("AExp"), TypeConst("Map", (k, v))), TypeConst("Nat")
        ),
        precedence=5,
        scope="imp_def",
    )

    env = get_theorem_environment(engine)
    env.register_rule(
        Rule(eval_a(avar(x), s), nat_of(get(s, x))), "imp_def", name="eval_avar"
    )
    env.register_rule(
        Rule(
            eval_a(avar(x_id), s),
            nat_of(get(s, x_id)),
            skip_decrease_check=True,
        ),
        "imp_def",
        name="eval_avar_x_id",
    )
    env.register_rule(
        Rule(nat_of(some(n)), n, skip_decrease_check=True),
        "imp_def",
        name="nat_of_some",
    )
    env.register_rule(
        Rule(nat_of(none), zero, skip_decrease_check=True),
        "imp_def",
        name="nat_of_none",
    )
    env.register_rule(
        Rule(exec_cmd(skip, s), s, skip_decrease_check=True),
        "imp_def",
        name="exec_skip",
    )
    env.register_rule(
        Rule(
            exec_cmd(assign(x, e), s), put(s, x, eval_a(e, s)), skip_decrease_check=True
        ),
        "imp_def",
        name="exec_assign",
    )
    env.register_rule(
        Rule(exec_cmd(seq(c1, c2), s), exec_cmd(c2, exec_cmd(c1, s))),
        "imp_def",
        name="exec_seq",
    )
    env.register_rule(
        Rule(
            exec_cmd(if_cmd(bh, c1, c2), s),
            if_term(eval_b(bh, s), exec_cmd(c1, s), exec_cmd(c2, s)),
            skip_decrease_check=True,
        ),
        "imp_def",
        name="exec_if",
    )
    env.register_rule(
        Rule(exec_cmd(if_cmd(bconst(true), c1, c2), s), exec_cmd(c1, s)),
        "imp_def",
        name="exec_if_true",
    )
    env.register_rule(
        Rule(exec_cmd(if_cmd(bconst(false), c1, c2), s), exec_cmd(c2, s)),
        "imp_def",
        name="exec_if_false",
    )
    env.register_rule(
        Rule(
            put(
                put(V("m_map", "Map"), V("k_map", "VarId"), V("v_map", "Nat")),
                V("k_map", "VarId"),
                V("v_map", "Nat"),
            ),
            put(V("m_map", "Map"), V("k_map", "VarId"), V("v_map", "Nat")),
            skip_decrease_check=True,
        ),
        "imp_def",
        name="put_put_same",
    )
    env.register_rule(
        Rule(
            exec_cmd(while_cmd(bh, ch), s),
            if_term(
                eval_b(bh, s),
                exec_cmd(while_cmd(bh, ch), exec_cmd(ch, s)),
                s,
            ),
        ),
        "imp_def",
        name="exec_while",
    )
    env.register_rule(
        Rule(
            exec_cmd(while_cmd(bconst(false), ch), s),
            s,
            skip_decrease_check=True,
        ),
        "imp_def",
        name="exec_while_false",
    )
    env.register_rule(
        Rule(eval_b(bconst(true), s), true, skip_decrease_check=True),
        "imp_def",
        name="eval_b_const_true",
    )
    env.register_rule(
        Rule(eval_b(bconst(false), s), false, skip_decrease_check=True),
        "imp_def",
        name="eval_b_const_false",
    )
    env.register_rule(
        Rule(
            eval_b(blt(V("e1h"), V("e2h")), s),
            blt_nat(eval_a(V("e1h"), s), eval_a(V("e2h"), s)),
            skip_decrease_check=True,
        ),
        "imp_def",
        name="eval_b_blt",
    )
    env.register_rule(
        Rule(blt_nat(zero, zero), false), "imp_def", name="blt_nat_zero_zero"
    )
    env.register_rule(
        Rule(blt_nat(zero, succ(V("n_nat"))), true),
        "imp_def",
        name="blt_nat_zero_succ",
    )
    env.register_rule(
        Rule(blt_nat(succ(V("n_nat2")), zero), false),
        "imp_def",
        name="blt_nat_succ_zero",
    )
    env.register_rule(
        Rule(
            blt_nat(succ(V("n_nat3")), succ(V("m_nat"))),
            blt_nat(V("n_nat3"), V("m_nat")),
        ),
        "imp_def",
        name="blt_nat_succ_succ",
    )
    refl_nat = V("k_nat")
    env.register_rule(
        Rule(blt_nat(refl_nat, refl_nat), false, skip_decrease_check=True),
        "imp_def",
        name="blt_nat_refl",
    )
    env.register_rule(
        Rule(
            holds(and_a(p_assert, q_assert), s),
            App("and", holds(p_assert, s), holds(q_assert, s)),
            skip_decrease_check=True,
        ),
        "imp_def",
        name="holds_and",
    )
    env.register_rule(
        Rule(
            holds(not_a(p_assert), s),
            App("not", holds(p_assert, s)),
            skip_decrease_check=True,
        ),
        "imp_def",
        name="holds_not",
    )
    env.register_rule(
        Rule(holds(bassn(guard), s), eval_b(guard, s), skip_decrease_check=True),
        "imp_def",
        name="holds_bassn",
    )
    env.register_rule(
        Rule(holds(aeq(x, n), s), eq(get(s, x), some(n)), skip_decrease_check=True),
        "imp_def",
        name="holds_aeq",
    )
    env.register_rule(
        Rule(if_term(p_bool, p_bool, true), true, skip_decrease_check=True),
        "imp_def",
        name="if_same_true",
    )
    env.register_rule(
        Rule(if_term(p_bool, true, true), true, skip_decrease_check=True),
        "imp_def",
        name="if_true_true",
    )
    one = succ(zero)
    two = succ(one)
    hoare_semantics_rule = Rule(
        hoare(p_assert, c, q_assert, s),
        if_term(holds(p_assert, s), holds(q_assert, exec_cmd(c, s)), true),
    )
    env.register_rule(hoare_semantics_rule, "imp_def", name="hoare_semantics")

    n_rep = V("n_rep", "Nat")
    m_rep = V("m_rep", "Nat")
    env.register_definition(
        "repeat_set_zero", repeat_set(m_rep, zero), skip, scope="imp_def"
    )
    register_recursive_definition(
        engine,
        "repeat_set",
        (
            (
                repeat_set(m_rep, succ(n_rep)),
                seq(
                    assign(x_id, aconst(m_rep)),
                    repeat_set(m_rep, n_rep),
                ),
            ),
        ),
        signature=SortSignature((TypeConst("Nat"), TypeConst("Nat")), TypeConst("Com")),
        scope="imp_def",
    )

    env._sync_engine_rules()
    env.activate_scope("imp_def")

    register_induction_scheme(
        engine,
        InductionScheme(
            name="com",
            sort="Com",
            base_terms=(skip,),
            constructors=(
                InductionConstructor("assign", 2, ()),
                InductionConstructor("seq", 2, (0, 1)),
                InductionConstructor("if_cmd", 3, (1, 2)),
                InductionConstructor("while_cmd", 2, (1,)),
            ),
        ),
    )

    _print_language_and_semantics()

    goals_ok: list[bool] = []
    goals_ok.append(
        _prove_rewrite(
            "Theorem 1: Skip preserves any state",
            "forall s: exec(skip, s) = s",
            Clause((), eq(exec_cmd(skip, s), s), ()),
            engine,
            depth=8,
        )
    )
    goals_ok.append(
        _prove_rewrite(
            "Theorem 2: State extension for assignment",
            "forall x, e, s: get(exec(assign(x,e), s), x) = some(eval_a(e, s))",
            Clause((), eq(get(exec_cmd(assign(x, e), s), x), some(eval_a(e, s))), ()),
            engine,
            depth=10,
        )
    )

    com_scheme = get_induction_scheme(engine, "com")
    assert com_scheme is not None
    goals_ok.append(
        _prove_induction(
            "Theorem 3: Determinism of execution",
            r"forall c, s, s1, s2: exec(c,s)=s1 /\ exec(c,s)=s2 -> s1=s2",
            Clause(((exec_cmd(c, s), s1), (exec_cmd(c, s), s2)), eq(s1, s2), ()),
            engine,
            var=c,
            scheme=com_scheme,
            depth=16,
            induction_depth=1,
        )
    )
    goals_ok.append(
        _prove_rewrite(
            "Theorem 4: Assignment followed by skip",
            "forall x, e, s: exec(seq(assign(x,e), skip), s) = put(s, x, eval_a(e,s))",
            Clause(
                (),
                eq(exec_cmd(seq(assign(x, e), skip), s), put(s, x, eval_a(e, s))),
                (),
            ),
            engine,
            depth=10,
        )
    )
    goals_ok.append(
        _prove_rewrite(
            "Theorem 5: Sequential assignment",
            "forall x, y, e1, e2, s: exec(seq(assign(x,e1), assign(y,e2)), s) = put(put(s, x, eval_a(e1,s)), y, eval_a(e2, put(s, x, eval_a(e1,s))))",
            Clause(
                (),
                eq(
                    exec_cmd(seq(assign(x, e1), assign(y, e2)), s),
                    put(
                        put(s, x, eval_a(e1, s)),
                        y,
                        eval_a(e2, put(s, x, eval_a(e1, s))),
                    ),
                ),
                (),
            ),
            engine,
            depth=12,
        )
    )
    goals_ok.append(
        _prove_rewrite(
            "Theorem 6: While loop with false condition",
            "When b=false, while b do c = skip",
            Clause(
                (),
                eq(
                    exec_cmd(
                        while_cmd(
                            bconst(false),
                            assign(x, aadd(avar(x), aconst(succ(zero)))),
                        ),
                        s,
                    ),
                    s,
                ),
                (),
            ),
            engine,
            depth=20,
        )
    )
    goals_ok.append(
        _prove_rewrite(
            "Theorem 7: If-else true branch",
            "if true then c1 else c2 = c1",
            Clause(
                (), eq(exec_cmd(if_cmd(bconst(true), c1, c2), s), exec_cmd(c1, s)), ()
            ),
            engine,
            depth=8,
        )
    )
    goals_ok.append(
        _prove_rewrite(
            "Theorem 8: If-else false branch",
            "if false then c1 else c2 = c2",
            Clause(
                (), eq(exec_cmd(if_cmd(bconst(false), c1, c2), s), exec_cmd(c2, s)), ()
            ),
            engine,
            depth=8,
        )
    )

    print("\n=== Theorem 9: While loop with reducible blt condition ===")
    print("While blt(S(0), 0) do skip = skip (blt(S(0), 0) rewrites to false)")
    print("Manual proof using ProofSession:\n")

    while_blt_goal = Clause(
        (),
        eq(
            exec_cmd(while_cmd(blt(aconst(succ(zero)), aconst(zero)), skip), s),
            s,
        ),
        (),
    )

    session = ProofSession(while_blt_goal, engine)
    session.activate_scope("imp_def")

    session.rewrite_first("exec_while")
    session.simp()
    theorem_9_ok = session.qed()
    print(f"Proved: {theorem_9_ok}\n")

    print("\n=== Theorem 10: Hoare proof for sequence + conditional ===")
    print("{x=0} x:=1; if x<2 then x:=2 else x:=3 {x=2}")
    print("Manual proof using ProofSession:\n")

    theorem_10_goal = Clause(
        (),
        eq(
            hoare(
                aeq(x_id, zero),
                seq(
                    assign(x_id, aconst(one)),
                    if_cmd(
                        blt(avar(x_id), aconst(two)),
                        assign(x_id, aconst(two)),
                        assign(x_id, aconst(succ(two))),
                    ),
                ),
                aeq(x_id, two),
                put(empty, x_id, zero),
            ),
            true,
        ),
        (),
    )

    session = ProofSession(theorem_10_goal, engine)
    session.activate_scope("imp_def")

    session.rewrite_first("hoare_semantics")
    session.rewrite_first("holds_aeq")
    session.simp()
    theorem_10_ok = session.qed()
    print(f"Proved: {theorem_10_ok}\n")

    print("\n=== Theorem 11: Hoare proof of if-true ===")
    print("{x=1} if true then x:=2 else x:=3 {x=2}")
    print("Manual proof using ProofSession:\n")

    one = succ(zero)
    two = succ(one)
    initial_state = put(empty, x_id, zero)

    if_true_goal = Clause(
        (),
        eq(
            hoare(
                aeq(x_id, zero),
                if_cmd(
                    bconst(true),
                    assign(x_id, aconst(two)),
                    assign(x_id, aconst(succ(two))),
                ),
                aeq(x_id, two),
                initial_state,
            ),
            true,
        ),
        (),
    )

    session = ProofSession(if_true_goal, engine)
    session.activate_scope("imp_def")

    session.rewrite_first("hoare_semantics")
    session.rewrite_first("holds_aeq")
    session.simp()
    theorem_11_ok = session.qed()
    print(f"Proved: {theorem_11_ok}\n")

    print("\n=== Theorem 12: Hoare proof of while-loop with false condition ===")
    print("{P} while false do c {P} - loop never executes, invariant preserved")
    print("Manual proof using ProofSession:\n")

    initial_state = put(empty, x_id, zero)
    while_false_goal = Clause(
        (),
        eq(
            hoare(
                aeq(x_id, zero),
                while_cmd(bconst(false), assign(x_id, aconst(succ(zero)))),
                aeq(x_id, zero),
                initial_state,
            ),
            true,
        ),
        (),
    )

    session = ProofSession(while_false_goal, engine)
    session.activate_scope("imp_def")

    session.rewrite_first("hoare_semantics")
    session.rewrite_first("holds_aeq")
    session.simp()
    theorem_12_ok = session.qed()
    print(f"Proved: {theorem_12_ok}\n")

    print("\n=== Theorem 13: Hoare proof of while-loop with iteration ===")
    print("{x=0} while x<1 do x:=x+1 {x=1}")
    print("Manual proof using ProofSession:\n")

    one = succ(zero)
    initial_state = put(empty, x_id, zero)
    while_one_goal = Clause(
        (),
        eq(
            hoare(
                aeq(x_id, zero),
                while_cmd(
                    blt(avar(x_id), aconst(one)),
                    assign(x_id, aadd(avar(x_id), aconst(one))),
                ),
                aeq(x_id, one),
                initial_state,
            ),
            true,
        ),
        (),
    )

    session = ProofSession(while_one_goal, engine)
    session.activate_scope("imp_def")

    session.rewrite_first("hoare_semantics")
    session.rewrite_first("holds_aeq")
    session.simp()
    session.rewrite_first("exec_while")
    session.simp()
    session.rewrite_first("exec_while")
    session.simp()
    theorem_13_ok = session.qed()
    print(f"Proved: {theorem_13_ok}\n")

    print("\n=== Theorem 14: Execution of repeated assignment ===")
    print("exec(repeat_set(m, n), put(s, x=m)) = put(s, x=m)")
    print("Proof by induction on n:\n")

    m_repeat_nat = V("m_repeat_nat", "Nat")
    theorem_14_goal = Clause(
        (),
        eq(
            exec_cmd(repeat_set(m_repeat_nat, n), put(s, x_id, m_repeat_nat)),
            put(s, x_id, m_repeat_nat),
        ),
        (),
    )

    session = ProofSession(theorem_14_goal, engine)
    session.activate_scope("imp_def")
    session.induct(n)
    session.rewrite_first("def-repeat_set_zero")
    session.rewrite_first("exec_skip")
    session.simp()
    session.rewrite_first("def-repeat_set.0")
    session.rewrite_first("exec_seq")
    session.rewrite_first("exec_assign")
    session.rewrite_first("IH.0")
    session.simp()
    if session.goals:
        session.exact()
    theorem_14_ok = session.qed()
    print(f"Proved: {theorem_14_ok}\n")

    if (
        all(goals_ok)
        and theorem_9_ok
        and theorem_10_ok
        and theorem_11_ok
        and theorem_12_ok
        and theorem_13_ok
        and theorem_14_ok
    ):
        print("=== All theorems proved! ===")
    else:
        print("=== Some theorems failed! ===")


if __name__ == "__main__":
    main()
