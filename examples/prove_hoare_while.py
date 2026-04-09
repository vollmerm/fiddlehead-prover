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
    ok = prove_with_induction(
        goal,
        engine,
        var,
        scheme,
        depth=depth,
        induction_depth=induction_depth,
    )
    print(f"Proved: {ok}")
    return ok


def main() -> None:
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
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
        SortSignature((TypeConst("Assert"), TypeConst("Map", (k, v))), TypeConst("Bool")),
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
    env.register_rule(Rule(eval_a(avar(x), s), nat_of(get(s, x))), "imp_def", "eval_avar")
    env.register_rule(
        Rule(
            eval_a(avar(x_id), s),
            nat_of(get(s, x_id)),
            skip_decrease_check=True,
        ),
        "imp_def",
        "eval_avar_x_id",
    )
    env.register_rule(
        Rule(nat_of(some(n)), n, skip_decrease_check=True),
        "imp_def",
        "nat_of_some",
    )
    env.register_rule(
        Rule(nat_of(none), zero, skip_decrease_check=True),
        "imp_def",
        "nat_of_none",
    )
    env.register_rule(Rule(exec_cmd(skip, s), s, skip_decrease_check=True), "imp_def", "exec_skip")
    env.register_rule(
        Rule(exec_cmd(assign(x, e), s), put(s, x, eval_a(e, s)), skip_decrease_check=True),
        "imp_def",
        "exec_assign",
    )
    env.register_rule(
        Rule(exec_cmd(seq(c1, c2), s), exec_cmd(c2, exec_cmd(c1, s))),
        "imp_def",
        "exec_seq",
    )
    env.register_rule(
        Rule(
            exec_cmd(if_cmd(bh, c1, c2), s),
            if_term(eval_b(bh, s), exec_cmd(c1, s), exec_cmd(c2, s)),
            skip_decrease_check=True,
        ),
        "imp_def",
        "exec_if",
    )
    env.register_rule(
        Rule(exec_cmd(if_cmd(bconst(true), c1, c2), s), exec_cmd(c1, s)),
        "imp_def",
        "exec_if_true",
    )
    env.register_rule(
        Rule(exec_cmd(if_cmd(bconst(false), c1, c2), s), exec_cmd(c2, s)),
        "imp_def",
        "exec_if_false",
    )
    env.register_rule(
        Rule(
            exec_cmd(while_cmd(bh, ch), s),
            if_term(
                eval_b(bh, s),
                exec_cmd(while_cmd(bh, ch), exec_cmd(ch, s)),
                s,
            ),
            skip_decrease_check=True,
        ),
        "imp_def",
        "exec_while",
    )
    env.register_rule(
        Rule(eval_b(bconst(true), s), true, skip_decrease_check=True),
        "imp_def",
        "eval_b_const_true",
    )
    env.register_rule(
        Rule(eval_b(bconst(false), s), false, skip_decrease_check=True),
        "imp_def",
        "eval_b_const_false",
    )
    env.register_rule(
        Rule(
            eval_b(blt(V("e1h"), V("e2h")), s),
            blt_nat(eval_a(V("e1h"), s), eval_a(V("e2h"), s)),
            skip_decrease_check=True,
        ),
        "imp_def",
        "eval_b_blt",
    )
    env.register_rule(Rule(blt_nat(zero, zero), false), "imp_def", "blt_nat_zero_zero")
    env.register_rule(
        Rule(blt_nat(zero, succ(V("n_nat"))), true),
        "imp_def",
        "blt_nat_zero_succ",
    )
    env.register_rule(
        Rule(blt_nat(succ(V("n_nat2")), zero), false),
        "imp_def",
        "blt_nat_succ_zero",
    )
    env.register_rule(
        Rule(blt_nat(succ(V("n_nat3")), succ(V("m_nat"))), blt_nat(V("n_nat3"), V("m_nat"))),
        "imp_def",
        "blt_nat_succ_succ",
    )
    refl_nat = V("k_nat")
    env.register_rule(
        Rule(blt_nat(refl_nat, refl_nat), false, skip_decrease_check=True),
        "imp_def",
        "blt_nat_refl",
    )
    env.register_rule(
        Rule(
            holds(and_a(p_assert, q_assert), s),
            App("and", holds(p_assert, s), holds(q_assert, s)),
            skip_decrease_check=True,
        ),
        "imp_def",
        "holds_and",
    )
    env.register_rule(
        Rule(
            holds(not_a(p_assert), s),
            App("not", holds(p_assert, s)),
            skip_decrease_check=True,
        ),
        "imp_def",
        "holds_not",
    )
    env.register_rule(
        Rule(holds(bassn(guard), s), eval_b(guard, s), skip_decrease_check=True),
        "imp_def",
        "holds_bassn",
    )
    env.register_rule(
        Rule(holds(aeq(x, n), s), eq(get(s, x), some(n)), skip_decrease_check=True),
        "imp_def",
        "holds_aeq",
    )
    one = succ(zero)
    two = succ(one)
    env.register_rule(
        Rule(
            hoare(p_assert, c, q_assert, s),
            if_term(holds(p_assert, s), holds(q_assert, exec_cmd(c, s)), true),
            skip_decrease_check=True,
        ),
        "imp_def",
        "hoare_semantics",
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
            Clause((), eq(exec_cmd(seq(assign(x, e), skip), s), put(s, x, eval_a(e, s))), ()),
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
                    put(put(s, x, eval_a(e1, s)), y, eval_a(e2, put(s, x, eval_a(e1, s)))),
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
            Clause((), eq(exec_cmd(if_cmd(bconst(true), c1, c2), s), exec_cmd(c1, s)), ()),
            engine,
            depth=8,
        )
    )
    goals_ok.append(
        _prove_rewrite(
            "Theorem 8: If-else false branch",
            "if false then c1 else c2 = c2",
            Clause((), eq(exec_cmd(if_cmd(bconst(false), c1, c2), s), exec_cmd(c2, s)), ()),
            engine,
            depth=8,
        )
    )
    goals_ok.append(
        _prove_rewrite(
            "Theorem 9: While loop with reducible blt condition",
            "While blt(S(0), 0) do skip = skip (blt(S(0), 0) rewrites to false)",
            Clause(
                (),
                eq(exec_cmd(while_cmd(blt(aconst(succ(zero)), aconst(zero)), skip), s), s),
                (),
            ),
            engine,
            depth=20,
        )
    )
    goals_ok.append(
        _prove_hoare(
            "Theorem 10: Hoare proof for sequence + conditional",
            "{x=0} x:=1; if x<2 then x:=2 else x:=3 {x=2}",
            Clause(
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
            ),
            engine,
            depth=24,
        )
    )

    if all(goals_ok):
        print("\n=== All theorems proved! ===")
    else:
        print("\n=== Some theorems failed! ===")


if __name__ == "__main__":
    main()
