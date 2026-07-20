from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *


def main() -> None:
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, map_theory(), activate_scopes=True)

    a = TypeVar("A")
    k = TypeVar("K")
    v = TypeVar("V")
    x = V("x")
    n = V("n", "Nat")
    s = V("s", "Map")
    zero = Const("0")
    succ = lambda t: App("S", t)
    add = lambda a, b: App("add", a, b)
    eq = lambda a, b: App("eq", a, b)
    get = lambda m, k: App("get", m, k)
    put = lambda m, k, val: App("put", m, k, val)
    some = lambda x: App("some", x)
    none = Const("none")
    empty = Const("empty")
    true = Const("true")
    false = Const("false")
    nat_of = lambda opt: App("nat_of", opt)

    aconst = lambda n: App("aconst", n)
    avar = lambda v: App("avar", v)
    aadd = lambda a1, a2: App("aadd", a1, a2)
    asub = lambda a1, a2: App("asub", a1, a2)

    bconst = lambda b: App("bconst", b)
    beq = lambda a1, a2: App("beq", a1, a2)
    blt = lambda a1, a2: App("blt", a1, a2)
    band = lambda b1, b2: App("band", b1, b2)

    skip = Const("skip")
    assign = lambda v, a: App("assign", v, a)
    seq = lambda c1, c2: App("seq", c1, c2)
    if_cmd = lambda b, c1, c2: App("if_cmd", b, c1, c2)
    while_cmd = lambda b, c: App("while_cmd", b, c)

    eval_a = lambda e, st: App("eval_a", e, st)
    eval_b = lambda e, st: App("eval_b", e, st)
    exec_cmd = lambda c, st: App("exec", c, st)

    e1 = V("e1", "AExp")
    e2 = V("e2", "AExp")
    e = V("e", "AExp")
    b = V("b", "BExp")
    b1 = V("b1", "BExp")
    b2 = V("b2", "BExp")
    c1 = V("c1", "Com")
    c2 = V("c2", "Com")
    c = V("c", "Com")

    engine.sort_arities["AExp"] = 0
    engine.sort_arities["BExp"] = 0
    engine.sort_arities["Com"] = 0

    register_sort_signature(
        engine, "aconst", SortSignature((TypeConst("Nat"),), TypeConst("AExp"))
    )
    engine.config.precedence["aconst"] = 5
    register_sort_signature(engine, "avar", SortSignature((a,), TypeConst("AExp")))
    engine.config.precedence["avar"] = 5
    register_sort_signature(
        engine,
        "aadd",
        SortSignature((TypeConst("AExp"), TypeConst("AExp")), TypeConst("AExp")),
    )
    engine.config.precedence["aadd"] = 3
    register_sort_signature(
        engine,
        "asub",
        SortSignature((TypeConst("AExp"), TypeConst("AExp")), TypeConst("AExp")),
    )
    engine.config.precedence["asub"] = 3

    register_sort_signature(
        engine, "bconst", SortSignature((TypeConst("Bool"),), TypeConst("BExp"))
    )
    engine.config.precedence["bconst"] = 5
    register_sort_signature(
        engine,
        "beq",
        SortSignature((TypeConst("AExp"), TypeConst("AExp")), TypeConst("BExp")),
    )
    engine.config.precedence["beq"] = 4
    register_sort_signature(
        engine,
        "blt",
        SortSignature((TypeConst("AExp"), TypeConst("AExp")), TypeConst("BExp")),
    )
    engine.config.precedence["blt"] = 4
    register_sort_signature(
        engine,
        "band",
        SortSignature((TypeConst("BExp"), TypeConst("BExp")), TypeConst("BExp")),
    )
    engine.config.precedence["band"] = 3

    register_sort_signature(engine, "skip", SortSignature((), TypeConst("Com")))
    engine.config.precedence["skip"] = 1
    register_sort_signature(
        engine,
        "assign",
        SortSignature((a, TypeConst("AExp")), TypeConst("Com")),
    )
    engine.config.precedence["assign"] = 1
    register_sort_signature(
        engine,
        "seq",
        SortSignature((TypeConst("Com"), TypeConst("Com")), TypeConst("Com")),
    )
    engine.config.precedence["seq"] = 2
    register_sort_signature(
        engine,
        "if_cmd",
        SortSignature(
            (TypeConst("BExp"), TypeConst("Com"), TypeConst("Com")), TypeConst("Com")
        ),
    )
    engine.config.precedence["if_cmd"] = 1
    register_sort_signature(
        engine,
        "while_cmd",
        SortSignature((TypeConst("BExp"), TypeConst("Com")), TypeConst("Com")),
    )
    engine.config.precedence["while_cmd"] = 1

    register_sort_signature(
        engine,
        "eval_a",
        SortSignature((TypeConst("AExp"), TypeConst("Map", (k, v))), TypeConst("Nat")),
    )
    engine.config.precedence["eval_a"] = 5
    register_sort_signature(
        engine,
        "eval_b",
        SortSignature((TypeConst("BExp"), TypeConst("Map", (k, v))), TypeConst("Bool")),
    )
    engine.config.precedence["eval_b"] = 5
    register_sort_signature(
        engine,
        "exec",
        SortSignature(
            (TypeConst("Com"), TypeConst("Map", (k, v))), TypeConst("Map", (k, v))
        ),
    )
    engine.config.precedence["exec"] = 5
    register_sort_signature(
        engine,
        "nat_of",
        SortSignature((TypeConst("Option", (TypeConst("Nat"),)),), TypeConst("Nat")),
    )
    engine.config.precedence["nat_of"] = 5

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
    get_theorem_environment(engine).activate_scope("imp_def")

    eval_avar_rule = Rule(eval_a(avar(x), s), nat_of(get(s, x)))
    get_theorem_environment(engine).register_rule(
        eval_avar_rule, scope="imp_def", label="eval_avar"
    )

    exec_skip_rule = Rule(exec_cmd(skip, s), s, skip_decrease_check=True)
    exec_assign_rule = Rule(
        exec_cmd(assign(x, e), s), put(s, x, eval_a(e, s)), skip_decrease_check=True
    )
    exec_seq_rule = Rule(exec_cmd(seq(c1, c2), s), exec_cmd(c2, exec_cmd(c1, s)))
    exec_if_true_rule = Rule(exec_cmd(if_cmd(bconst(true), c1, c2), s), exec_cmd(c1, s))
    exec_if_false_rule = Rule(
        exec_cmd(if_cmd(bconst(false), c1, c2), s), exec_cmd(c2, s)
    )
    exec_while_rule = Rule(
        exec_cmd(while_cmd(b, c), s),
        App("if", eval_b(b, s), exec_cmd(while_cmd(b, c), exec_cmd(c, s)), s),
    )

    env = get_theorem_environment(engine)
    env.register_rule(exec_skip_rule, scope="imp_def", label="exec_skip")
    env.register_rule(exec_assign_rule, scope="imp_def", label="exec_assign")
    env.register_rule(exec_seq_rule, scope="imp_def", label="exec_seq")
    env.register_rule(exec_if_true_rule, scope="imp_def", label="exec_if_true")
    env.register_rule(exec_if_false_rule, scope="imp_def", label="exec_if_false")
    env.register_rule(exec_while_rule, scope="imp_def", label="exec_while")

    env._sync_engine_rules()

    com_induction_scheme = InductionScheme(
        name="com",
        sort="Com",
        base_terms=(skip,),
        constructors=(
            InductionConstructor("assign", 2, ()),
            InductionConstructor("seq", 2, (0, 1)),
            InductionConstructor("if_cmd", 3, (1, 2)),
            InductionConstructor("while_cmd", 2, (1,)),
        ),
    )
    register_induction_scheme(engine, com_induction_scheme)

    print("=== Simple Imperative Language Interpreter ===\n")

    print("Language constructors:")
    print("  AExp:  aconst(n), avar(x), aadd(e1,e2), asub(e1,e2)")
    print("  BExp:  bconst(b), beq(e1,e2), blt(e1,e2), band(b1,b2)")
    print("  Com:   skip, assign(x,e), seq(c1,c2), if_cmd(b,c1,c2), while_cmd(b,c)")

    print("\nInterpreter definitions:")
    print("  eval_a(aconst(n), s) -> n")
    print("  eval_a(avar(x), s) -> nat_of(get(s, x))")
    print("  eval_a(aadd(e1,e2), s) -> add(eval_a(e1,s), eval_a(e2,s))")
    print("  eval_a(asub(e1,e2), s) -> eval_a(e1, s)")
    print("  exec(skip, s) -> s")
    print("  exec(assign(x,e), s) -> put(s, x, eval_a(e,s))")
    print("  exec(seq(c1,c2), s) -> exec(c2, exec(c1,s))")
    print("  exec(if_cmd(true,c1,c2), s) -> exec(c1, s)")
    print("  exec(if_cmd(false,c1,c2), s) -> exec(c2, s)")
    print(
        "  exec(while_cmd(b,c), s) -> if(eval_b(b,s), exec(while_cmd(b,c), exec(c,s)), s)"
    )

    s1 = V("s1", "Map")
    s2 = V("s2", "Map")

    print("\n=== Theorem 1: Determinism ===")
    print(r"forall c, s, s1, s2: exec(c,s)=s1 /\ exec(c,s)=s2 -> s1=s2")
    print("Proof by induction on c\n")

    det_goal = Clause(
        (
            (exec_cmd(c, s), s1),
            (exec_cmd(c, s), s2),
        ),
        eq(s1, s2),
        (),
    )

    com_scheme = get_induction_scheme(engine, "com")
    assert com_scheme is not None
    ok1 = prove(
        det_goal, engine, var=c, scheme=com_scheme, depth=16, induction_depth=1
    )
    print(f"Proved: {ok1}\n")

    print("=== Theorem 2: State Extension for Assign ===")
    print("forall x, e, s: get(exec(assign(x,e), s), x) = some(eval_a(e, s))")
    print("Proof by rewriting (no induction needed)\n")

    ext_goal = Clause((), eq(get(exec_cmd(assign(x, e), s), x), some(eval_a(e, s))), ())
    ok2 = prove(ext_goal, engine, depth=10)
    print(f"Proved: {ok2}")
    if ok2:
        print(f"Simplified to: {ext_goal.goal} -> true")
    print()

    if ok1 and ok2:
        print("=== All theorems proved! ===")
    else:
        print("=== Some theorems failed! ===")


if __name__ == "__main__":
    main()
