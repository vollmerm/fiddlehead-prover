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
    install_theory(engine, tree_theory(), activate_scopes=True)
    register_induction_scheme(engine, tree_induction_scheme())

    env = get_theorem_environment(engine)

    t = V("t", "Tree")
    l = V("l", "Tree")
    r = V("r", "Tree")
    v = V("v")
    w = V("w")

    zero = Const("0")
    succ = lambda n: App("S", n)

    leaf = Const("leaf")
    node = lambda l, v, r: App("node", l, v, r)
    eq = lambda a, b: App("eq", a, b)

    mirror = lambda t: App("mirror", t)
    size = lambda t: App("size", t)
    add = lambda a, b: App("add", a, b)

    register_sort_signature(
        engine,
        "mirror",
        SortSignature(
            (TypeConst("Tree", (TypeVar("A"),)),), TypeConst("Tree", (TypeVar("A"),))
        ),
    )
    engine.config.precedence["mirror"] = 5

    register_sort_signature(
        engine,
        "size",
        SortSignature((TypeConst("Tree", (TypeVar("A"),)),), TypeConst("Nat")),
    )
    engine.config.precedence["size"] = 5

    engine.reset_rules(
        engine.rules
        + [Rule(mirror(leaf), leaf)]
        + [Rule(mirror(node(l, v, r)), node(mirror(r), v, mirror(l)))]
        + [Rule(size(leaf), zero)]
        + [Rule(size(node(l, v, r)), succ(add(size(l), size(r))))]
    )

    print("=== Binary Tree Mirror Properties ===\n")

    print("Definitions registered:")
    print("  mirror(leaf) -> leaf")
    print("  mirror(node(l, v, r)) -> node(mirror(r), v, mirror(l))")
    print("  size(leaf) -> 0")
    print("  size(node(l, v, r)) -> S(add(size(l), size(r)))\n")

    print("Theorem 1: mirror(mirror(t)) = t  (mirror is an involution)")
    print("  Proof by induction on t")
    goal1 = Clause((), eq(mirror(mirror(t)), t), ())
    tree_scheme = get_induction_scheme(engine, "tree")
    assert tree_scheme is not None
    ok1 = prove(
        goal1, engine, var=t, scheme=tree_scheme, depth=12, induction_depth=1
    )
    print(f"  Proved: {ok1}")
    print()

    print("Theorem 2: size(mirror(t)) = size(t)  (mirror preserves size)")
    print("  Proof by induction on t")
    goal2 = Clause((), eq(size(mirror(t)), size(t)), ())
    ok2 = prove(
        goal2, engine, var=t, scheme=tree_scheme, depth=12, induction_depth=1
    )
    print(f"  Proved: {ok2}")
    print()

    print("Theorem 3: mirror(node(leaf, v, leaf)) = node(leaf, v, leaf)  (single node)")
    goal3 = Clause((), eq(mirror(node(leaf, v, leaf)), node(leaf, v, leaf)), ())
    ok3, trace3 = prove_with_trace(goal3, engine, depth=8)
    print(f"  Proved: {ok3}")
    if ok3:
        print(f"  Simplified to: {goal3.goal} -> true")
    print()

    if ok1 and ok2 and ok3:
        print("=== All theorems proved! ===")
    else:
        print("=== Some theorems failed! ===")


if __name__ == "__main__":
    main()
