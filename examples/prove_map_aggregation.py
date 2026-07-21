from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *
from fiddlehead.prover import TypeVar, map_induction_scheme


def main() -> None:
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, map_theory(), activate_scopes=True)
    register_induction_scheme(engine, map_induction_scheme())

    m = V("m", "Map")
    k = V("k")
    k1 = V("k1")
    k2 = V("k2")
    n = V("n", "Nat")
    n1 = V("n1", "Nat")
    n2 = V("n2", "Nat")
    zero = Const("0")
    succ = lambda t: App("S", t)

    put = lambda m, k, v: App("put", m, k, v)
    get = lambda m, k: App("get", m, k)
    some = lambda x: App("some", x)
    empty = Const("empty")
    sum_entries = lambda m: App("sum_entries", m)

    register_recursive_definition(
        engine,
        "sum_entries",
        (
            (sum_entries(empty), zero),
            (sum_entries(put(m, k, n)), add(n, sum_entries(m))),
        ),
        signature=SortSignature(
            (TypeConst("Map", (TypeVar("K"), TypeConst("Nat"))),),
            TypeConst("Nat"),
        ),
        precedence=5,
        scope="map_aggregation",
    )
    get_theorem_environment(engine).activate_scope("map_aggregation")

    print("=== Map Aggregation with Induction ===\n")

    print("Definitions registered:")
    print("  sum_entries(empty) = 0")
    print("  sum_entries(put(m, k, n)) = add(n, sum_entries(m))\n")

    print("Theorem 1: sum_entries(put(empty, k, n)) = n  (single entry sum)")
    goal1 = Clause((), eq(sum_entries(put(empty, k, n)), n), ())
    ok1 = prove(goal1, engine, depth=8)
    print(f"  Proved: {ok1}")
    if ok1:
        print(f"  Simplified to: {goal1.goal} -> true")
    print()

    print(
        "Theorem 2: sum_entries(put(put(m, k2, n2), k1, n1)) = add(n1, sum_entries(put(m, k2, n2)))"
    )
    print("  (reordering unrelated writes)")
    goal2 = Clause(
        (),
        eq(
            sum_entries(put(put(m, k2, n2), k1, n1)),
            add(n1, sum_entries(put(m, k2, n2))),
        ),
        (),
    )
    ok2 = prove(goal2, engine, depth=10)
    print(f"  Proved: {ok2}")
    print()

    print(
        "Theorem 3: sum_entries(put(m, k, 0)) = sum_entries(m)  [adding zero doesn't change sum]"
    )
    print("  Proof by induction on m")
    goal3 = Clause((), eq(sum_entries(put(m, k, zero)), sum_entries(m)), ())
    map_scheme = get_induction_scheme(engine, "map")
    assert map_scheme is not None
    ok3 = prove(
        goal3, engine, var=m, scheme=map_scheme, depth=12, induction_depth=1
    )
    print(f"  Proved: {ok3}")
    print()

    print(
        "Theorem 4: sum_entries(put(put(m, k2, n2), k1, n1)) = add(n1, add(n2, sum_entries(m)))"
    )
    print("  (full reordering - follows from associativity of add)")
    goal4 = Clause(
        (),
        eq(sum_entries(put(put(m, k2, n2), k1, n1)), add(n1, add(n2, sum_entries(m)))),
        (),
    )
    ok4 = prove(goal4, engine, depth=12)
    print(f"  Proved: {ok4}")
    print()

    if ok1 and ok2 and ok3 and ok4:
        print("=== All theorems proved! ===")
    else:
        print("=== Some theorems failed! ===")


if __name__ == "__main__":
    main()
