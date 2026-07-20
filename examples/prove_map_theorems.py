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
    install_theory(engine, map_theory(), activate_scopes=True)

    m = V("m", "Map")
    k = V("k")
    k1 = V("k1")
    k2 = V("k2")
    v = V("v")
    v1 = V("v1")
    v2 = V("v2")

    eq = lambda a, b: App("eq", a, b)
    put = lambda m, k, v: App("put", m, k, v)
    get = lambda m, k: App("get", m, k)
    some = lambda x: App("some", x)
    none = Const("none")
    empty = Const("empty")

    print("=== Finite Map Theory Demo ===\n")

    print("1. get(empty, k) = none")
    goal1 = Clause((), eq(get(empty, k), none), ())
    ok1 = prove(goal1, engine, depth=8)
    print(f"   Proved: {ok1}\n")

    print("2. get(put(m, k, v), k) = some(v)")
    goal2 = Clause((), eq(get(put(m, k, v), k), some(v)), ())
    ok2 = prove(goal2, engine, depth=8)
    print(f"   Proved: {ok2}\n")

    print(
        "3. get(put(put(m, k2, v2), k1, v1), k1) = some(v1)  [unrelated writes reordered]"
    )
    goal3 = Clause((), eq(get(put(put(m, k2, v2), k1, v1), k1), some(v1)), ())
    ok3 = prove(goal3, engine, depth=8)
    print(f"   Proved: {ok3}\n")

    print("4. get(put(put(m, k1, v1), k2, v2), k1) = some(v1)  [requires k2 != k1]")
    goal4 = Clause((), eq(get(put(put(m, k1, v1), k2, v2), k1), some(v1)), ((k2, k1),))
    ok4 = prove(goal4, engine, depth=8)
    print(f"   Proved with k2 != k1: {ok4}\n")

    print(
        "5. Case splitting: get(put(m, k1, v1), k2) simplifies to if(eq(k1,k2), some(v1), get(m,k2))"
    )
    goal5 = Clause((), eq(get(put(m, k1, v1), k2), some(v1)), ())
    simp5 = simplify_clause(goal5, engine)
    lhs = simp5.goal.args[0]
    print(f"   LHS after simplify: {lhs}")
    print(f"   Is if expression: {lhs.symbol == 'if'}\n")


if __name__ == "__main__":
    main()
