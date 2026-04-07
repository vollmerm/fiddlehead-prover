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

    n = V("n", "Nat")
    zero = Const("0")
    succ = lambda t: App("S", t)
    add = lambda a, b: App("add", a, b)
    eq = lambda a, b: App("eq", a, b)
    twice = lambda t: App("twice", t)

    register_recursive_definition(
        engine,
        "twice",
        (
            (twice(zero), zero),
            (twice(succ(n)), succ(succ(twice(n)))),
        ),
        signature=SortSignature((TypeConst("Nat"),), TypeConst("Nat")),
        precedence=5,
        scope="twice_def",
    )
    get_theorem_environment(engine).activate_scope("twice_def")

    print("=== Recursive function theorem: twice(n) = add(n, n) ===\n")
    print("Definitions registered:")
    print("  twice(0) = 0")
    print("  twice(S(n)) = S(S(twice(n)))\n")

    sample = twice(succ(succ(zero)))
    print(f"Sample normalization: {sample} -> {normalize(sample, engine)}\n")

    goal = Clause((), eq(twice(n), add(n, n)), ())
    nat_scheme = get_induction_scheme(engine, "nat")
    assert nat_scheme is not None
    ok, trace = prove_with_trace(
        goal,
        engine,
        depth=14,
        var=n,
        scheme=nat_scheme,
        induction_depth=1,
    )
    print("Theorem: forall n, twice(n) = add(n, n)")
    print(f"Proved by induction: {ok}\n")
    if ok:
        print(render_proof_trace(trace))
    assert ok


if __name__ == "__main__":
    main()
