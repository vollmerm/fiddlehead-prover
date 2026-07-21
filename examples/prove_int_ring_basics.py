from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *


def run_proof(name: str, clause: Clause, engine: Engine, depth: int = 10) -> None:
    ok = prove(clause, engine, depth=depth)
    print(f"\n=== {name} ===")
    print("Goal:", clause.goal)
    print("Proved:", ok)
    assert ok, f"Expected proof to succeed: {name}"
    print(render_proof_trace(ok.trace))


def main() -> None:
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, int_theory(), activate_scopes=True)

    zadd = lambda a, b: App("zadd", a, b)
    zmul = lambda a, b: App("zmul", a, b)
    zneg = lambda t: App("zneg", t)

    z0 = Const("z0")
    z1 = Const("z1")
    x = V("x", "Int")
    y = V("y", "Int")
    a = V("a", "Int")
    b = V("b", "Int")
    c = V("c", "Int")

    run_proof("zadd commutativity (AC)", Clause((), eq(zadd(x, y), zadd(y, x))), engine)
    run_proof("zmul commutativity (AC)", Clause((), eq(zmul(x, y), zmul(y, x))), engine)
    run_proof(
        "contextual congruence with EqClasses",
        Clause(((a, b),), eq(zadd(a, c), zadd(b, c))),
        engine,
    )
    run_proof(
        "concrete additive inverse: 1 + (-1) = 0",
        Clause((), eq(zadd(z1, zneg(z1)), z0)),
        engine,
    )
    run_proof(
        "double negation on 1",
        Clause((), eq(zneg(zneg(z1)), z1)),
        engine,
    )


if __name__ == "__main__":
    main()
