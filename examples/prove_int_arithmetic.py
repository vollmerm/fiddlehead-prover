from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *


def run_proof(
    name: str, clause: Clause, engine: Engine, depth: int = 10, var=None, scheme=None
) -> None:
    ok = prove(
        clause, engine, depth=depth, var=var, scheme=scheme
    )
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

    z0 = Const("z0")
    z1 = Const("z1")
    zadd = lambda l, r: App("zadd", l, r)
    zmul = lambda l, r: App("zmul", l, r)
    zneg = lambda t: App("zneg", t)
    zsucc = lambda t: App("zsucc", t)
    zpred = lambda t: App("zpred", t)
    zsub = lambda l, r: App("zsub", l, r)
    znonneg = lambda t: App("znonneg", t)
    zleq = lambda l, r: App("zleq", l, r)
    zlt = lambda l, r: App("zlt", l, r)

    x = V("x", "Int")
    y = V("y", "Int")
    z = V("z", "Int")

    # ---- Rewriting / normalization ----

    print("=== Integer rewrites ===")
    print(f"zsucc(z0)      = {normalize(zsucc(z0), engine)}")
    print(f"zpred(z0)      = {normalize(zpred(z0), engine)}")
    print(f"zsucc(zpred(z0)) = {normalize(zsucc(zpred(z0)), engine)}")
    print(f"zsub(z1, z0)   = {normalize(zsub(z1, z0), engine)}")
    print(f"znonneg(z0)    = {normalize(znonneg(z0), engine)}")
    print(f"znonneg(z1)    = {normalize(znonneg(z1), engine)}")
    print(f"zneg(zsucc(z0))= {normalize(zneg(zsucc(z0)), engine)}")
    print(f"zneg(zneg(zsucc(z0))) = {normalize(zneg(zneg(zsucc(z0))), engine)}")

    # ---- AC properties (commutativity of zadd, zmul) ----

    int_scheme = get_induction_scheme(engine, "int")
    assert int_scheme is not None

    run_proof(
        "zadd commutativity",
        Clause((), eq(zadd(x, y), zadd(y, x))),
        engine,
        depth=8,
    )

    run_proof(
        "zmul commutativity",
        Clause((), eq(zmul(x, y), zmul(y, x))),
        engine,
        depth=8,
    )

    # ---- Induction proofs ----

    run_proof(
        "zneg involutive",
        Clause((), eq(zneg(zneg(x)), x)),
        engine,
        depth=12,
        var=x,
        scheme=int_scheme,
    )

    run_proof(
        "zadd identity (by induction)",
        Clause((), eq(zadd(x, z0), x)),
        engine,
        depth=12,
        var=x,
        scheme=int_scheme,
    )

    # ---- Packaged lemmas ----

    lemma_names = register_int_lemmas(engine, depth=12, induction_depth=2)
    print(f"\nRegistered lemmas: {lemma_names}")

    run_proof(
        "zadd associativity (via lemma rewrite)",
        Clause((), eq(zadd(zadd(x, y), z), zadd(x, zadd(y, z)))),
        engine,
        depth=4,
    )

    run_proof(
        "zneg involutive (via lemma rewrite)",
        Clause((), eq(zneg(zneg(x)), x)),
        engine,
        depth=4,
    )

    # ---- Ordering normalization ----

    print("\n=== Ordering ===")
    print(f"zleq(z0, z1)  = {normalize(zleq(z0, z1), engine)}")
    print(f"zlt(z0, z1)   = {normalize(zlt(z0, z1), engine)}")
    print(f"zleq(z0, z0)  = {normalize(zleq(z0, z0), engine)}")

    print("\nAll proofs succeeded.")


if __name__ == "__main__":
    main()
