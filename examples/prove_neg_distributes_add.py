from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *


def run_proof(name: str, clause: Clause, engine: Engine, depth: int = 10, var=None, scheme=None) -> None:
    ok = prove(clause, engine, depth=depth, var=var, scheme=scheme)
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
    zneg = lambda t: App("zneg", t)
    zadd = lambda l, r: App("zadd", l, r)
    zmul = lambda l, r: App("zmul", l, r)
    zsucc = lambda t: App("zsucc", t)
    zpred = lambda t: App("zpred", t)

    x = V("x", "Int")
    y = V("y", "Int")

    int_scheme = get_induction_scheme(engine, "int")
    assert int_scheme is not None

    # ---------------------------------------------------------------
    # Show that normalization alone cannot prove the property.
    # When variables are abstract (not concrete zint pairs), the
    # rewrite engine has no rule for zneg(zadd(x, y)) and the goal
    # remains unchanged after normalization.
    # ---------------------------------------------------------------

    goal_neg_add = Clause((), eq(zneg(zadd(x, y)), zadd(zneg(x), zneg(y))))

    norm_neg_add = normalize(goal_neg_add.goal, engine)
    print("=== Normalization alone ===")
    print(f"Goal after normalize: {norm_neg_add}")
    print(f"Solved by normalization: {norm_neg_add == Const('true')}")

    # ---------------------------------------------------------------
    # INDUCTION PROOF 1
    #
    # Theorem:   zneg(zadd(x, y)) = zadd(zneg(x), zneg(y))
    #
    # Negation distributes over addition.  This is a fundamental ring
    # identity.  It requires induction because the rewrite engine
    # cannot unfold the abstract variable x to expose the internal
    # zint(pos, neg) representation that the zadd rules operate on.
    #
    # The induction uses the "int" scheme (base: z0; steps: zsucc, zpred).
    # Crucially, the int_theory now includes rules that push zsucc/zpred
    # through zadd and zneg, allowing the induction hypothesis to be
    # applied in the step cases via cross-fertilization.
    # ---------------------------------------------------------------

    run_proof(
        "zneg distributes over zadd (induction on x)",
        goal_neg_add,
        engine,
        depth=16,
        var=x,
        scheme=int_scheme,
    )

    # ---------------------------------------------------------------
    # INDUCTION PROOF 2
    #
    # Theorem:   zmul(x, zadd(y, z1)) = zadd(zmul(x, y), x)
    #
    # x * (y + 1) = x*y + x.  This is the right-distributivity of
    # multiplication over addition plus one, which follows from the
    # peano-style recursion for zmul.  Again, normalization alone
    # cannot reduce this when x is an abstract variable.
    # ---------------------------------------------------------------

    goal_mul_add = Clause((), eq(zmul(x, zadd(y, z1)), zadd(zmul(x, y), x)))

    norm_mul_add = normalize(goal_mul_add.goal, engine)
    print(f"\n=== Normalization alone ===")
    print(f"Goal after normalize: {norm_mul_add}")
    print(f"Solved by normalization: {norm_mul_add == Const('true')}")

    run_proof(
        "zmul(x, zadd(y, z1)) = zadd(zmul(x, y), x) (induction on x)",
        goal_mul_add,
        engine,
        depth=16,
        var=x,
        scheme=int_scheme,
    )

    print("\nAll proofs succeeded.")


if __name__ == "__main__":
    main()
