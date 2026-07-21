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


    x_nat = V("x", "Nat")
    y_nat = V("y", "Nat")
    z_nat = V("z", "Nat")

    goal = Clause((), eq(add(add(x_nat, y_nat), z_nat), add(x_nat, add(y_nat, z_nat))))
    nat_scheme = get_induction_scheme(engine, "nat")
    assert nat_scheme is not None

    ok = prove(
        goal,
        engine,
        depth=12,
        var=x_nat,
        scheme=nat_scheme,
        induction_depth=1,
    )
    assert ok
    print(render_proof_trace(ok.trace))


if __name__ == "__main__":
    main()
