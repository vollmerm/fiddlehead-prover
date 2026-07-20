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
    install_theory(engine, list_theory(), activate_scopes=True)

    eq = lambda a, b: App("eq", a, b)
    add = lambda a, b: App("add", a, b)
    append = lambda a, b: App("append", a, b)
    length = lambda t: App("length", t)

    xs = V("xs", "List")
    ys = V("ys", "List")

    goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))))
    list_scheme = get_induction_scheme(engine, "list")
    assert list_scheme is not None

    ok = prove(
        goal,
        engine,
        depth=14,
        var=xs,
        scheme=list_scheme,
        induction_depth=1,
    )
    assert ok
    print(render_proof_trace(ok.trace))


if __name__ == "__main__":
    main()
