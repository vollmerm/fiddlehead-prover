from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *
from fiddlehead.prover import TypeVar, clause_solved
from fiddlehead.proof import (
    Clause,
    clause_solved,
    fertilize_clause,
    simplify_clause,
)
from fiddlehead.generalize import destructor_elim_clause


def demo_destructor_elimination(engine) -> None:
    """Show what destructor_elim_clause does to a goal with head/tail."""

    print("=" * 65)
    print("Demo: Destructor Elimination")
    print("=" * 65)

    reset_var_interner()

    xs = V("xs", "List")
    h = V("hd")
    t = V("tl", "List")
    nil = Const("nil")
    head = lambda x: App("head", x)
    tail = lambda x: App("tail", x)

    # Register head and tail as selector rules
    theory = get_theorem_environment(engine)
    hv = V("head_h")
    tv = V("head_t", "List")
    theory.register_recursive_definition(
        "head",
        ((head(cons(hv, tv)), hv),),
        scope="selectors",
        signature=SortSignature(
            (TypeConst("List", (TypeVar("A"),)),), TypeVar("A")
        ),
    )
    theory.register_recursive_definition(
        "tail",
        ((tail(cons(hv, tv)), tv),),
        scope="selectors",
        signature=SortSignature(
            (TypeConst("List", (TypeVar("A"),)),),
            TypeConst("List", (TypeVar("A"),)),
        ),
    )
    theory.activate_scope("selectors")

    list_scheme = get_induction_scheme(engine, "list")
    assert list_scheme is not None

    # -----------------------------------------------------------------------
    # Goal with head(xs) and tail(xs): DE should replace them with fresh vars
    # -----------------------------------------------------------------------
    clause = Clause(
        assumptions=(),
        goal=eq(add(length(tail(xs)), length(tail(xs))), length(xs)),
    )

    print(f"  Original goal:  {clause.goal}")

    de_result = destructor_elim_clause(clause, xs, list_scheme, engine)
    if de_result is not None:
        print(f"  After DE goal:  {de_result.goal}")
        print(f"  New assumptions (pinning fresh vars):")
        for lhs, rhs in de_result.assumptions:
            print(f"    {lhs} = {rhs}")
    else:
        print("  (DE did not fire — no destructor applications found)")

    # -----------------------------------------------------------------------
    # Simulate what happens in the step case (xs → cons(h_arg, xs_ih))
    # -----------------------------------------------------------------------
    if de_result is not None:
        h_arg = V("h_arg")
        xs_ih = V("xs_ih", "List")
        subst = {xs: cons(h_arg, xs_ih)}

        from fiddlehead.proof import instantiate_clause

        step_clause = instantiate_clause(de_result, subst)
        simplified_step = simplify_clause(step_clause, engine)

        print(f"\n  In the step case (xs → cons(h_arg, xs_ih)):")
        print(f"  Step assumptions:")
        for lhs, rhs in simplified_step.assumptions:
            print(f"    {lhs} = {rhs}")
        print(f"  Step goal: {simplified_step.goal}")
        print("  => Fresh vars are now bound to h_arg and xs_ih (concrete values)")

    print()


def demo_fertilization(engine) -> None:
    """Show fertilize_clause finding and applying an IH substitution."""

    print("=" * 65)
    print("Demo: Cross-Fertilization")
    print("=" * 65)

    xs_ih = V("xs_ih_fert", "List")
    ys = V("ys_fert", "List")
    zs = V("zs_fert", "List")
    h_var = V("h_fert")

    # Mimic the step clause from the append-assoc induction proof.
    # IH: append(append(xs_ih, ys), zs) = append(xs_ih, append(ys, zs))
    ih_lhs = append(append(xs_ih, ys), zs)
    ih_rhs = append(xs_ih, append(ys, zs))

    # The step goal after simplification of append(cons(h, xs_ih), ys):
    # eq(cons(h, append(append(xs_ih, ys), zs)), cons(h, append(xs_ih, append(ys, zs))))
    step_goal = eq(
        cons(h_var, append(append(xs_ih, ys), zs)),
        cons(h_var, append(xs_ih, append(ys, zs))),
    )

    clause = Clause(
        assumptions=((ih_lhs, ih_rhs),),
        goal=step_goal,
    )

    print(f"  IH: {ih_lhs} = {ih_rhs}")
    print(f"  Step goal: {step_goal}")
    print()

    # First, try plain simplification (which uses schematic rules)
    simplified = simplify_clause(clause, engine)
    print(f"  After simplify_clause: {simplified.goal}")
    print(f"  Solved by simplify: {clause_solved(simplified)}")

    # Now try fertilize explicitly on the simplified clause
    if not clause_solved(simplified):
        fert_result = fertilize_clause(simplified, engine)
        print(f"\n  fertilize_clause fired: {fert_result is not None}")
        if fert_result is not None:
            print(f"  After fertilize: {fert_result.goal}")
            print(f"  Solved: {clause_solved(fert_result)}")
    print()


def demo_standard_proofs_unaffected(engine) -> None:
    """Verify that standard induction proofs still work with both features enabled."""

    print("=" * 65)
    print("Demo: Standard Proofs with Both Features Enabled")
    print("=" * 65)

    xs = V("xs", "List")
    ys = V("ys", "List")
    zs = V("zs", "List")
    n = V("n", "Nat")
    m = V("m", "Nat")
    nil = Const("nil")

    list_scheme = get_induction_scheme(engine, "list")
    nat_scheme = get_induction_scheme(engine, "nat")

    theorems = [
        (
            "append(xs, nil) = xs",
            Clause((), eq(append(xs, nil), xs)),
            xs,
            list_scheme,
            10,
        ),
        (
            "append(append(xs,ys),zs) = append(xs,append(ys,zs))",
            Clause((), eq(append(append(xs, ys), zs), append(xs, append(ys, zs)))),
            xs,
            list_scheme,
            15,
        ),
        (
            "length(append(xs,ys)) = add(length(xs),length(ys))",
            Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys)))),
            xs,
            list_scheme,
            14,
        ),
        (
            "add(n, m) = add(m, n)",
            Clause((), eq(add(n, m), add(m, n))),
            n,
            nat_scheme,
            10,
        ),
    ]

    for name, goal, var, scheme, depth in theorems:
        ok = prove(
            goal,
            engine,
            var=var,
            scheme=scheme,
            depth=depth,
            destructor_elim=True,  # DE enabled (default)
        )
        status = "OK" if ok else "FAILED"
        print(f"  [{status}]  {name}")

    print()


def main() -> None:
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    demo_destructor_elimination(engine)
    demo_fertilization(engine)
    demo_standard_proofs_unaffected(engine)

    print("=" * 65)
    print("All demos completed successfully.")
    print("=" * 65)


if __name__ == "__main__":
    main()
