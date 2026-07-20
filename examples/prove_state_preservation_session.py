"""
Manual proof demonstrating ProofSession tactics.

This example shows various tactics that can be used in manual proofs.
"""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *


def print_goal(session: ProofSession, label: str = "Goal") -> None:
    """Print current goal safely."""
    if session.current_goal() is None:
        print(f"  {label}: (all goals solved)")
    else:
        print(f"  {label}: {session.current_goal().goal}")


def main() -> None:
    reset_var_interner()

    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    xs = V("xs", "List")
    ys = V("ys", "List")
    nil = Const("nil")
    cons = lambda a, b: App("cons", a, b)
    append = lambda a, b: App("append", a, b)
    length = lambda a: App("length", a)
    zero = Const("0")
    succ = lambda t: App("S", t)
    add = lambda a, b: App("add", a, b)
    eq = lambda a, b: App("eq", a, b)

    print("=" * 70)
    print("ProofSession Tactics Demo")
    print("=" * 70)

    print("""
We prove: length(append(xs, ys)) = add(length(xs), length(ys))

This is the standard list length append theorem.
""")

    goal = Clause((), eq(length(append(xs, ys)), add(length(xs), length(ys))), ())

    print(f"Goal: {goal.goal}\n")

    print("=== Attempting automatic proof ===")
    ok_auto = prove(goal, engine, depth=10)
    print(f"prove (basic): {ok_auto}")

    from fiddlehead import get_induction_scheme

    list_scheme = get_induction_scheme(engine, "list")
    ok_induct = prove(
        goal, engine, var=xs, scheme=list_scheme, depth=12, induction_depth=1
    )
    print(f"prove with induction: {ok_induct}")

    print("\n=== Manual proof with ProofSession ===\n")

    session = ProofSession(goal, engine)

    print("Step 1: Show available rules")
    rules = session.list_rules()
    print(f"  Available rules: {sorted(rules.keys())}\n")

    print("Step 2: Apply induction on xs")
    session.induct(xs)
    print(f"  Created {len(session.goals)} branches\n")

    while session.current_goal() is not None:
        print(f"--- Processing branch ---")
        print_goal(session, "Current goal")

        ihs = session.list_ihs()
        if ihs:
            print(f"  IHs: {list(ihs.keys())}")

        print("  Using simp() to simplify...")
        session.simp()

        if session.current_goal() is None:
            print("  Solved by simplifier!")
        else:
            print_goal(session, "After simp")

            print("  Trying to discharge with exact()...")
            try:
                session.exact()
                print("  Discharged!")
            except ValueError as e:
                print(f"  Note: {e}")
        print()

    print("=" * 70)
    print(f"Proof complete: {session.qed()}")
    print("=" * 70)

    print("\nProof trace:")
    print(render_proof_trace(session.trace))

    print("""
Tactics demonstrated:

1. ProofSession(goal, engine) - Create interactive proof session

2. session.list_rules() - List available theory rules

3. session.induct(var) - Apply structural induction
   Creates branches for each constructor of the type

4. session.simp() - Apply automatic simplification
   Uses all available rules to simplify the goal

5. session.list_ihs() - View induction hypotheses
   Shows what IH rules are available in the current branch

6. session.exact() - Discharge goal from assumptions
   Succeeds if goal simplifies to true or matches assumption

7. session.qed() - Check if all goals are discharged

8. render_proof_trace() - Render proof tree as text

The key advantage of manual proof:
- You see exactly what's happening at each step
- You can try different rewrite strategies
- You can inspect assumptions, IHs, and goal state
- When automatic fails, you can diagnose why
""")


if __name__ == "__main__":
    main()
