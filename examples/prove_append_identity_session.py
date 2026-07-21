"""
Manual interactive proof of append(xs, nil) = xs using ProofSession.

This example demonstrates:
- Interactive proof sessions with ProofSession
- Named rule lookups via list_rules()
- Manual induction with induct()
- Induction hypothesis access via list_ihs()
- Named rewrites with rewrite_first() and rewrite_by_name()
"""

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

    xs = V("xs", "List")
    nil = Const("nil")

    goal = Clause((), eq(append(xs, nil), xs))

    print("=== Manual Proof: append(xs, nil) = xs ===\n")
    print(f"Goal: {goal.goal}\n")

    session = ProofSession(goal, engine)

    print("Step 0: Show available theory rules")
    print("  Theory rules available:")
    rules = session.list_rules()
    for name in sorted(rules.keys()):
        if "core.list" in name:
            print(f"    {name}: {rules[name].lhs} -> {rules[name].rhs}")
    print()

    print("Step 1: Apply induct(xs)")
    session.induct(xs)
    print(f"  Branches created: {len(session.goals)}")
    print(f"  Current goal: {session.current_goal().goal}")
    print()

    print("=== Branch 1: Base Case (xs = nil) ===")
    print(f"  Goal: {session.current_goal().goal}")
    print(f"  IHs: {session.list_ihs()}")

    print("\n  Step 1a: Apply theory rule for append(nil, xs)")
    session.rewrite_first("theory.core.list.append-nil")
    print(f"  Goal after rewrite: {session.current_goal().goal}")

    print("\n  Step 1b: Discharge with exact()")
    session.exact()
    print(f"  Base case solved: {session.current_goal() is not None}")
    print(f"  (Moving to step case)\n")

    print("=== Branch 2: Step Case (xs = cons(h, t)) ===")
    print(f"  Goal: {session.current_goal().goal}")
    print(f"  IHs: {session.list_ihs()}")
    for name, rule in session.list_ihs().items():
        print(f"    {name}: {rule.lhs} -> {rule.rhs}")
    print()

    print("  Step 2a: Apply theory rule for append(cons(h, t), xs)")
    session.rewrite_first("theory.core.list.append-cons")
    print(f"  Goal after rewrite: {session.current_goal().goal}")

    print("\n  Step 2b: Apply IH.0 (append(t, nil) = t)")
    session.rewrite_first("IH.0")
    print(f"  Goal after IH: {session.current_goal().goal}")

    print("\n  Step 2c: Discharge with exact()")
    session.exact()
    print(f"  Step case solved: {session.current_goal() is None}")
    print()

    print("=== Proof Complete ===")
    print(f"All goals solved: {session.current_goal() is None}")
    print()

    print("=== Proof Trace ===")
    print(render_proof_trace(session.trace))


if __name__ == "__main__":
    main()
