from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from fiddlehead import *


def main() -> None:
    reset_var_interner()

    # Set up engine with natural number and list theories
    engine = make_engine(rules=builtin_rules())
    install_theory(engine, nat_theory(), activate_scopes=True)
    install_theory(engine, list_theory(), activate_scopes=True)

    # Term constructors
    nil = Const("nil")
    cons = lambda h, t: App("cons", h, t)
    append = lambda a, b: App("append", a, b)
    rev = lambda xs: App("rev", xs)
    eq = lambda a, b: App("eq", a, b)

    # Variables (with explicit List sort for induction scheme resolution)
    xs = V("xs", "List")
    ys = V("ys", "List")
    h = V("h")           # list element (no sort needed)
    t = V("t", "List")   # list tail

    # Register rev as a recursive definition.
    # rev(nil) = nil
    # rev(cons(h, t)) = append(rev(t), cons(h, nil))
    #
    # precedence=4 is required: must be strictly above append(3) so that the
    # step equation passes the LPO decrease check in register_recursive_definition.
    theory = get_theorem_environment(engine)
    theory.register_recursive_definition(
        "rev",
        (
            (rev(nil), nil),
            (rev(cons(h, t)), append(rev(t), cons(h, nil))),
        ),
        scope="rev_defs",
        signature=SortSignature(
            (TypeConst("List", (TypeVar("A"),)),),
            TypeConst("List", (TypeVar("A"),)),
        ),
        precedence=4,
    )
    theory.activate_scope("rev_defs")
    # Rule names: "def-rev.0" and "def-rev.1"

    list_scheme = get_induction_scheme(engine, "list")
    assert list_scheme is not None

    # =========================================================================
    # Theorem 1: append(xs, nil) = xs  (append_right_id)
    # =========================================================================
    print("=" * 65)
    print("Theorem 1: append(xs, nil) = xs  (append_right_id)")
    print("=" * 65)

    goal1 = Clause((), eq(append(xs, nil), xs))

    sess1 = ProofSession(goal1, engine)
    print(f"  Goal: {goal1.goal}")
    sess1.induct(xs)
    print(f"  After induct(xs): {len(sess1.goals)} branches")

    # --- Branch 1: Base case xs = nil ---
    # Goal: eq(append(nil, nil), nil)
    print(f"\n  [Base] {sess1.current_goal().goal}")
    sess1.rewrite_first("theory.core.list.0")  # append(nil, nil) -> nil
    print(f"         after list.0: {sess1.current_goal().goal}")
    sess1.exact()
    print("         solved.")

    # --- Branch 2: Step case xs = cons(h', t') ---
    # IH.0: append(t', nil) = t'
    # Goal: eq(append(cons(h', t'), nil), cons(h', t'))
    print(f"\n  [Step] {sess1.current_goal().goal}")
    ihs = sess1.list_ihs()
    print(f"         IHs: { {k: str(v.lhs) + ' -> ' + str(v.rhs) for k, v in ihs.items()} }")
    sess1.rewrite_first("theory.core.list.1")  # cons(h', append(t', nil))
    print(f"         after list.1: {sess1.current_goal().goal}")
    sess1.rewrite_first("IH.0")                # cons(h', t')
    print(f"         after IH.0:   {sess1.current_goal().goal}")
    sess1.exact()
    print("         solved.")

    assert sess1.qed(), "Theorem 1 session proof failed"
    print("\n  ProofSession: qed() = True")

    ok1, cert1 = prove_checked(
        goal1, engine, depth=12, var=xs, scheme=list_scheme, induction_depth=1
    )
    assert ok1 and cert1 is not None, "prove_checked failed for append_right_id"
    print(f"  prove_checked: {ok1}")

    theory.register_lemma(Lemma("append_right_id", goal1, cert1), depth=12, induction_depth=1)
    theory.register_lemma_rewrite("append_right_id", scope="lemma_rewrites", orientation="auto")
    theory.activate_scope("lemma_rewrites")   # activate once; later rewrites auto-sync
    print("  Registered: 'lemma-append_right_id'  =>  append(xs,nil) -> xs")

    # =========================================================================
    # Theorem 2: append(append(xs,ys),zs) = append(xs,append(ys,zs))  (append_assoc)
    # =========================================================================
    print("\n" + "=" * 65)
    print("Theorem 2: append(append(xs,ys),zs) = append(xs,append(ys,zs))")
    print("           (append_assoc)")
    print("=" * 65)

    zs = V("zs", "List")
    goal2 = Clause((), eq(append(append(xs, ys), zs), append(xs, append(ys, zs))))

    sess2 = ProofSession(goal2, engine)
    print(f"  Goal: {goal2.goal}")
    sess2.induct(xs)
    print(f"  After induct(xs): {len(sess2.goals)} branches")

    # --- Branch 1: Base case xs = nil ---
    # Goal: eq(append(append(nil,ys),zs), append(nil,append(ys,zs)))
    # simp() applies list.0 twice: append(nil,ys)->ys and append(nil,append(ys,zs))->append(ys,zs)
    print(f"\n  [Base] {sess2.current_goal().goal}")
    sess2.simp()
    print("         solved by simp().")

    # --- Branch 2: Step case xs = cons(h', t') ---
    # IH.0: append(append(t', ys), zs) = append(t', append(ys, zs))
    # Goal: eq(append(append(cons(h',t'),ys),zs), append(cons(h',t'),append(ys,zs)))
    print(f"\n  [Step] {sess2.current_goal().goal}")
    print(f"         IHs: {list(sess2.list_ihs().keys())}")
    # Step 1: inner rewrite — append(cons(h',t'), ys) -> cons(h', append(t',ys))
    sess2.rewrite_first("theory.core.list.1")
    print(f"         after list.1 (inner): {sess2.current_goal().goal}")
    # Step 2: outer rewrite — append(cons(h', append(t',ys)), zs) -> cons(h', append(append(t',ys),zs))
    sess2.rewrite_first("theory.core.list.1")
    print(f"         after list.1 (outer): {sess2.current_goal().goal}")
    # Step 3: apply IH — append(append(t',ys),zs) -> append(t', append(ys,zs))
    sess2.rewrite_first("IH.0")
    print(f"         after IH.0:           {sess2.current_goal().goal}")
    # Step 4: expand RHS — append(cons(h',t'), append(ys,zs)) -> cons(h', append(t',append(ys,zs)))
    sess2.rewrite_first("theory.core.list.1")
    print(f"         after list.1 (RHS):   {sess2.current_goal().goal}")
    sess2.exact()
    print("         solved.")

    assert sess2.qed(), "Theorem 2 session proof failed"
    print("\n  ProofSession: qed() = True")

    ok2, cert2 = prove_checked(
        goal2, engine, depth=12, var=xs, scheme=list_scheme, induction_depth=1
    )
    assert ok2 and cert2 is not None, "prove_checked failed for append_assoc"
    print(f"  prove_checked: {ok2}")

    theory.register_lemma(Lemma("append_assoc", goal2, cert2), depth=12, induction_depth=1)
    theory.register_lemma_rewrite("append_assoc", scope="lemma_rewrites", orientation="auto")
    # scope already active — _add_rule_to_scope auto-syncs the engine
    print("  Registered: 'lemma-append_assoc'")
    print("              append(append(xs,ys),zs) -> append(xs,append(ys,zs))")

    # =========================================================================
    # Theorem 3: rev(append(xs,ys)) = append(rev(ys), rev(xs))  (rev_append)
    #
    # This is the key lemma. The step case requires:
    #   - Two rewrites to expose the recursive structure
    #   - The induction hypothesis IH.0
    #   - A second def-rev.1 rewrite on the RHS
    #   - append_assoc to reassociate and close the goal
    # =========================================================================
    print("\n" + "=" * 65)
    print("Theorem 3: rev(append(xs,ys)) = append(rev(ys), rev(xs))")
    print("           (rev_append)  [KEY LEMMA]")
    print("=" * 65)

    goal3 = Clause((), eq(rev(append(xs, ys)), append(rev(ys), rev(xs))))

    sess3 = ProofSession(goal3, engine)
    print(f"  Goal: {goal3.goal}")
    sess3.induct(xs)
    print(f"  After induct(xs): {len(sess3.goals)} branches")

    # --- Branch 1: Base case xs = nil ---
    # Goal: eq(rev(append(nil,ys)), append(rev(ys), rev(nil)))
    #   list.0:           rev(ys) = append(rev(ys), rev(nil))
    #   def-rev.0:        rev(ys) = append(rev(ys), nil)
    #   append_right_id:  rev(ys) = rev(ys)
    print(f"\n  [Base] {sess3.current_goal().goal}")
    sess3.rewrite_first("theory.core.list.0")      # append(nil,ys) -> ys
    print(f"         after list.0:              {sess3.current_goal().goal}")
    sess3.rewrite_first("def-rev.0")               # rev(nil) -> nil
    print(f"         after def-rev.0:           {sess3.current_goal().goal}")
    sess3.rewrite_first("lemma-append_right_id")   # append(rev(ys), nil) -> rev(ys)
    print(f"         after append_right_id:     {sess3.current_goal().goal}")
    sess3.exact()
    print("         solved.")

    # --- Branch 2: Step case xs = cons(h', t') ---
    # IH.0: rev(append(t', ys)) = append(rev(ys), rev(t'))
    # Goal: eq(rev(append(cons(h',t'),ys)), append(rev(ys), rev(cons(h',t'))))
    #
    #  list.1:       rev(cons(h', append(t',ys)))    =  append(rev(ys), rev(cons(h',t')))
    #  def-rev.1:    append(rev(append(t',ys)),       =  append(rev(ys), rev(cons(h',t')))
    #                        cons(h',nil))
    #  IH.0:         append(append(rev(ys),rev(t')), =  append(rev(ys), rev(cons(h',t')))
    #                        cons(h',nil))
    #  def-rev.1     append(append(rev(ys),rev(t')), =  append(rev(ys),
    #  (RHS):                cons(h',nil))                     append(rev(t'),cons(h',nil)))
    #  append_assoc: append(rev(ys),                 =  append(rev(ys),
    #                  append(rev(t'),cons(h',nil)))           append(rev(t'),cons(h',nil)))
    print(f"\n  [Step] {sess3.current_goal().goal}")
    print(f"         IHs: {list(sess3.list_ihs().keys())}")
    sess3.rewrite_first("theory.core.list.1")   # expand append in argument of outer rev
    print(f"         after list.1:              {sess3.current_goal().goal}")
    sess3.rewrite_first("def-rev.1")            # unfold rev(cons(h', append(t',ys))) on LHS
    print(f"         after def-rev.1 (LHS):     {sess3.current_goal().goal}")
    sess3.rewrite_first("IH.0")                 # replace rev(append(t',ys)) using IH
    print(f"         after IH.0:                {sess3.current_goal().goal}")
    sess3.rewrite_first("def-rev.1")            # unfold rev(cons(h',t')) on RHS
    print(f"         after def-rev.1 (RHS):     {sess3.current_goal().goal}")
    sess3.rewrite_first("lemma-append_assoc")   # reassociate LHS to match RHS
    print(f"         after append_assoc:        {sess3.current_goal().goal}")
    sess3.exact()
    print("         solved.")

    assert sess3.qed(), "Theorem 3 session proof failed"
    print("\n  ProofSession: qed() = True")

    ok3, cert3 = prove_checked(
        goal3, engine, depth=14, var=xs, scheme=list_scheme, induction_depth=1
    )
    assert ok3 and cert3 is not None, "prove_checked failed for rev_append"
    print(f"  prove_checked: {ok3}")

    theory.register_lemma(Lemma("rev_append", goal3, cert3), depth=14, induction_depth=1)
    theory.register_lemma_rewrite("rev_append", scope="lemma_rewrites", orientation="auto")
    print("  Registered: 'lemma-rev_append'")
    print("              rev(append(xs,ys)) -> append(rev(ys),rev(xs))")

    # =========================================================================
    # Theorem 4: rev(rev(xs)) = xs  (rev_rev) — MAIN THEOREM
    #
    # The step case uses rev_append to swap the outer rev inside,
    # the IH to discharge rev(rev(t')), then simp to normalize the
    # remaining rev(cons(h', nil)) subterm using the accumulated rules.
    # =========================================================================
    print("\n" + "=" * 65)
    print("Theorem 4: rev(rev(xs)) = xs  (rev_rev)  [MAIN THEOREM]")
    print("=" * 65)

    goal4 = Clause((), eq(rev(rev(xs)), xs))

    sess4 = ProofSession(goal4, engine)
    print(f"  Goal: {goal4.goal}")
    sess4.induct(xs)
    print(f"  After induct(xs): {len(sess4.goals)} branches")

    # --- Branch 1: Base case xs = nil ---
    # Goal: eq(rev(rev(nil)), nil)
    # simp applies: rev(nil)->nil, rev(nil)->nil => eq(nil, nil) => true
    print(f"\n  [Base] {sess4.current_goal().goal}")
    sess4.simp()
    print("         solved by simp().")

    # --- Branch 2: Step case xs = cons(h', t') ---
    # IH.0: rev(rev(t')) = t'
    # Goal: eq(rev(rev(cons(h',t'))), cons(h',t'))
    #
    #  def-rev.1:      rev(append(rev(t'), cons(h',nil)))  =  cons(h',t')
    #  rev_append:     append(rev(cons(h',nil)), rev(rev(t')))  =  cons(h',t')
    #  IH.0:           append(rev(cons(h',nil)), t')            =  cons(h',t')
    #  simp():  unfolds rev(cons(h',nil)) step by step:
    #    def-rev.1:  append(rev(t'), cons(h',nil))
    #    def-rev.0:  append(append(nil, cons(h',nil)))... -> cons(h',nil)
    #    list.1+0:   append(cons(h',nil), t') -> cons(h', t')  => done
    print(f"\n  [Step] {sess4.current_goal().goal}")
    print(f"         IHs: {list(sess4.list_ihs().keys())}")
    sess4.rewrite_first("def-rev.1")           # rev(cons(h',t')) -> append(rev(t'),cons(h',nil))
    print(f"         after def-rev.1:           {sess4.current_goal().goal}")
    sess4.rewrite_first("lemma-rev_append")    # rev(append(rev(t'),cons(h',nil))) -> append(rev(cons(h',nil)), rev(rev(t')))
    print(f"         after rev_append:          {sess4.current_goal().goal}")
    sess4.rewrite_first("IH.0")                # rev(rev(t')) -> t'
    print(f"         after IH.0:                {sess4.current_goal().goal}")
    sess4.simp()                               # normalize rev(cons(h',nil)) and remaining appends
    print("         solved by simp().")

    assert sess4.qed(), "Theorem 4 session proof failed"
    print("\n  ProofSession: qed() = True")

    ok4, cert4 = prove_checked(
        goal4, engine, depth=16, var=xs, scheme=list_scheme, induction_depth=1
    )
    assert ok4 and cert4 is not None, "prove_checked failed for rev_rev"
    print(f"  prove_checked: {ok4}")

    theory.register_lemma(Lemma("rev_rev", goal4, cert4), depth=16, induction_depth=1)
    print("  Registered: 'rev_rev'")

    # =========================================================================
    print("\n" + "=" * 65)
    print("All four theorems proved successfully!")
    print("  1. append_right_id : append(xs, nil) = xs")
    print("  2. append_assoc    : append(append(xs,ys),zs) = append(xs,append(ys,zs))")
    print("  3. rev_append      : rev(append(xs,ys)) = append(rev(ys),rev(xs))")
    print("  4. rev_rev         : rev(rev(xs)) = xs")
    print("=" * 65)

    assert ok1 and ok2 and ok3 and ok4


if __name__ == "__main__":
    main()
