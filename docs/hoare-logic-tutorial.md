# Hoare logic tutorial for IMP programs

This is a beginner-friendly walkthrough of how to encode and prove Hoare-style
program properties in Fiddlehead, using:

- `examples/prove_hoare_while.py`

The headline theorem in that example is:

```text
{x = 0} x := 1; if x < 2 then x := 2 else x := 3 {x = 2}
```

---

## What you will learn

By the end, you should understand how to:

1. Represent programs, states, and assertions as terms.
2. Encode execution semantics as rewrite rules.
3. Encode Hoare judgments and assertion satisfaction.
4. State proof goals as `Clause`s.
5. Prove `hoare(pre, cmd, post, s) = true` by rewriting.

---

## 1. Mental model: how Fiddlehead proves things

Fiddlehead is a first-order rewriting prover. You define:

- **terms** (`App`, `Const`, `V`)
- **rules** (`Rule(lhs, rhs)`)
- **goals** (`Clause(...)`)

Then the engine repeatedly rewrites until goals simplify to `true`.

For Hoare logic, you do not use a special tactic language. Instead, you embed
Hoare concepts as terms and rules, then let rewriting prove them.

---

## 2. Minimal setup

In the example script:

```python
reset_var_interner()
engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory(), activate_scopes=True)
install_theory(engine, map_theory(), activate_scopes=True)
```

This gives:

- booleans/equality simplification (`builtin_rules`)
- naturals (`0`, `S`, `add`, ...)
- finite maps for state (`empty`, `put`, `get`, `some`, `none`)

---

## 3. Representing IMP programs and expressions

The script builds IMP syntax constructors as helper lambdas:

```python
aconst = lambda t: App("aconst", t)
avar = lambda t: App("avar", t)
aadd = lambda a, b: App("aadd", a, b)

bconst = lambda b: App("bconst", b)
blt = lambda a, b: App("blt", a, b)

assign = lambda x, e: App("assign", x, e)
seq = lambda c1, c2: App("seq", c1, c2)
if_cmd = lambda b, c1, c2: App("if_cmd", b, c1, c2)
while_cmd = lambda b, c: App("while_cmd", b, c)
```

Interpreter functions:

```python
eval_a = lambda e, s: App("eval_a", e, s)
eval_b = lambda b, s: App("eval_b", b, s)
exec_cmd = lambda c, s: App("exec", c, s)
```

---

## 4. Sorts and signatures (important for beginners)

Fiddlehead is typed. Every symbol you introduce should have a sort signature.

Examples from the script:

```python
register_sort_signature(engine, "assign", SortSignature((a, TypeConst("AExp")), TypeConst("Com")))
register_sort_signature(engine, "exec", SortSignature((TypeConst("Com"), TypeConst("Map", (k, v))), TypeConst("Map", (k, v))))
register_sort_signature(engine, "hoare", SortSignature((TypeConst("Assert"), TypeConst("Com"), TypeConst("Assert"), TypeConst("Map", (k, v))), TypeConst("Bool")))
```

If you forget a signature, proof normalization fails early with a type error.

---

## 5. Encoding IMP execution semantics

The script adds rewrite rules for the interpreter, for example:

```python
Rule(exec_cmd(skip, s), s)
Rule(exec_cmd(assign(x, e), s), put(s, x, eval_a(e, s)))
Rule(exec_cmd(seq(c1, c2), s), exec_cmd(c2, exec_cmd(c1, s)))
Rule(exec_cmd(if_cmd(b, c1, c2), s), if(eval_b(b, s), exec_cmd(c1, s), exec_cmd(c2, s)))
```

The `while` rule is encoded by one-step unfold:

```python
Rule(
    exec_cmd(while_cmd(b, c), s),
    if(eval_b(b, s), exec_cmd(while_cmd(b, c), exec_cmd(c, s)), s),
)
```

---

## 6. Encoding Hoare logic in terms

### 6.1 Assertion terms

```python
bassn = lambda b: App("bassn", b)          # Bool expression lifted to assertion
and_a = lambda p, q: App("and_a", p, q)    # conjunction
not_a = lambda p: App("not_a", p)          # negation
aeq = lambda x, n: App("aeq", x, n)        # x = n
holds = lambda p, s: App("holds", p, s)    # assertion satisfaction
```

### 6.2 Hoare judgment term

```python
hoare = lambda p, c, q, s: App("hoare", p, c, q, s)
```

### 6.3 Hoare/Assertion semantics rules

```python
Rule(holds(and_a(p, q), s), and(holds(p, s), holds(q, s)))
Rule(holds(not_a(p), s), not(holds(p, s)))
Rule(holds(bassn(b), s), eval_b(b, s))
Rule(holds(aeq(x, n), s), eq(get(s, x), some(n)))

Rule(hoare(p, c, q, s), if(holds(p, s), holds(q, exec_cmd(c, s)), true))
```

This means a Hoare theorem is proved by showing this reduces to `true`.

---

## 7. The worked theorem

Theorem:

```text
{x=0} x:=1; if x<2 then x:=2 else x:=3 {x=2}
```

The script encodes:

```python
pre = aeq(x_id, zero)
cmd = seq(
    assign(x_id, aconst(one)),
    if_cmd(
        blt(avar(x_id), aconst(two)),
        assign(x_id, aconst(two)),
        assign(x_id, aconst(succ(two))),
    ),
)
post = aeq(x_id, two)
state0 = put(empty, x_id, zero)
```

Goal:

```python
Clause((), eq(hoare(pre, cmd, post, state0), true), ())
```

Intuition:

1. precondition says `x=0` in `state0`
2. first assignment sets `x=1`
3. guard `x<2` is true, so then-branch runs
4. then-branch sets `x=2`
5. postcondition `x=2` holds

---

## 8. How the proof is executed

The script uses:

```python
ok, trace = prove_with_trace(goal, engine, depth=...)
```

For this Hoare theorem, the helper prints whether the Hoare judgment simplified
to `true`.

If a goal fails, print:

```python
engine.normalize(goal.goal)
```

to see where rewriting got stuck.

---

## 9. Manual Hoare proofs with `ProofSession`

The tutorial example also shows the same Hoare theorem proved step by step with
`ProofSession`. This is useful when you want to see each rewrite explicitly
instead of letting `prove_with_trace(...)` do everything at once.

Start by creating a session and activating the Hoare theory scope:

```python
session = ProofSession(theorem_10_goal, engine)
session.activate_scope("imp_def")
```

Then rewrite the Hoare judgment into its semantic form:

```python
session.rewrite_first("hoare_semantics")
session.rewrite_first("holds_aeq")
session.simp()
```

For the sequence-and-conditional example, that is enough to discharge the
goal:

```python
theorem_10_ok = session.qed()
```

The same pattern works for the other manual proofs in the script:

```python
session = ProofSession(while_blt_goal, engine)
session.activate_scope("imp_def")
session.rewrite_first("exec_while")
session.simp()
session.qed()
```

For the one-step while-loop example, you rewrite `exec_while`, simplify the
result, then repeat the same rewrite/simplify cycle until the loop condition
reduces to `false`.

The key idea is that manual proofs follow the same semantic rules as the
automated proof, but you control the order of rewriting and simplification.

---

## 10. A more interesting inductive theorem

The final theorem in the example is no longer a one-step Hoare proof. It shows
how to reason inductively about a recursive IMP command:

```text
exec(repeat_set(m, n), put(s, x=m)) = put(s, x=m)
```

The recursive command is defined so that:

```python
repeat_set(m, 0) = skip
repeat_set(m, S(n)) = seq(assign(x, aconst(m)), repeat_set(m, n))
```

This theorem is interesting because the proof needs both unfolding and the
induction hypothesis. In the base case, `repeat_set(m, 0)` becomes `skip`, so
`exec(skip, ...)` simplifies immediately. In the step case, the recursive call
is exposed only after rewriting the command definition and execution semantics.

The proof script follows this shape:

```python
session = ProofSession(theorem_14_goal, engine)
session.activate_scope("imp_def")
session.induct(n)

session.rewrite_first("def-repeat_set_zero")
session.rewrite_first("exec_skip")
session.simp()

session.rewrite_first("def-repeat_set.0")
session.rewrite_first("exec_seq")
session.rewrite_first("exec_assign")
session.rewrite_first("IH.0")
session.simp()
```

What is happening here:

1. `induct(n)` splits the goal into the base case and step case.
2. The base case rewrites `repeat_set(m, 0)` to `skip`, then `exec_skip`
   closes it.
3. The step case unfolds `repeat_set(m, S(n))` into a sequence.
4. `exec_seq` and `exec_assign` expose the recursive call under `exec`.
5. `IH.0` rewrites that recursive call away, and `simp()` finishes the goal.

This is the kind of theorem that benefits from the stronger simplification and
induction handling in the prover core.

---

## 11. Common beginner mistakes

1. Missing sort signature for a new symbol.
2. Using inconsistent variable sorts.
3. Forgetting a bridge rule (for example `exec(if_cmd(...))` or `nat_of(some(n))`).
4. Writing a non-decreasing rule that causes rewrite divergence.

---

## 12. Suggested next exercises

1. Change the postcondition to `x=3` and confirm the theorem fails.
2. Replace the conditional with `if x<1 then ... else ...` and update the proof.
3. Add a second theorem with conjunction in the postcondition:
   `and_a(aeq(x, two), not_a(bassn(blt(avar(x), aconst(two)))))`.

---

## 13. Run the tutorial example

```bash
.venv/bin/python examples/prove_hoare_while.py
```

You should see all theorems proved, including the Hoare sequence/conditional
theorem.
