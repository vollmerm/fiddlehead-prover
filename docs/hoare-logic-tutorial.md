# Hoare-style proof tutorial for IMP programs

This tutorial shows how `examples/prove_hoare_while.py` encodes IMP semantics
and proves both execution properties and a real Hoare triple for a `while`
program with an explicit invariant.

The workflow is:

1. Encode IMP syntax and interpreter semantics as rewrite rules.
2. Add assertion syntax and Hoare-judgment semantics.
3. State goals as equality clauses (`eq(lhs, rhs)`).
4. Use rewriting (and induction when needed) to discharge goals.

## 1. Start with an engine and base theories

```python
from fiddlehead import *

reset_var_interner()
engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory(), activate_scopes=True)
install_theory(engine, map_theory(), activate_scopes=True)
```

`nat_theory` gives naturals (`0`, `S`, `add`), and `map_theory` gives finite
maps (`empty`, `put`, `get`, `some`, `none`) for program state.

## 2. Build IMP terms

Fiddlehead terms are built with `Const`, `V`, and `App`. A thin layer of helper
constructors keeps goals readable:

```python
zero = Const("0")
skip = Const("skip")
true = Const("true")
false = Const("false")

aconst = lambda t: App("aconst", t)
avar = lambda x: App("avar", x)
aadd = lambda a, b: App("aadd", a, b)
blt = lambda a, b: App("blt", a, b)

assign = lambda x, e: App("assign", x, e)
seq = lambda c1, c2: App("seq", c1, c2)
while_cmd = lambda b, c: App("while_cmd", b, c)

eval_a = lambda e, s: App("eval_a", e, s)
eval_b = lambda b, s: App("eval_b", b, s)
exec_cmd = lambda c, s: App("exec", c, s)
eq = lambda a, b: App("eq", a, b)
```

## 3. Register sorts and signatures

For typed rewriting, every symbol in your new language should have a sort
signature.

In the full script, this includes:

- IMP sorts: `AExp`, `BExp`, `Com`
- syntax constructors: `aconst`, `aadd`, `blt`, `assign`, `while_cmd`, ...
- interpreter functions: `eval_a`, `eval_b`, `exec`
- assertion layer: `Assert`, `bassn`, `and_a`, `not_a`, `holds`, `hoare`

If a symbol is missing a signature, term/rule validation will fail early.

## 4. Install interpreter semantics as rewrite rules

Define the executable semantics by rewriting `eval_*` and `exec` terms:

```python
env = get_theorem_environment(engine)

env.register_rule(Rule(exec_cmd(skip, s), s, skip_decrease_check=True), scope="imp_def")
env.register_rule(
    Rule(exec_cmd(seq(c1, c2), s), exec_cmd(c2, exec_cmd(c1, s))),
    scope="imp_def",
)
env.register_rule(
    Rule(
        exec_cmd(while_cmd(b, c), s),
        App("if", eval_b(b, s), exec_cmd(while_cmd(b, c), exec_cmd(c, s)), s),
        skip_decrease_check=True,
    ),
    scope="imp_def",
)
```

For boolean evaluation, bridge expression-level comparisons to nat-level
comparisons:

```python
blt_nat = lambda a, b: App("blt_nat", a, b)
env.register_rule(
    Rule(eval_b(blt(e1, e2), s), blt_nat(eval_a(e1, s), eval_a(e2, s))),
    scope="imp_def",
)
```

Then add recursive `blt_nat` equations (`0` vs `S(_)`, `S(_)` vs `0`, etc.).

## 5. Add an induction scheme for commands

Program-shape proofs (like determinism) need induction over `Com`:

```python
register_induction_scheme(
    engine,
    InductionScheme(
        name="com",
        sort="Com",
        base_terms=(skip,),
        constructors=(
            InductionConstructor("assign", 2, ()),
            InductionConstructor("seq", 2, (0, 1)),
            InductionConstructor("if_cmd", 3, (1, 2)),
            InductionConstructor("while_cmd", 2, (1,)),
        ),
    ),
)
```

## 6. Add Hoare assertions and judgments

The example introduces a shallow embedding of Hoare logic:

```python
bassn = lambda b: App("bassn", b)              # boolean-as-assertion
and_a = lambda p, q: App("and_a", p, q)        # assertion conjunction
not_a = lambda p: App("not_a", p)              # assertion negation
holds = lambda p, s: App("holds", p, s)        # assertion satisfaction
hoare = lambda p, c, q, s: App("hoare", p, c, q, s)
```

Core rewrite rules connect this to executable semantics:

```python
Rule(holds(and_a(p, q), s), App("and", holds(p, s), holds(q, s)))
Rule(holds(not_a(p), s), App("not", holds(p, s)))
Rule(holds(bassn(b), s), eval_b(b, s))
Rule(hoare(p, c, q, s), App("if", holds(p, s), holds(q, exec_cmd(c, s)), true))
```

For while proofs with an explicit invariant `I` and guard `B`, the script also
uses the specialized unfold:

```python
Rule(
    hoare(I, while_cmd(B, body), and_a(I, not_a(bassn(B))), s),
    App("if", holds(I, s), holds(and_a(I, not_a(bassn(B))), exec_cmd(while_cmd(B, body), s)), true),
)
```

## 7. Prove rewriting goals

A direct execution fact is usually just rewriting:

```python
goal = Clause((), eq(exec_cmd(skip, s), s), ())
ok, trace = prove_with_trace(goal, engine, depth=8)
assert ok
```

Theorem 9 in `examples/prove_hoare_while.py` is still this style:

```python
goal = Clause(
    (),
    eq(exec_cmd(while_cmd(blt(aconst(S(zero)), aconst(zero)), skip), s), s),
    (),
)
ok, trace = prove_with_trace(goal, engine, depth=20)
```

The condition rewrites to `false`, then the `if(false, ..., s)` branch collapses
to `s`.

## 8. Prove induction goals

For determinism of execution:

```python
det_goal = Clause(
    ((exec_cmd(c, s), s1), (exec_cmd(c, s), s2)),
    eq(s1, s2),
    (),
)
scheme = get_induction_scheme(engine, "com")
assert scheme is not None
assert prove_with_induction(det_goal, engine, c, scheme, depth=16, induction_depth=1)
```

Use this pattern whenever your theorem ranges over arbitrary commands.

## 9. Prove a real Hoare while triple

The headline Hoare theorem in the example is:

```text
{inv(x)} while false do x := x + 1 {inv(x) /\ not false}
```

encoded as:

```python
Clause(
    ((holds(inv(x), s), true),),
    eq(
        hoare(
            inv(x),
            while_cmd(bconst(false), assign(x, aadd(avar(x), aconst(S(zero))))),
            and_a(inv(x), not_a(bassn(bconst(false)))),
            s,
        ),
        true,
    ),
    (),
)
```

This is a genuine Hoare judgment (not just an execution equality): it proves
that from the invariant precondition, the `while` command satisfies the expected
postcondition `I /\ ¬B`.

## 10. Practical checklist

When a Hoare-style proof does not close:

1. Check symbol sort signatures first.
2. Normalize the key subterms directly (`normalize(term, engine)`) to see where rewriting stops.
3. Ensure rewrite scopes are synced and activated (`env._sync_engine_rules()`, `env.activate_scope(...)`).
4. For recursive program properties, confirm the induction variable and scheme sort match.

## 11. Run the example

```bash
.venv/bin/python examples/prove_hoare_while.py
```

This should print all ten theorems as proved, including the explicit
while-invariant Hoare theorem.
