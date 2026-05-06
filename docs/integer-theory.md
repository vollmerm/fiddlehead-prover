# Integer arithmetic tutorial

This tutorial explains how to use the `int_theory` to prove properties about
integers in Fiddlehead. It covers normalization, induction, lemma registration,
and ordering — from simple rewrites up through non-trivial inductive proofs.

The companion example script is `examples/prove_int_arithmetic.py`.

---

## What you will learn

1. How integer terms are represented and normalized
2. How to run induction proofs over integers
3. How to register and use integer lemmas
4. How to use subtraction and ordering operations

---

## 1. Setting up the integer theory

The integer theory depends on the natural-number theory (`nat_theory`). Always
install both:

```python
from fiddlehead import *

reset_var_interner()

engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory(), activate_scopes=True)
install_theory(engine, int_theory(), activate_scopes=True)
```

Define the term helpers you will use throughout:

```python
z0 = Const("z0")
z1 = Const("z1")
zadd = lambda a, b: App("zadd", a, b)
zmul = lambda a, b: App("zmul", a, b)
zneg = lambda t:   App("zneg", t)
zsucc = lambda t:  App("zsucc", t)
zpred = lambda t:  App("zpred", t)
zsub = lambda a, b: App("zsub", a, b)
znonneg = lambda t: App("znonneg", t)
zleq = lambda a, b: App("zleq", a, b)
zlt = lambda a, b: App("zlt", a, b)
eq = lambda a, b: App("eq", a, b)
```

---

## 2. How integers are represented

The integer theory uses a **pair representation**: the integer *a − b* is
represented by the term `zint(a, b)`, where `a` and `b` are natural numbers.

| Term | Represents | Normalizes to |
| --- | --- | --- |
| `z0` | 0 | `zint(0, 0)` |
| `z1` | 1 | `zint(S(0), 0)` |
| `zint(S(0), 0)` | 1 − 0 = 1 | (canonical) |
| `zint(0, S(0))` | 0 − 1 = −1 | (canonical) |
| `zint(S(0), S(0))` | 1 − 1 = 0 | `zint(0, 0)` |

The simplification rule `zint(S(a), S(b)) → zint(a, b)` keeps the
representation canonical by canceling common successors.

---

## 3. Normalization by rewriting

The core operations all reduce to the `zint` canonical form:

```python
print(normalize(zsucc(z0), engine))       # zint(S(0), 0)
print(normalize(zsub(z1, z0), engine))    # zint(S(0), 0)
print(normalize(zneg(zneg(z1)), engine))  # zint(S(0), 0)
print(normalize(znonneg(z0), engine))     # true
```

Use `normalize(...)` while you are developing a proof to see what the
rewrite system can do on its own. If a term reduces to `true`, it is already
proved.

---

## 4. Operations reference

| Symbol | Arity | Sorts | Description |
| --- | --- | --- | --- |
| `z0` | 0 | `Int` | zero |
| `z1` | 0 | `Int` | one |
| `zint` | 2 | `Nat × Nat → Int` | pair constructor for *pos* − *neg* |
| `zadd` | 2 | `Int × Int → Int` | addition (associative, commutative) |
| `zmul` | 2 | `Int × Int → Int` | multiplication (associative, commutative) |
| `zneg` | 1 | `Int → Int` | negation |
| `zsucc` | 1 | `Int → Int` | constructive successor for induction |
| `zpred` | 1 | `Int → Int` | constructive predecessor for induction |
| `zsub` | 1 | `Int × Int → Int` | subtraction (defined as `zadd(x, zneg(y))`) |
| `znonneg` | 1 | `Int → Bool` | is the integer non-negative? |
| `zleq` | 2 | `Int × Int → Bool` | less-than-or-equal (defined via `znonneg`) |
| `zlt` | 2 | `Int × Int → Bool` | less-than (defined via `zleq` and `zsucc`) |

### Interactive rules: `zsucc` and `zpred`

These two synthetic constructors are what make induction over integers
possible. They are defined so that:

```
zsucc(zint(a, b)) → zint(S(a), b)      "add 1"
zpred(zint(a, b)) → zint(a, S(b))      "subtract 1"
```

They cancel each other:

```
zpred(zsucc(x)) → x
zsucc(zpred(x)) → x
```

And negation pushes through them:

```
zneg(zsucc(x)) → zpred(zneg(x))
zneg(zpred(x)) → zsucc(zneg(x))
```

These interaction rules are essential for induction — without them, the
induction hypothesis often cannot be applied. For example, proving
`zneg(zneg(x)) = x` by induction relies on `zneg(zsucc(ih))` reducing to
`zpred(zneg(ih))`, which then lets the induction hypothesis fire.

---

## 5. AC properties: commutativity without induction

Because `zadd` and `zmul` are marked associative and commutative, the AC
normalizer handles commutativity automatically — no induction required:

```python
comm_goal = Clause((), eq(zadd(x, y), zadd(y, x)))
assert prove(comm_goal, engine, depth=8)   # True
```

Similarly for multiplication:

```python
mul_comm_goal = Clause((), eq(zmul(x, y), zmul(y, x)))
assert prove(mul_comm_goal, engine, depth=8)   # True
```

The proof trace will show a single simplification step that uses AC rewriting
to reorder the arguments, producing `zadd(x, y) = zadd(x, y)`, which the
builtin `eq(x, x) → true` rule discharges.

---

## 6. Integer induction

The integer induction scheme (`"int"`) uses `z0` as the base term and
`zsucc`/`zpred` as the two step constructors. This gives you three
proof obligations for a universal statement ∀x. P(x):

1. **Base case**: P(z0)
2. **Successor step**: P(ih) → P(zsucc(ih))
3. **Predecessor step**: P(ih) → P(zpred(ih))

### Proving double-negation elimination

This is a non-trivial induction proof that exercises negation interaction
rules and hypothesis application:

```python
x = V("x", "Int")
scheme = get_induction_scheme(engine, "int")
assert scheme is not None

neg_involutive = Clause((), eq(zneg(zneg(x)), x))
ok, trace = prove_with_trace(
    neg_involutive, engine,
    depth=12,
    var=x,
    scheme=scheme,
    induction_depth=2,
)
assert ok
```

Walk through what happens under the hood:

**Base case** — `zneg(zneg(z0)) = z0`:
```
zneg(zneg(z0)) → zneg(z0) → z0
```
The rule `zneg(z0) → z0` fires twice, reducing the left side to `z0`,
and `eq(z0, z0) → true` finishes the branch.

**Successor step** — assume `zneg(zneg(ih)) = ih`, prove
`zneg(zneg(zsucc(ih))) = zsucc(ih)`:
```
zneg(zneg(zsucc(ih)))
  → zneg(zpred(zneg(ih)))     (by zneg(zsucc(x)) → zpred(zneg(x)))
  → zsucc(zneg(zneg(ih)))     (by zneg(zpred(x)) → zsucc(zneg(x)))
  → zsucc(ih)                 (by induction hypothesis)
```
The goal reduces to `eq(zsucc(ih), zsucc(ih))`.

**Predecessor step** — mirror image, using `zpred` instead of `zsucc`.

### Proving additive identity

Another useful property that works by induction:

```python
add_zero_r = Clause((), eq(zadd(x, z0), x))
ok, trace = prove_with_trace(
    add_zero_r, engine,
    depth=12,
    var=x,
    scheme=scheme,
    induction_depth=2,
)
assert ok
```

Here the base case `zadd(z0, z0) = z0` is discharged by the identity rule
`zadd(z0, y) → y`. The step case `zadd(zsucc(ih), z0) = zsucc(ih)` is
handled by `zadd(y, z0) → y` (matching `y = zsucc(ih)`).

### What can and cannot be proved with induction

The induction scheme works best for properties about `zneg`, `zsucc`, and
`zpred` (which have interaction rules) and simple identities involving `zadd`
and `zmul` against constants like `z0` and `z1`.

Properties like "zadd commutes with zsucc"
(`zadd(zsucc(x), y) = zsucc(zadd(x, y))`) or "zneg distributes over zadd"
(`zneg(zadd(x, y)) = zadd(zneg(x), zneg(y))`) cannot yet be proved by
induction because the current rule set does not push `zsucc`/`zpred` through
`zadd` or `zmul`. Such rules can be added as theory extensions, but they
require careful ordering (see the prover core documentation for details).

---

## 7. Lemma registration

The theory ships with a companion function `register_int_lemmas` that proves
and registers key algebraic identities as scoped rewrite rules:

```python
lemma_names = register_int_lemmas(engine, depth=12, induction_depth=2)
print(lemma_names)  # ['zadd-assoc', 'zneg-involutive']
```

After registration, the lemmas are active as rewrites. Goals that match the
lemma's left-hand side are reduced automatically:

```python
y = V("y", "Int")
z = V("z", "Int")
assoc_goal = Clause((), eq(zadd(zadd(x, y), z), zadd(x, zadd(y, z))))
assert prove(assoc_goal, engine, depth=4)   # True
```

Because `zadd-assoc` is installed as a lemma rewrite, the AC normalizer
reorders the left side to match the right side in a single simplification
step, requiring no induction.

The `zneg-involutive` lemma similarly eliminates double negation anywhere it
appears:

```python
assert str(normalize(zneg(zneg(x)), engine)) == str(x)
```

You can combine lemma rewrites to prove compound properties. For example,
proving that `zsub(x, zneg(y))` simplifies to `zadd(x, y)`:

```python
# zsub(x, zneg(y)) → zadd(x, zneg(zneg(y))) → zadd(x, y)
sub_neg_goal = Clause((), eq(zsub(x, zneg(y)), zadd(x, y)))
assert prove(sub_neg_goal, engine, depth=4)   # True
```

---

## 8. Ordering over integers

The integer theory provides three ordering operations built compositionally:

| Operation | Definition |
| --- | --- |
| `znonneg(x)` | structural check against `zint` form — reduces to `true`/`false` for concrete integers |
| `zleq(x, y)` | `znonneg(zsub(y, x))` — *y − x* must be non-negative |
| `zlt(x, y)` | `zleq(zsucc(x), y)` — *x + 1 ≤ y* |

Concrete comparisons normalize automatically:

```python
print(normalize(zleq(z0, z1), engine))  # true  (0 ≤ 1)
print(normalize(zlt(z0, z1), engine))   # true  (0 < 1)
print(normalize(zleq(z1, z0), engine))  # znonneg(zint(0, S(0))) — not reduced
```

A comparison against a variable like `zleq(x, x)` will not reduce on its own
because the variable blocks the structural check. Proving ordering properties
over variables by induction requires additional interaction rules that are
not yet part of the default theory (see Section 6).

---

## 9. Worked example: full proof script

Here is a complete script that exercises normalization, AC properties,
induction, lemmas, and ordering:

```python
from fiddlehead import *

reset_var_interner()

engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory(), activate_scopes=True)
install_theory(engine, int_theory(), activate_scopes=True)

z0 = Const("z0")
z1 = Const("z1")
zadd = lambda a, b: App("zadd", a, b)
zmul = lambda a, b: App("zmul", a, b)
zneg = lambda t:   App("zneg", t)
zsucc = lambda t:  App("zsucc", t)
zsub = lambda a, b: App("zsub", a, b)
znonneg = lambda t: App("znonneg", t)
zleq = lambda a, b: App("zleq", a, b)
eq = lambda a, b: App("eq", a, b)

# --- Normalization ---
assert str(normalize(zsucc(z0), engine)) == "zint(S(0), 0)"
assert str(normalize(zsub(z1, z0), engine)) == "zint(S(0), 0)"
assert str(normalize(znonneg(z0), engine)) == "true"

# --- Commutativity (AC, no induction) ---
x = V("x", "Int")
y = V("y", "Int")
assert prove(Clause((), eq(zadd(x, y), zadd(y, x))), engine, depth=8)
assert prove(Clause((), eq(zmul(x, y), zmul(y, x))), engine, depth=8)

# --- Induction ---
scheme = get_induction_scheme(engine, "int")

ok, trace = prove_with_trace(
    Clause((), eq(zneg(zneg(x)), x)),
    engine, depth=12, var=x, scheme=scheme, induction_depth=2,
)
assert ok

ok, trace = prove_with_trace(
    Clause((), eq(zadd(x, z0), x)),
    engine, depth=12, var=x, scheme=scheme, induction_depth=2,
)
assert ok

# --- Lemmas ---
register_int_lemmas(engine, depth=12, induction_depth=2)

z = V("z", "Int")
assert prove(
    Clause((), eq(zadd(zadd(x, y), z), zadd(x, zadd(y, z)))),
    engine, depth=4,
)

# --- Ordering ---
assert str(normalize(zleq(z0, z1), engine)) == "true"

print("All proofs succeeded.")
```

Save this as a `.py` file and run it — every assertion should pass.

---

## 10. Debugging proofs that get stuck

If `prove_with_induction` returns `False`, inspect the simplified goals:

```python
from fiddlehead.proof import induction_branches, simplify_clause, clause_solved

branches = induction_branches(goal, var, scheme)
for i, branch in enumerate(branches):
    simplified = simplify_clause(branch, engine)
    print(f"Branch {i}: {simplified.goal}")
    print(f"  solved: {clause_solved(simplified)}")
```

You can also normalize the goal directly to see how far rewriting gets:

```python
print(engine.normalize(goal.goal))
```

Common reasons a goal does not reduce:

- A variable of sort `Int` blocks a rewrite rule that expects a `zint(...)`
  term. Try simplifying with `simplify_clause` first to apply contextual
  assumptions.
- The induction hypothesis cannot fire because the term has the wrong shape.
  Check whether the `zsucc`/`zpred` interaction rules cover your case.
- A constant like `z0` was expanded to `zint(0, 0)` before a matching rule
  could fire. The integer theory includes expanded-form identity rules (e.g.
  `zadd(zint(0, 0), y) → y`) to handle this.

---

## What to read next

- `examples/prove_int_arithmetic.py` — the full runnable example
- `examples/prove_int_ring_basics.py` — the simpler, AC-only version
- [Public API Guide](public-api.md) — the core API reference
- [Prover Core](prover-core.md) — architecture and waterfall prover internals
