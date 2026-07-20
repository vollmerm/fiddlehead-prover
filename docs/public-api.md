# Public API guide for simple proofs

This guide covers the part of the public API you need to write the kind of
proofs shown in the `examples/` directory. It focuses on the small set of names
you are most likely to use first.

The recommended import is:

```python
from fiddlehead import *
```

## A typical proof script

Most example scripts follow the same pattern:

1. Build terms with `V(...)`, `Const(...)`, and `App(...)`.
2. Create an engine with `make_engine(rules=builtin_rules())`.
3. Install one or more theories with `install_theory(...)`.
4. State a goal with `Clause(...)`.
5. Prove it with `prove(...)` or `prove_with_trace(...)`, passing `var=` for
   proofs by induction.

Calling `reset_var_interner()` first is optional; it clears remembered
variable sorts when unrelated proof scripts share one interpreter.

That is enough for the natural-number and list proofs in `examples/`.

## Building terms

Fiddlehead goals are built out of first-order terms.

### `V(name, sort=None)`

Creates a variable. Prefer this to constructing `Var(...)` directly.

```python
x = V("x", "Nat")
xs = V("xs", "List")
```

Use the `sort` argument when the variable belongs to a typed theory such as
`Nat`, `List`, `Tree`, or `Map`.

### `Const(name)`

Creates a constant term.

```python
zero = Const("0")
nil = Const("nil")
```

### `App(symbol, *args)`

Creates a function application term.

```python
S = lambda t: App("S", t)
add = lambda a, b: App("add", a, b)
eq = lambda a, b: App("eq", a, b)
append = lambda a, b: App("append", a, b)
```

In practice, most scripts define a few small helpers like `eq`, `add`, or
`append` so the goals are easier to read.

## Creating an engine

### `builtin_rules()`

Returns the prover's built-in rewrite rules for equality and basic boolean
simplification. Start here unless you have a specific reason to build an engine
from a different rule set.

### `make_engine(rules=...)`

Creates the engine that owns the rewrite rules, installed theories, caches, and
registered induction schemes for a proof run.

```python
engine = make_engine(rules=builtin_rules())
```

For simple proofs, this is usually all you need.

## Loading theories

Theories provide rewrite rules, sort information, and induction schemes.

### `install_theory(engine, theory, activate_scopes=True)`

Installs a theory into an engine.

```python
install_theory(engine, nat_theory())
install_theory(engine, list_theory())
```

Reinstalling the same theory version is a no-op, so scripts and notebook
cells can be re-run safely. Installing a different version of an installed
theory raises.

Most of the example scripts use these built-in theories:

| Theory | What it gives you |
| --- | --- |
| `nat_theory()` | natural numbers and arithmetic symbols like `0`, `S`, `add` |
| `int_theory()` | integer-ring symbols like `z0`, `z1`, `zadd`, `zmul`, `zneg` |
| `list_theory()` | list constructors and functions like `nil`, `cons`, `append`, `length` |
| `map_theory()` | finite map operations such as `empty`, `put`, `get` |
| `tree_theory()` | tree constructors used by the tree examples |

## Writing goals with `Clause`

`Clause` is the goal object you pass to the prover:

```python
Clause(assumptions, goal, disequalities=())
```

- `assumptions`: a tuple of local equalities like `((lhs, rhs), ...)`
- `goal`: the term you want to prove
- `disequalities`: optional local disequalities like `((lhs, rhs), ...)`

Most simple examples use no assumptions:

```python
goal = Clause((), eq(add(x, zero), x))
```

The map examples show the third argument in use:

```python
goal = Clause((), eq(get(put(put(m, k1, v1), k2, v2), k1), some(v1)), ((k2, k1),))
```

That means "prove the goal assuming `k2 != k1`."

## Core proof functions

The automated prover now runs a waterfall-style search. In broad terms it
simplifies the clause, splits `if(...)` branches, uses any active
forward-chaining facts, tries goal-level transformations such as fertilization,
and opens induction when you provide or select an induction target.

### `normalize(term, engine)`

Rewrites a term to normal form using the engine's rules and installed theories.

```python
term = add(S(S(zero)), S(zero))
print(normalize(term, engine))  # S(S(S(0)))
```

Use this when you want to see what the rewrite system can already simplify
before turning the term into a proof goal.

### `simplify_clause(clause, engine)`

Simplifies a clause under its local assumptions and disequalities. This is
useful when a goal only reduces after you add local case information.

### `prove(clause, engine, ...)`

Attempts to prove a clause with the default waterfall search and returns a
boolean.

```python
assert prove(Clause((), eq(zero, zero)), engine, depth=4)
```

Use this when you want the default automation but do not need a trace.

### `prove_with_trace(clause, engine, ...)`

Runs the same waterfall search and returns `(ok, trace)`.

```python
ok, trace = prove_with_trace(goal, engine, depth=12)
```

If induction is needed, pass `var=...`, `scheme=...`, and `induction_depth=...`
the way the arithmetic and list examples do.

### `render_waterfall_trace(trace)`

Renders the trace in a stage-oriented view.

```python
print(render_waterfall_trace(trace))
```

This is especially useful when you want to see where the prover simplified,
forward-chained, split branches, generalized, or introduced induction.

### `render_proof_trace(trace)`

Turns the returned trace into a readable proof tree.

```python
print(render_proof_trace(trace))
```

### `get_induction_scheme(engine, name)`

Looks up a registered induction scheme by name.

```python
nat_scheme = get_induction_scheme(engine, "nat")
list_scheme = get_induction_scheme(engine, "list")
assert nat_scheme is not None
assert list_scheme is not None
```

### `prove(clause, engine, var=..., ...)` — proofs by induction

Passing `var=` to `prove` (or `prove_with_trace`) proves the clause by
induction on that variable. The scheme is looked up from the variable's sort;
pass `scheme=` or `scheme_name=` to override.

```python
assert prove(goal, engine, var=x, depth=8, induction_depth=1)
```

Invalid induction requests raise `ValueError` instead of returning `False`:
an unknown scheme name, a variable whose sort has no registered scheme, a
variable/scheme sort mismatch, or a variable that does not occur in the
clause. A plain `False` therefore always means the search itself failed —
try a larger `depth` or inspect the trace.

### `prove_checked(clause, engine, ...)`

Runs the same waterfall-backed search but returns a certificate as well.

```python
ok, cert = prove_checked(goal, engine, depth=8, var=x, scheme=nat_scheme)
assert ok and cert is not None
assert check_certificate(cert, engine, depth=8, induction_depth=1)
```

Certificate checking replays the same kind of proof steps that ordinary proof
search uses, including forward chaining, fertilization, generalization,
destructor elimination, branch splitting, and induction.

## Interactive proof sessions

`ProofSession` is the REPL-oriented wrapper around the same proof machinery. It
keeps track of the active goal and available induction hypotheses, and it now
includes small formatting helpers for interactive use:

```python
session = ProofSession(goal, engine)
print(session.describe())
print(session.format_goal())
print(session.format_rules("*core.nat*"))
print(session.format_ihs())
```

Rule registration also auto-generates a usable name when `name=` is omitted,
which makes anonymous REPL registrations available to `rewrite_by_name(...)`.

## Worked example: natural-number proof

This follows the same basic arithmetic pattern as `README.md` and
`examples/prove_add_associativity.py`.

```python
from fiddlehead import *

reset_var_interner()

x = V("x", "Nat")
zero = Const("0")
S = lambda t: App("S", t)
add = lambda a, b: App("add", a, b)
eq = lambda a, b: App("eq", a, b)

engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory(), activate_scopes=True)

term = add(S(S(zero)), S(zero))
assert str(normalize(term, engine)) == "S(S(S(0)))"

goal = Clause((), eq(add(x, zero), x))
scheme = get_induction_scheme(engine, "nat")
assert scheme is not None
assert prove(goal, engine, var=x, scheme=scheme, depth=8, induction_depth=1)
```

## Worked example: append associativity with a trace

This is the same shape as `examples/prove_append_associativity.py`.

```python
from fiddlehead import *

reset_var_interner()

eq = lambda a, b: App("eq", a, b)
append = lambda a, b: App("append", a, b)

xs = V("xs", "List")
ys = V("ys", "List")
zs = V("zs", "List")

engine = make_engine(rules=builtin_rules())
install_theory(engine, list_theory(), activate_scopes=True)

scheme = get_induction_scheme(engine, "list")
assert scheme is not None

goal = Clause((), eq(append(append(xs, ys), zs), append(xs, append(ys, zs))))
ok, trace = prove_with_trace(
    goal,
    engine,
    depth=12,
    var=xs,
    scheme=scheme,
    induction_depth=1,
)
assert ok
print(render_proof_trace(trace))
```

## How the example scripts map to the API

| Example | Main APIs to look at |
| --- | --- |
| `prove_add_associativity.py` | `V`, `Const`, `App`, `Clause`, `make_engine`, `install_theory`, `get_induction_scheme`, `prove_with_trace` |
| `prove_int_ring_basics.py` | `int_theory`, AC-based proving with `prove_with_trace`, and contextual equalities via `Clause(assumptions=...)` |
| `prove_append_associativity.py` | `V`, `App`, `Clause`, `list_theory`, `prove_with_trace`, `render_proof_trace` |
| `prove_length_append.py` | same as above, plus installing both `nat_theory()` and `list_theory()` |
| `prove_map_theorems.py` | `Clause(..., disequalities=...)` and `simplify_clause` |
| `prove_map_aggregation.py` | `register_recursive_definition`, `SortSignature`, `prove_with_trace`, `prove` |

The remaining examples go a step further and extend the prover with custom sort
signatures, rewrite rules, or induction schemes. Those are public APIs too, but
they are not the first things you need to learn to write the simpler proofs in
this repository.

## Recursive function definitions

Use `register_recursive_definition(...)` when you want to add recursive function
equations through the public API instead of manually mutating engine rule lists.

```python
register_recursive_definition(
    engine,
    "sum_entries",
    (
        (sum_entries(empty), zero),
        (sum_entries(put(m, k, n)), add(n, sum_entries(m))),
    ),
    signature=SortSignature(
        (TypeConst("Map", (TypeVar("K"), TypeConst("Nat"))),),
        TypeConst("Nat"),
    ),
    precedence=5,
    scope="map_aggregation",
)
```

The equations are validated for sort correctness and required to be decreasing
as rewrite rules under the engine's current ordering.

If you are already working with the theorem environment directly, you can use
`get_theorem_environment(engine).register_recursive_definition(...)`.

In interactive scripts, the same feature is available through
`ProofSession.register_recursive_definition(...)`.

All three entry points register scoped rules, so you can activate and deactivate
the scope the same way you manage lemma rewrites and non-recursive definitions.

`examples/prove_map_aggregation.py` shows the recommended workflow:

1. Register the symbol signature (`SortSignature`)
2. Register recursive equations with `register_recursive_definition(...)`
3. Prove properties of the new function with `prove(...)` and
   `prove_with_trace(...)`

## What to read next

- `README.md` for the shortest project overview
- `examples/` for complete runnable scripts
