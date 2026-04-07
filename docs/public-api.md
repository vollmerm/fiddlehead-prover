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

1. Reset the variable interner with `reset_var_interner()`.
2. Build terms with `V(...)`, `Const(...)`, and `App(...)`.
3. Create an engine with `make_engine(rules=builtin_rules())`.
4. Install one or more theories with `install_theory(...)`.
5. State a goal with `Clause(...)`.
6. Prove it with `prove_with_trace(...)` or `prove_with_induction(...)`.

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
install_theory(engine, nat_theory(), activate_scopes=True)
install_theory(engine, list_theory(), activate_scopes=True)
```

Most of the example scripts use these built-in theories:

| Theory | What it gives you |
| --- | --- |
| `nat_theory()` | natural numbers and arithmetic symbols like `0`, `S`, `add` |
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

### `prove_with_trace(clause, engine, ...)`

Runs proof search and returns `(ok, trace)`.

```python
ok, trace = prove_with_trace(goal, engine, depth=12)
```

If induction is needed, pass `var=...`, `scheme=...`, and `induction_depth=...`
the way the arithmetic and list examples do.

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

### `prove_with_induction(clause, engine, var, scheme, ...)`

Proves a clause by explicitly supplying the induction variable and scheme.

```python
assert prove_with_induction(goal, engine, x, nat_scheme, depth=8, induction_depth=1)
```

This is the most direct induction API when you already know which variable and
scheme you want to use.

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
assert prove_with_induction(goal, engine, x, scheme, depth=8, induction_depth=1)
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
| `prove_append_associativity.py` | `V`, `App`, `Clause`, `list_theory`, `prove_with_trace`, `render_proof_trace` |
| `prove_length_append.py` | same as above, plus installing both `nat_theory()` and `list_theory()` |
| `prove_map_theorems.py` | `Clause(..., disequalities=...)` and `simplify_clause` |
| `prove_map_aggregation.py` | `register_recursive_definition`, `SortSignature`, `prove_with_trace`, `prove_with_induction` |

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
3. Prove properties of the new function with `prove_with_trace(...)` and
   `prove_with_induction(...)`

## What to read next

- `README.md` for the shortest project overview
- `examples/` for complete runnable scripts
