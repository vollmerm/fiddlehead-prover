# Fiddlehead

Fiddlehead is a theorem prover and proof assistant written in Python.

I started it as a learning project because I wanted to understand, from the inside, how systems like ACL2 and Z3 work. Over time it grew into something more capable than a toy, but I have tried to keep the core ideas visible so the codebase stays useful for learning.

The public API is exposed through `fiddlehead`, which re-exports the main interface from `fiddlehead.prover`.

## What it does

Fiddlehead works with first-order terms and equality goals. It can:

- normalize terms with rewrite rules
- reason about equalities in context
- prove simple clauses by simplification, branching, and induction
- infer and check sorts
- load small theories with scoped rewrites and induction schemes

It is a better fit for small, explicit proof experiments than for large formal developments. The aim is to keep the prover compact enough that you can read through the implementation and understand how the pieces fit together.

## Public API

The recommended entrypoint is:

```python
from fiddlehead import *
```

For a workflow-oriented guide to the core public API used by the example
proofs, see [`docs/public-api.md`](docs/public-api.md).

## Examples

This example installs a small natural-number theory, normalizes a term, and proves a basic identity by induction.

```python
from fiddlehead import *

x = V("x", "Nat")
y = V("y", "Nat")
zero = Const("0")
S = lambda t: App("S", t)
add = lambda a, b: App("add", a, b)
eq = lambda a, b: App("eq", a, b)

engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory())

term = add(S(S(zero)), S(zero))
print(normalize(term, engine))  # S(S(S(0)))

goal = Clause((), eq(add(x, zero), x))
assert prove(goal, engine, var=x)  # induction scheme inferred from x's sort
```

This one proves associativity of list append and prints the resulting proof trace.

```python
from fiddlehead import *

eq = lambda a, b: App("eq", a, b)
append = lambda a, b: App("append", a, b)

xs = V("xs", "List")
ys = V("ys", "List")
zs = V("zs", "List")

engine = make_engine(rules=builtin_rules())
install_theory(engine, list_theory())

goal = Clause((), eq(append(append(xs, ys), zs), append(xs, append(ys, zs))))
result = prove(goal, engine, var=xs)
assert result
print(render_proof_trace(result.trace))
```

Here is a small manual proof of `append(xs, nil) = xs` using `ProofSession`:

```python
from fiddlehead import *

xs = V("xs", "List")
nil = Const("nil")
append = lambda a, b: App("append", a, b)
eq = lambda a, b: App("eq", a, b)

engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory())
install_theory(engine, list_theory())

goal = Clause((), eq(append(xs, nil), xs))
session = ProofSession(goal, engine)

session.induct(xs)
session.rewrite_first("theory.core.list.0")
session.exact()
session.rewrite_first("theory.core.list.1")
session.rewrite_first("IH.0")
session.exact()

assert session.qed()
```

Example proof tree output:

```text
- prove [solved] :: depth=12 -> eq(append(append(xs, ys), zs), append(xs, append(ys, zs)))
  - simplify -> eq(append(append(xs, ys), zs), append(xs, append(ys, zs)))
  - induction [solved] :: var=xs, scheme=list -> eq(append(append(xs, ys), zs), append(xs, append(ys, zs)))
    - induction-branch [solved] :: depth=12 -> eq(append(append(nil, ys), zs), append(nil, append(ys, zs)))
      - simplify -> true
    - induction-branch [solved] :: depth=12 -> eq(append(append(cons(xs_cons_arg_0, xs_ih_0), ys), zs), append(cons(xs_cons_arg_0, xs_ih_0), append(ys, zs)))
      - simplify -> true
```

The `examples` directory has a few larger scripts. For example:

```text
$ python ./examples/prove_length_append.py
- prove [solved] :: depth=14 -> eq(length(append(xs, ys)), add(length(xs), length(ys)))
  - simplify -> eq(length(append(xs, ys)), add(length(xs), length(ys)))
  - induction [solved] :: var=xs, scheme=list -> eq(length(append(xs, ys)), add(length(xs), length(ys)))
    - induction-branch [solved] :: depth=14 -> eq(length(append(nil, ys)), add(length(nil), length(ys)))
      - simplify -> true
    - induction-branch [solved] :: depth=14 -> eq(length(append(cons(xs_cons_arg_0, xs_ih_0), ys)), add(length(cons(xs_cons_arg_0, xs_ih_0)), length(ys)))
      - simplify -> true
```

## Installation

Clone the repository and install it locally for development:

```bash
git clone https://github.com/vollmerm/fiddlehead-prover.git
cd fiddlehead-prover
python -m venv .venv  # or python3
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e .
```
