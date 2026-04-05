# Fiddlehead

Fiddlehead is a tiny proof assistant with a pleasantly mossy vibe: a pocket-sized theorem prover for rewriting terms, chasing equalities, and occasionally coaxing induction into doing something clever.

It exposes a public Python API through `fiddlehead`, which re-exports the stable interface from `fiddlehead.prover`. Under the hood it supports:

- first-order terms 
- rewrite rules and normalization
- clause proving with simplification, branching, and induction
- strict sort inference and checking
- theorem environments, scoped rewrites, and interactive proof sessions

## Public-facing API

The recommended entrypoint is:

```python
from fiddlehead import *
```

The lower-level module path also works:

```python
from fiddlehead.prover import *
```
## Examples

```python
from fiddlehead import *

reset_var_interner()

x = V("x", "Nat")
y = V("y", "Nat")
zero = Const("0")
S = lambda t: App("S", t)
add = lambda a, b: App("add", a, b)
eq = lambda a, b: App("eq", a, b)

engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory(), activate_scopes=True)

term = add(S(S(zero)), S(zero))
print(normalize(term, engine))  # S(S(S(0)))

goal = Clause((), eq(add(x, zero), x))
scheme = get_induction_scheme(engine, "nat")
assert scheme is not None
assert prove_with_induction(goal, engine, x, scheme, depth=8, induction_depth=1)
```

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

list_scheme = get_induction_scheme(engine, "list")
assert list_scheme is not None

goal = Clause((), eq(append(append(xs, ys), zs), append(xs, append(ys, zs))))
ok, trace = prove_with_trace(
    goal, engine, depth=12, var=xs, scheme=list_scheme, induction_depth=1
)
assert ok
print(render_proof_trace(trace))
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

Check out the `examples` folder for more:

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

## Project layout

- `src/fiddlehead/prover.py`: public facade
- `src/fiddlehead/syntax.py`: terms, variables, substitution, matching
- `src/fiddlehead/kernel.py`: engine, rewriting, typing, tracing
- `src/fiddlehead/proof.py`: clauses, proof search, certificates
- `src/fiddlehead/theory.py`: theories, theorem environments, sessions

## Installation

Clone the repo and install it locally for development:

```bash
git clone https://github.com/vollmerm/fiddlehead-prover.git
cd fiddlehead-prover
python -m venv .venv # or python3
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e .
```
