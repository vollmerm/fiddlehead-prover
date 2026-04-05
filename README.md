# Fiddlehead

Fiddlehead is a tiny proof assistant with a pleasantly mossy vibe: a pocket-sized theorem prover for rewriting terms, chasing equalities, and occasionally coaxing induction into doing something clever.

It exposes a public Python API through `fiddlehead.prover`. Under the hood it supports:

- first-order terms 
- rewrite rules and normalization
- clause proving with simplification, branching, and induction
- strict sort inference and checking
- theorem environments, scoped rewrites, and interactive proof sessions

## Public-facing API

The main entrypoint is:

```python
from fiddlehead.prover import *
```

The most useful pieces are:

| API | Purpose |
| --- | --- |
| `V`, `Const`, `App` | Build variables, constants, and terms |
| `Rule`, `builtin_rules` | Define rewrite systems |
| `make_engine`, `EngineConfig` | Create prover state |
| `normalize` | Rewrite a term to normal form |
| `Clause`, `simplify_clause`, `prove` | Work with proof goals |
| `InductionScheme`, `prove_with_induction` | Prove by structural induction |
| `SortSignature`, `register_sort_signature`, `infer_sort` | Define and inspect sorts |
| `nat_theory`, `list_theory`, `install_theory` | Load common theory fragments |
| `ProofSession` | Drive proofs interactively |

## Examples

```python
from fiddlehead.prover import *

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
from fiddlehead.prover import *

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

## Project layout

- `src/fiddlehead/prover.py`: public facade
- `src/fiddlehead/syntax.py`: terms, variables, substitution, matching
- `src/fiddlehead/kernel.py`: engine, rewriting, typing, tracing
- `src/fiddlehead/proof.py`: clauses, proof search, certificates
- `src/fiddlehead/theory.py`: theories, theorem environments, sessions

## Development

Run tests from the repository root with:

```bash
python3 -m pytest -q
```
