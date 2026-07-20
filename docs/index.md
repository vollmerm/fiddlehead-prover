# Fiddlehead

Fiddlehead is a small theorem prover written in Python.

## What it does

Fiddlehead works with first-order terms and equality goals:

- Normalize terms with rewrite rules
- Reason about equalities in context
- Prove simple clauses with a waterfall of simplification, forward chaining, branching, and induction
- Infer and check sorts
- Load small theories with scoped rewrites and induction schemes

## Quick Start

```python
from fiddlehead import *

x = V("x", "Nat")
zero = Const("0")
S = lambda t: App("S", t)
add = lambda a, b: App("add", a, b)
eq = lambda a, b: App("eq", a, b)

engine = make_engine(rules=builtin_rules())
install_theory(engine, nat_theory())

goal = Clause((), eq(add(x, zero), x))
prove(goal, engine, var=x)  # induction scheme inferred from x's sort
```

## Installation

```bash
git clone https://github.com/vollmerm/fiddlehead-prover.git
cd fiddlehead-prover
python -m venv .venv
source .venv/bin/activate
pip install -e .
```

## Documentation

- [Public API Guide](public-api.md)
- [Integer Arithmetic Tutorial](integer-theory.md)
- [Hoare Logic Tutorial](hoare-logic-tutorial.md)
- `examples/` directory for larger proof scripts
