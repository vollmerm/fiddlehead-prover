# Understanding the Fiddlehead prover core

Fiddlehead is a small theorem prover, but it is meant to be read, not just used.
The public API still comes through `fiddlehead.prover`, while the implementation
is split across focused modules in `src/fiddlehead/` such as `syntax.py`,
`kernel.py`, `proof.py`, `theory.py`, `session.py`, `trace.py`, and
`validation.py`.

The guiding idea is simple: **rewrite terms as far as possible, use contextual
equalities when rewriting is not enough, and bring in induction only when the
goal really needs it**.

This document walks through the prover in roughly the same order that the code
uses when it runs.

## 1. Terms: the prover's basic language

Everything in Fiddlehead is a term. There are two term forms:

- `Var(name, sort)` for variables
- `Fun(symbol, args)` for function applications

Constants such as `0`, `nil`, `true`, and `false` are just arity-0 functions.

Two implementation details matter in practice:

1. `Fun` terms are hash-consed, so repeated constructions often share identity.
2. Variables are created through `V(name, sort)` and interned per session, so
   the prover gets stable variable identity and consistent sorts.

That lets the implementation take a few fast paths without making identity part
of the logical meaning of a term.

## 2. Substitution and matching: how rewrite rules apply

Rewriting is driven by first-order matching.

- `match(pattern, target)` tries to build a substitution that makes a rule's
  left-hand side fit a target term.
- `apply_subst(term, subst)` applies that substitution to produce the rewritten
  result.

When the same pattern variable appears more than once, the matcher checks it
carefully. It uses identity when that is enough, but falls back to semantic
equality when needed. That keeps matching efficient without making it brittle.

## 3. Rewrite orientation: keeping simplification pointed in one direction

Unconditional rewrites are only accepted when they move in a decreasing
direction according to a lightweight LPO-style ordering.

That ordering lives in engine configuration rather than in global state. In
practice, it uses:

- a precedence map (`symbol -> priority`)
- AC metadata (`assoc`, `comm`) used during AC normalization

The goal is not to prove perfect termination properties. The goal is to keep the
rewrite system disciplined enough that normalization usually moves forward
instead of wandering.

## 4. Equality closure in context: using assumptions effectively

Goals are proved under a `Context` that can contain equalities and
disequalities.

The important detail is that **not every equality is handled the same way**.
When a clause is turned into a `Context`, the prover splits its equalities into
three buckets:

1. **Substitutions** such as `x = 0` or `ys = nil`, where one side is a bare
   variable
2. **Ground equalities** such as `0 = S(0)`, where both sides are closed terms
3. **Rewrite equalities** such as induction hypotheses, where matching is
   needed before they can be used

Substitutions and ground equalities go into union-find congruence closure
(`EqClasses`). Rewrite equalities do not. Instead, they are oriented into local
schematic rewrite rules.

That split is what lets the prover do three different jobs without confusing
them:

- treat `x = t` like a local binding
- use closed equalities for congruence-based canonicalization
- still rewrite with non-ground facts such as induction hypotheses

Once substitutions and ground equalities are loaded, the prover builds
equivalence classes with union-find (`EqClasses`) and closes them under
congruence. That means:

- if `a = b`, then `f(a)` and `f(b)` are treated as the same when both matter
- if the context contains `x = y` and `y = 0`, the prover can use `x = 0`

This is what allows local assumptions to help with normalization and with
checking rule conditions, while rewrite-style contextual facts stay available as
actual rewrites instead of being forced into the congruence engine.

### 4.1 Context-aware disequality simplification

While simplifying `eq(...)` and `neq(...)`, the prover also consults local
disequalities through congruence closure.

That matters in two common situations:

1. **Conditional rewrites.** If a rule requires `neq(k1, k2) = true`, a
   branch-local disequality can make that condition succeed.
2. **Case splits through `if`.** The map theory uses terms like
   `if_(eq(k1, k), some(v), get(m, k))`. If the context says `k != k1`, then
   `eq(k1, k)` simplifies to `false`, so the term reduces to the else branch.

Two design choices keep this sound:

- Disequalities stay local to the clause currently being simplified. They are
  not turned into global rewrite rules.
- Disequality checks happen after congruence-based canonicalization, so they
  apply to equivalent representatives, not just to the original spelling of a
  term.

Another small but important detail is timing: `eq(...)` and `neq(...)` are
checked against contextual equality and disequality information **before** the
prover falls back to generic rewrite rules. So if the context already entails
that two terms are equal, `eq(lhs, rhs)` becomes `true` immediately; if the
context entails that they are different, it becomes `false`. `neq(...)` works
the same way in the opposite direction.

## 5. `Engine`: the container for run-specific state

All state that matters for a proof run lives in `Engine`.

An engine holds:

- rewrite rules and the rule index
- the current context
- per-engine configuration for precedence and AC metadata
- a per-run memo cache
- an engine-scoped ground cache
- an engine-scoped induction scheme registry
- optional trace settings and fuel bounds

Because this state is explicit, callers can decide whether they want strict
isolation or deliberate sharing. Nothing depends on hidden module-global prover state.

## 6. What normalization actually does

`normalize(term, engine)` runs the engine's normalization loop. At a high level,
that loop:

1. builds or extends context equality classes for the current term
2. canonicalizes the term with substitutions and ground equalities
3. recursively rewrites subterms
4. AC-normalizes where the engine says a symbol is associative or commutative
5. canonicalizes again after the subterms have changed
6. simplifies `eq(...)` and `neq(...)` directly from contextual equality or
   disequality information when possible
7. tries indexed engine rewrite rules
8. tries contextual schematic rewrites coming from `rewrite_equalities`
9. repeats until it reaches a fixpoint or runs out of fuel

Ground terms are memoized in the engine-scoped ground cache, so repeated
normalization of the same closed term can be reused on purpose when engines
share cache state.

One subtle point here is that the two rewrite sources play different roles.
Ordinary engine rules are the globally installed rewrite system and must respect
the engine's decrease check unless they are explicitly marked otherwise.
Contextual schematic rewrites are local facts, so they are allowed to act more
like targeted one-off rewrite rules.

## 7. Clauses and the waterfall prover

A proof goal is represented as:

- `Clause(assumptions, goal, disequalities)`

The prover now runs a small waterfall over that clause. Its main stages are:

1. simplify the goal under its local assumptions
2. prune branches whose local equalities contradict their local disequalities
3. check whether the result is `true`
4. split `if(...)` terms into branches
5. add local facts from active forward-chaining rules
6. try goal-level transformations such as fertilization
7. if induction is available, try destructor elimination, generalization, and then induction
8. recurse with depth control on the resulting obligations

The branch rules are straightforward:

- `if(eq(a, b), t, e)` adds `a = b` to the then-branch and `a != b` to the
  else-branch
- a general boolean `if(c, t, e)` adds `c = true` or `c = false`

That keeps proof search readable while still letting the prover do more than a
pure simplify/split loop.

The pruning step is worth calling out because it is easy to miss when only
reading the public API. After simplification, the prover asks whether any
branch-local disequality is already contradicted by the branch's equalities. If
so, that branch is treated as a dead end and the search stops there instead of
spending more effort on it.

## 8. Induction as generated obligations

Induction is explicit and driven by induction schemes.

- `InductionScheme` describes the base cases and constructors
- `induction_branches(...)` generates the resulting obligations
- step cases include induction hypotheses as assumptions

Within the waterfall, induction is a later stage rather than the first move.
`prove_with_induction(...)` fixes the induction target up front, then the prover
may first use:

- destructor elimination to replace selector-style terms by fresh variables
- generalization to replace rigid repeated structure by fresh variables tied
  back to the originals with equalities

That generalization step is optional, but it matters because it can strengthen
the clause enough that the resulting induction hypotheses become usable. After
that, induction expands in the usual way and still respects the configured
induction-depth bound.

Because induction schemes are engine-scoped, different engines can expose
different inductive worlds. One engine might know about naturals, another about
lists, and another about both.

## 9. Proof traces: reading proofs as proof stories

Fiddlehead can record a proof-level trace that explains the shape of a proof
instead of only showing low-level rewrite steps.

The trace is built out of `ProofNode` events and stored as a `ProofTrace` tree.
The main entry points are:

- `prove_with_trace(...)`, which returns `(result, trace)`
- `render_proof_trace(trace)`, which prints the tree in a readable form
- `render_waterfall_trace(trace)`, which groups the same run by waterfall stage

The useful part is what the trace emphasizes:

- each proof attempt
- the result of simplification
- where forward chaining fired
- where fertilization or generalization changed the clause
- branch splits and branch outcomes
- where induction was introduced
- the subproofs for each induction branch
- whether each node was solved or failed

So when a theorem succeeds by induction, the trace makes that visible in a
human-readable way.

## 10. Checked proofs: certificates and replay

Fiddlehead separates proof search from proof checking with a small certificate
layer.

- `prove_checked(...)` runs the same waterfall-backed search as ordinary proving
  and returns a `ProofCertificate` tree
- `check_certificate(...)` replays that certificate against the current rules,
  context behavior, and induction schemes

Certificate nodes record:

- the original clause
- the simplified clause
- the step kind (`solved`, `split`, `forward-chain`, `fertilize`,
  `destructor-elim`, `generalize`, `induction`)
- child certificates
- induction metadata such as `var` and `scheme_name` when relevant

That keeps automation lightweight while still making successful proofs
independently checkable.

## 11. Interactive proving in Python: `ProofSession`

`ProofSession` is the small interactive layer for working with clause goals from
Python.

It includes:

- core tactics such as `simp`, `split`, `induct`, `induct_many`, `rewrite`,
  `exact`, `apply_lemma`, and `qed`
- theorem-environment hooks such as `register_lemma(...)`,
  `register_definition(...)`, `register_recursive_definition(...)`,
  `register_lemma_rewrite(...)`,
  `activate_scope(...)`, and `deactivate_scope(...)`
- assumption-level helpers such as `assumptions()` and
  `keep_assumptions(...)`, which are especially useful when you want explicit
  control over induction hypotheses

The design stays conservative:

- every command goes through checked step helpers
- session state stays explicit (`goals`, `engine`, theorem environment, and
  trace)
- the behavior stays close to the prover's ordinary semantics

`ProofSession` also records a proof-structure trace, so interactive sessions can
be rendered with `render_proof_trace(...)` just like automated runs.

## 12. One narrative format across proving modes

Proof explanations can come from three related paths:

- direct proof search tracing with `prove_with_trace(...)`
- certificate replay structure with `certificate_to_proof_trace(...)`
- interactive session history through `ProofSession.trace`

All three use the same `ProofTrace` and `ProofNode` model. That keeps the output
consistent without adding a separate explanation system for each proving mode.

## 13. The theorem environment: named facts and scoped rewrites

`TheoremEnvironment` is engine-scoped state for managing named facts and
definitions.

It supports:

- named lemmas backed by validated certificates
- named non-recursive definitions and recursive definitions (as checked scoped rewrite sets)
- rule classes, including rewrite rules and forward-chaining rules
- scoped rule sets that can be activated and deactivated

Public entry points for recursive-definition workflows are:

- `register_recursive_definition(engine, ...)`
- `get_theorem_environment(engine).register_recursive_definition(...)`
- `ProofSession.register_recursive_definition(...)`

A few behaviors matter here:

- activating a scope rebuilds the engine's active rewrite rules from
  `base_rules + active rewrite-class rules in active scopes`
- forward-chaining-class rules stay available to the waterfall prover without
  becoming ordinary rewrite rules during normalization
- registering a lemma as a rewrite checks orientation safety with
  `_decreases(...)`
- non-orientable equalities are rejected instead of being accepted silently

This keeps theorem growth explicit and avoids a hidden global stockpile of
active facts.

## 14. Induction support in the tactic layer

Interactive induction supports three styles:

- explicit scheme selection with `induct(var, scheme=...)`
- named scheme lookup with `induct(var, scheme_name=...)`
- sort-driven auto-selection with `induct(var)` when `var.sort` has a
  registered scheme

`induct_many(...)` performs nested structural induction over multiple variables
and expands all resulting branch obligations.

Control over induction hypotheses is still explicit. You inspect assumptions
with `assumptions()` and retain the ones you want, including IHs, with
`keep_assumptions(indices)`.

## 15. Safer automation through staged simplification

Clause simplification has an explicit staged pipeline through
`simplify_clause_with_stages(...)`:

1. simplify and canonicalize assumptions
2. normalize the goal using rules only
3. normalize again with contextual reasoning, including congruence closure and
   conditional rewriting
4. close the goal to `true` when the context already entails the needed equality

`ProofSession.simp()` records these stages as `stage-*` trace nodes, which makes
stronger automation easier to inspect instead of harder.

## 16. Strict, inference-first typing

The prover uses an engine-scoped type-signature registry (`SortSignature`) with
strict typing rules.

In practice, that means:

- every function or constructor symbol used in terms must have a declared
  signature
- missing variable annotations are represented by inference variables and solved
  by unification
- parameterized sort annotations such as `List` come from registered
  sort-constructor arities rather than from validation-specific special cases
- `infer_sort(...)` rejects a term if its inferred type remains ambiguous

The signature model also supports linked type variables inside a symbol schema,
for example `cons : A -> List[A] -> List[A]`.

Typing checks happen when:

- rules enter the engine through `make_engine(...)`, rule resets, theorem
  rewrites, or definitions
- clauses enter simplification and proof search through
  `simplify_clause_with_stages(...)`
- interactive tactics introduce or transform goals

The main API entry points are:

- `register_sort_signature(engine, symbol, SortSignature(...))`
- `get_sort_signature(engine, symbol)`
- `infer_type(term, engine)` for inferred type terms
- `infer_sort(term, engine)` when you need a concrete, non-ambiguous sort

This keeps the typing story compact and predictable: one explicit unification
model and no permissive fallback path.
