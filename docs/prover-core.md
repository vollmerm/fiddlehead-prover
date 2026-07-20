# The Fiddlehead prover core

Fiddlehead is a small first-order theorem prover written to be read as well as
used. The public API comes through `fiddlehead.prover`; the implementation
lives in focused modules under `src/fiddlehead/`: `syntax.py`, `kernel.py`,
`proof.py`, `theory.py`, `session.py`, `trace.py`, and `validation.py`.

The design follows one idea: rewrite terms as far as possible, use contextual
equalities when rewriting is not enough, and bring in induction only when the
goal needs it.

This guide follows the prover in roughly the order the code runs.

## 1. Terms

Everything in Fiddlehead is a term, in one of two forms:

- `Var(name, sort)` for variables
- `Fun(symbol, args)` for function applications

Constants such as `0`, `nil`, `true`, and `false` are arity-0 functions.

Two implementation details are visible from the API:

1. `Fun` terms are hash-consed, so repeated constructions often share identity.
2. Variables are created through `V(name, sort)` and interned per session,
   which gives them stable identity and consistent sorts.

Hash-consing gives the implementation fast identity checks without making
identity part of the logical meaning of a term.

## 2. Substitution and matching

Rewriting is driven by first-order matching.

- `match(pattern, target)` builds a substitution that makes a rule's left-hand
  side fit a target term, or fails.
- `apply_subst(term, subst)` applies that substitution to produce the rewritten
  result.

When a pattern variable appears more than once, the matcher compares the bound
occurrences by identity first and falls back to semantic equality when identity
is not enough.

## 3. Rewrite orientation

Unconditional rewrites are accepted only when they decrease under a lightweight
LPO-style ordering. The ordering is part of engine configuration, not global
state, and is built from:

- a precedence map from symbol to priority
- AC metadata (`assoc`, `comm`) used during AC normalization

The ordering does not prove termination in any formal sense. It keeps the
rewrite system disciplined enough that normalization makes progress instead of
wandering.

## 4. Equality closure in context

Goals are proved under a `Context` that can contain equalities and
disequalities.

When a clause is turned into a `Context`, its equalities are split into three
groups:

1. Substitutions such as `x = 0` or `ys = nil`, where one side is a bare
   variable.
2. Ground equalities such as `0 = S(0)`, where both sides are closed terms.
3. Rewrite equalities such as induction hypotheses, which need matching before
   they can be used.

Substitutions and ground equalities go into union-find congruence closure
(`EqClasses`). Rewrite equalities are instead oriented into local schematic
rewrite rules.

The split lets each kind of equality do the job it is suited for: `x = t` acts
like a local binding, closed equalities feed congruence-based
canonicalization, and non-ground facts such as induction hypotheses stay
usable as rewrites.

After loading substitutions and ground equalities, the prover builds
equivalence classes with union-find and closes them under congruence:

- if `a = b`, then `f(a)` and `f(b)` are treated as the same term
- if the context contains `x = y` and `y = 0`, the prover can use `x = 0`

Local assumptions can therefore help with normalization and with checking rule
conditions, while rewrite-style contextual facts remain available as rewrites
rather than being forced into the congruence engine.

### 4.1 Disequality simplification

While simplifying `eq(...)` and `neq(...)`, the prover also consults local
disequalities through congruence closure. This helps in two common situations:

1. Conditional rewrites. If a rule requires `neq(k1, k2) = true`, a
   branch-local disequality can satisfy the condition.
2. Case splits through `if`. The map theory uses terms like
   `if_(eq(k1, k), some(v), get(m, k))`. If the context says `k != k1`, then
   `eq(k1, k)` simplifies to `false` and the term reduces to the else branch.

Two design choices keep this sound:

- Disequalities stay local to the clause being simplified; they never become
  global rewrite rules.
- Disequality checks run after congruence-based canonicalization, so they
  apply to equivalent representatives, not just the original spelling of a
  term.

Timing also matters: contextual equality and disequality information is
consulted before generic rewrite rules. If the context already entails that
two terms are equal, `eq(lhs, rhs)` becomes `true` immediately; if it entails
that they differ, it becomes `false`. `neq(...)` behaves symmetrically.

## 5. The `Engine`

All state that matters for a proof run lives in an `Engine`:

- rewrite rules and the rule index
- the current context
- per-engine configuration for precedence and AC metadata
- a per-run memo cache
- an engine-scoped ground cache
- an engine-scoped induction scheme registry
- optional trace settings and fuel bounds

Because this state is explicit, callers choose between strict isolation and
deliberate sharing. Nothing depends on hidden module-global state.

## 6. Normalization

`normalize(term, engine)` runs the engine's normalization loop:

1. build or extend context equality classes for the current term
2. canonicalize the term with substitutions and ground equalities
3. recursively rewrite subterms
4. AC-normalize where the engine marks a symbol associative or commutative
5. canonicalize again after the subterms have changed
6. simplify `eq(...)` and `neq(...)` directly from contextual equality or
   disequality information when possible
7. try indexed engine rewrite rules
8. try contextual schematic rewrites from `rewrite_equalities`
9. repeat until fixpoint or until the fuel bound runs out

Ground terms are memoized in the engine-scoped ground cache, so engines that
share cache state can reuse normalization results for closed terms.

The two rewrite sources play different roles. Engine rules form the globally
installed rewrite system and must pass the engine's decrease check unless
explicitly marked otherwise. Contextual schematic rewrites are local facts and
may act as targeted one-off rules.

## 7. Clauses and the waterfall prover

A proof goal is a `Clause(assumptions, goal, disequalities)`. The prover runs
a waterfall over that clause:

1. simplify the goal under its local assumptions
2. prune branches whose local equalities contradict their local disequalities
3. check whether the result is `true`
4. split `if(...)` terms into branches
5. add local facts from active forward-chaining rules
6. try goal-level transformations such as fertilization
7. if induction is available, try destructor elimination, generalization, and
   then induction
8. recurse with depth control on the resulting obligations

Branching follows two rules:

- `if(eq(a, b), t, e)` adds `a = b` to the then-branch and `a != b` to the
  else-branch
- a general boolean `if(c, t, e)` adds `c = true` or `c = false`

Pruning happens right after simplification: if a branch-local disequality is
already contradicted by the branch's equalities, the branch is a dead end and
the search stops there instead of spending more effort on it.

## 8. Induction

Induction is explicit and driven by induction schemes:

- `InductionScheme` describes the base cases and constructors
- `induction_branches(...)` generates the resulting obligations
- step cases include induction hypotheses as assumptions

Within the waterfall, induction comes late rather than first.
Passing `var=` (and optionally `scheme=`) to `prove(...)` fixes the induction
target up front; before inducting, the prover may apply:

- destructor elimination, which replaces selector-style terms by fresh
  variables
- generalization, which replaces rigid repeated structure by fresh variables
  tied back to the originals with equalities

Generalization is optional, but it can strengthen a clause enough that the
resulting induction hypotheses become usable. After that, induction expands as
usual and respects the configured induction-depth bound.

Induction schemes are engine-scoped, so different engines can register
different schemes: one engine might know about naturals, another about lists,
another about both.

## 9. Proof traces

Fiddlehead can record a proof-level trace that explains the shape of a proof
rather than individual rewrite steps.

The trace is a `ProofTrace` tree built from `ProofNode` events. The main entry
points are:

- `prove(...)`, whose `ProofResult` carries the tree as `result.trace`
- `render_proof_trace(trace)`, which prints the tree
- `render_waterfall_trace(trace)`, which groups the same run by waterfall stage

The trace records:

- each proof attempt
- the result of simplification
- where forward chaining fired
- where fertilization or generalization changed the clause
- branch splits and branch outcomes
- where induction was introduced
- the subproofs for each induction branch
- whether each node was solved or failed

When a theorem succeeds by induction, the trace shows where the induction
happened and how each branch was closed.

## 10. Certificates and replay

Proof search and proof checking are separated by a small certificate layer.

- `prove_checked(...)` runs the same waterfall-backed search as ordinary
  proving and returns a `ProofCertificate` tree
- `check_certificate(...)` replays that certificate against the current rules,
  context behavior, and induction schemes

Certificate nodes record:

- the original clause
- the simplified clause
- the step kind (`solved`, `split`, `forward-chain`, `fertilize`,
  `destructor-elim`, `generalize`, `induction`)
- child certificates
- induction metadata such as `var` and `scheme_name` when relevant

Automation stays lightweight, and successful proofs can be checked
independently of the search that found them.

## 11. Interactive proving: `ProofSession`

`ProofSession` is the interactive layer for working with clause goals from
Python. It provides:

- core tactics: `simp`, `split`, `induct`, `induct_many`, `rewrite`, `exact`,
  `apply_lemma`, and `qed`
- theorem-environment hooks: `register_lemma(...)`,
  `register_definition(...)`, `register_recursive_definition(...)`,
  `register_lemma_rewrite(...)`, `activate_scope(...)`, and
  `deactivate_scope(...)`
- assumption helpers: `assumptions()` and `keep_assumptions(...)`, useful when
  you want explicit control over induction hypotheses

Every command goes through checked step helpers, session state is explicit
(`goals`, `engine`, theorem environment, and trace), and tactic behavior stays
close to the prover's ordinary semantics.

`ProofSession` also records a proof-structure trace, so interactive sessions
can be rendered with `render_proof_trace(...)` just like automated runs.

## 12. One trace format across proving modes

Proof explanations come from three paths:

- direct proof search via `prove(...).trace`
- certificate replay with `certificate_to_proof_trace(...)`
- interactive history through `ProofSession.trace`

All three produce the same `ProofTrace` and `ProofNode` model, so there is one
explanation format rather than one per proving mode.

## 13. The theorem environment

`TheoremEnvironment` is engine-scoped state for named facts and definitions.
It supports:

- named lemmas backed by validated certificates
- named non-recursive and recursive definitions (as checked scoped rewrite
  sets)
- rule classes, including rewrite rules and forward-chaining rules
- scoped rule sets that can be activated and deactivated

The entry points for recursive definitions are:

- `register_recursive_definition(engine, ...)`
- `get_theorem_environment(engine).register_recursive_definition(...)`
- `ProofSession.register_recursive_definition(...)`

Behavior to be aware of:

- activating a scope rebuilds the engine's active rewrite rules from
  `base_rules` plus the rewrite-class rules in active scopes
- forward-chaining-class rules stay available to the waterfall prover without
  becoming rewrite rules during normalization
- registering a lemma as a rewrite checks orientation safety with
  `_decreases(...)`
- non-orientable equalities are rejected rather than accepted silently

Theorem growth stays explicit; there is no hidden global pool of active facts.

## 14. Induction in the tactic layer

Interactive induction supports three styles:

- explicit scheme selection: `induct(var, scheme=...)`
- named scheme lookup: `induct(var, scheme_name=...)`
- sort-driven auto-selection: `induct(var)` when `var.sort` has a registered
  scheme

`induct_many(...)` performs nested structural induction over multiple
variables and expands all resulting branch obligations.

Induction hypotheses stay under your control: inspect assumptions with
`assumptions()` and keep the ones you want with `keep_assumptions(indices)`.

## 15. Staged simplification

`simplify_clause_with_stages(...)` runs clause simplification as an explicit
pipeline:

1. simplify and canonicalize assumptions
2. normalize the goal using rules only
3. normalize again with contextual reasoning, including congruence closure and
   conditional rewriting
4. close the goal to `true` when the context already entails the needed
   equality

`ProofSession.simp()` records these stages as `stage-*` trace nodes, so you
can see which stage did the work.

## 16. Typing

The prover uses an engine-scoped type-signature registry (`SortSignature`)
with strict typing rules:

- every function or constructor symbol used in terms must have a declared
  signature
- missing variable annotations become inference variables and are solved by
  unification
- parameterized sorts such as `List` come from registered sort-constructor
  arities, not from validation special cases
- `infer_sort(...)` rejects a term whose inferred type remains ambiguous

Symbol schemas can link type variables, for example
`cons : A -> List[A] -> List[A]`.

Typing is checked when:

- rules enter the engine through `make_engine(...)`, rule resets, theorem
  rewrites, or definitions
- clauses enter simplification and proof search through
  `simplify_clause_with_stages(...)`
- interactive tactics introduce or transform goals

The API entry points are:

- `register_sort_signature(engine, symbol, SortSignature(...))`
- `get_sort_signature(engine, symbol)`
- `infer_type(term, engine)` for inferred type terms
- `infer_sort(term, engine)` when you need a concrete, non-ambiguous sort

There is one unification model and no permissive fallback path.
