from __future__ import annotations

"""
Boyer–Moore style rewriting core with:
- hash-consed terms
- LPO ordering
- AC normalization
- contextual rewriting (substitution-based)
- clause reasoning
- tracing
- term indexing
- ground-term caching
- per-call memoization
- conditional rewriting
- negation and split
- congruence closure
- induction schemes
- checked proof certificates
- interactive theorem environment/session
- strict inference-first term typing
- modular theory packages

Public API (small, stable surface — see ``__all__``):
- term constructors: V, Const, App
- term builders: fn, plus ready-made builders for the builtin and core-theory
  symbols (eq, neq, if_, not_, and_, or_, S, zero, add, mul, nil, cons,
  append, length)
- proving entry points: normalize, prove (returns ProofResult)
- checked proving entry points: prove_checked, check_certificate
- typing APIs: SortSignature, register_sort_signature, infer_type, infer_sort
- induction registration: register_induction_scheme, get_induction_scheme, get_induction_scheme_for_sort
- theory + theorem environment/session: Theory, nat_theory, list_theory, load_theory_module,
  install_theory, get_theorem_environment, TheoremEnvironment, ProofSession

Advanced names (TypeVar, Fun, EngineConfig, rule classes, trace internals, ...)
are not star-exported; import them explicitly from this module or from the
submodule that defines them (fiddlehead.syntax, .kernel, .proof, .trace,
.rule_classes, .generalize, .theory).
"""

from .kernel import (
    Context,
    Engine,
    EngineConfig,
    Fun,
    InductionConstructor,
    InductionScheme,
    Rule,
    SortSignature,
    Term,
    TypeConst,
    TypeTerm,
    TypeVar,
    Var,
    builtin_rules,
    default_engine_config,
    default_sort_signatures,
    get_induction_scheme,
    get_induction_scheme_for_sort,
    get_sort_signature,
    infer_sort,
    infer_type,
    int_induction_scheme,
    list_induction_scheme,
    make_engine,
    map_induction_scheme,
    nat_induction_scheme,
    normalize,
    register_induction_scheme,
    register_sort_signature,
    tree_induction_scheme,
)
from .proof import (
    Clause,
    ProofCertificate,
    ProofResult,
    certificate_to_proof_trace,
    check_certificate,
    clause_solved,
    fertilize_clause,
    induction_branches,
    prove,
    prove_checked,
    simplify_clause,
)
from .generalize import destructor_elim_clause
from .rule_classes import (
    RuleClass,
    RuleClassSpec,
    forward_chaining_rule_class,
    rewrite_rule_class,
)
from .session import ProofSession
from .syntax import (
    App,
    Const,
    S,
    V,
    add,
    and_,
    append,
    apply_subst,
    cons,
    eq,
    false,
    fn,
    if_,
    length,
    match,
    mul,
    neq,
    nil,
    not_,
    or_,
    reset_var_interner,
    true,
    zero,
)
from .trace import (
    ProofNode,
    ProofTrace,
    Trace,
    render_proof_trace,
    render_waterfall_trace,
)
from .theory import (
    Lemma,
    NamedRuleInfo,
    RuleSource,
    TheoremEnvironment,
    Theory,
    get_theorem_environment,
    install_theory,
    int_theory,
    list_theory,
    load_theory_module,
    map_theory,
    nat_theory,
    register_int_lemmas,
    register_recursive_definition,
    theory_from_module,
    tree_theory,
)

__all__ = [
    # terms
    "Term",
    "Var",
    "V",
    "Const",
    "App",
    "true",
    "false",
    "reset_var_interner",
    # term builders
    "fn",
    "eq",
    "neq",
    "if_",
    "not_",
    "and_",
    "or_",
    "S",
    "zero",
    "add",
    "mul",
    "nil",
    "cons",
    "append",
    "length",
    # rules and clauses
    "Rule",
    "Clause",
    # engine
    "Engine",
    "make_engine",
    "builtin_rules",
    # proving
    "normalize",
    "prove",
    "prove_checked",
    "check_certificate",
    "ProofResult",
    "ProofCertificate",
    "simplify_clause",
    "induction_branches",
    # traces
    "ProofTrace",
    "render_proof_trace",
    # sorts and typing
    "SortSignature",
    "TypeConst",
    "register_sort_signature",
    "infer_sort",
    "infer_type",
    # induction schemes
    "InductionScheme",
    "InductionConstructor",
    "register_induction_scheme",
    "get_induction_scheme",
    "get_induction_scheme_for_sort",
    # theories
    "Theory",
    "Lemma",
    "nat_theory",
    "int_theory",
    "list_theory",
    "map_theory",
    "tree_theory",
    "install_theory",
    "load_theory_module",
    "TheoremEnvironment",
    "get_theorem_environment",
    "register_recursive_definition",
    "register_int_lemmas",
    # interactive sessions
    "ProofSession",
]
