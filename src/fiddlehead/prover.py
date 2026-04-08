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

Public API (small, stable surface):
- term constructors: V, Const, App
- proving entry points: normalize, prove, prove_with_induction, prove_with_registered_induction
- checked proving entry points: prove_checked, check_certificate
- typing APIs: SortSignature, register_sort_signature, infer_type, infer_sort
- induction registration: register_induction_scheme, get_induction_scheme, get_induction_scheme_for_sort
- theory + theorem environment/session: Theory, nat_theory, list_theory, load_theory_module,
  install_theory, get_theorem_environment, TheoremEnvironment, ProofSession
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
    certificate_to_proof_trace,
    check_certificate,
    clause_solved,
    induction_branches,
    prove,
    prove_checked,
    prove_with_auto_induction,
    prove_with_induction,
    prove_with_registered_induction,
    prove_with_trace,
    simplify_clause,
)
from .session import ProofSession
from .syntax import App, Const, V, apply_subst, false, match, reset_var_interner, true
from .trace import (
    ProofNode,
    ProofTrace,
    Trace,
    render_proof_trace,
    render_waterfall_trace,
)
from .theory import (
    Lemma,
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
    register_recursive_definition,
    theory_from_module,
    tree_theory,
)

__all__ = [
    "Term",
    "TypeTerm",
    "TypeVar",
    "TypeConst",
    "Var",
    "Fun",
    "V",
    "reset_var_interner",
    "Const",
    "App",
    "true",
    "false",
    "Rule",
    "Clause",
    "Context",
    "InductionConstructor",
    "InductionScheme",
    "nat_induction_scheme",
    "list_induction_scheme",
    "map_induction_scheme",
    "tree_induction_scheme",
    "nat_theory",
    "int_theory",
    "list_theory",
    "map_theory",
    "tree_theory",
    "register_induction_scheme",
    "get_induction_scheme",
    "get_induction_scheme_for_sort",
    "make_engine",
    "EngineConfig",
    "SortSignature",
    "default_engine_config",
    "default_sort_signatures",
    "builtin_rules",
    "register_sort_signature",
    "get_sort_signature",
    "infer_type",
    "infer_sort",
    "match",
    "apply_subst",
    "normalize",
    "prove",
    "prove_with_auto_induction",
    "prove_with_induction",
    "prove_with_registered_induction",
    "simplify_clause",
    "clause_solved",
    "induction_branches",
    "ProofTrace",
    "ProofNode",
    "render_proof_trace",
    "render_waterfall_trace",
    "prove_with_trace",
    "ProofCertificate",
    "certificate_to_proof_trace",
    "prove_checked",
    "check_certificate",
    "Lemma",
    "RuleSource",
    "Theory",
    "theory_from_module",
    "load_theory_module",
    "install_theory",
    "TheoremEnvironment",
    "get_theorem_environment",
    "register_recursive_definition",
    "ProofSession",
    "Trace",
]
