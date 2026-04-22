from __future__ import annotations

"""Theory packaging and theorem-environment management.

The theory layer lets callers bundle signatures, rules, lemmas, induction
schemes, and rewrite settings into installable modules with compatibility
checks, scoped activation, and rule synchronization.
"""

import importlib
from dataclasses import dataclass, field
from enum import Enum, auto
from fnmatch import fnmatch
from types import ModuleType
from typing import Dict, Optional, Tuple

from .kernel import (
    Engine,
    EngineConfig,
    InductionScheme,
    Rule,
    SortSignature,
    TypeConst,
    TypeVar,
    _decreases,
    get_induction_scheme,
    get_induction_scheme_for_sort,
    list_induction_scheme,
    make_engine,
    nat_induction_scheme,
    register_induction_scheme,
    register_sort_signature,
    tree_induction_scheme,
    var_matches_scheme,
)
from .proof import (
    Clause,
    ProofCertificate,
    _check_exact_step,
    _check_induction_step,
    _check_rewrite_step,
    check_certificate,
    clause_solved,
    goal_equality,
    simplify_clause_with_stages,
)
from .rule_classes import (
    RuleClass,
    RuleClassInput,
    RuleClassSpec,
    has_rule_class,
    normalize_rule_classes,
    rewrite_rule_class,
)
from .syntax import App, Const, Fun, Term, V, Var, false, true
from .validation import _validate_clause_sorts, _validate_rule_sorts


class RuleSource(Enum):
    """Provenance tracking for named rules."""

    THEORY = auto()
    DEFINITION = auto()
    LEMMA = auto()


@dataclass(frozen=True)
class Lemma:
    """A named proved clause plus its checked certificate."""

    name: str
    clause: Clause
    certificate: ProofCertificate


@dataclass(frozen=True)
class NamedRuleInfo:
    """Stored metadata for a named theorem-environment rule."""

    rule: Rule
    source: RuleSource
    rule_classes: Tuple[RuleClassSpec, ...] = ()


@dataclass(frozen=True)
class Theory:
    """An installable package of symbols, rules, lemmas, and settings."""

    name: str
    version: str = "0.0.1"
    depends_on: Tuple[str, ...] = ()
    sort_arities: Dict[str, int] = field(default_factory=dict)
    sort_signatures: Dict[str, SortSignature] = field(default_factory=dict)
    rules: Tuple[Rule, ...] = ()
    definitions: Dict[str, Rule] = field(default_factory=dict)
    lemmas: Tuple[Lemma, ...] = ()
    schemes: Tuple[InductionScheme, ...] = ()
    precedence: Dict[str, int] = field(default_factory=dict)
    assoc: Tuple[str, ...] = ()
    comm: Tuple[str, ...] = ()
    default_scopes: Tuple[str, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "depends_on", tuple(self.depends_on))
        object.__setattr__(self, "sort_arities", dict(self.sort_arities))
        object.__setattr__(self, "sort_signatures", dict(self.sort_signatures))
        object.__setattr__(self, "rules", tuple(self.rules))
        object.__setattr__(self, "definitions", dict(self.definitions))
        object.__setattr__(self, "lemmas", tuple(self.lemmas))
        object.__setattr__(self, "schemes", tuple(self.schemes))
        object.__setattr__(self, "precedence", dict(self.precedence))
        object.__setattr__(self, "assoc", tuple(self.assoc))
        object.__setattr__(self, "comm", tuple(self.comm))
        object.__setattr__(self, "default_scopes", tuple(self.default_scopes))


def nat_theory(name: str = "core.nat", version: str = "1.0.0") -> Theory:
    """Return a standard arithmetic theory over natural numbers."""

    x = V("nat_x")
    y = V("nat_y")
    zero = Const("0")

    def succ(term: Term) -> Term:
        return App("S", term)

    def add(left: Term, right: Term) -> Term:
        return App("add", left, right)

    def mul(left: Term, right: Term) -> Term:
        return App("mul", left, right)

    return Theory(
        name=name,
        version=version,
        sort_signatures={
            "add": SortSignature(
                (TypeConst("Nat"), TypeConst("Nat")), TypeConst("Nat")
            ),
            "mul": SortSignature(
                (TypeConst("Nat"), TypeConst("Nat")), TypeConst("Nat")
            ),
        },
        rules=(
            Rule(add(zero, y), y),
            Rule(add(succ(x), y), succ(add(x, y))),
            Rule(add(x, zero), x),
            Rule(add(x, succ(y)), succ(add(x, y))),
            Rule(mul(zero, y), zero),
            Rule(mul(succ(x), y), add(y, mul(x, y))),
        ),
        schemes=(nat_induction_scheme(zero),),
        precedence={"mul": 4, "add": 3},
        assoc=("add",),
        comm=("add",),
    )


def int_theory(name: str = "core.int", version: str = "1.0.0") -> Theory:
    """Return an integer ring-style theory in a dedicated Int namespace."""

    x = V("int_x", "Int")
    y = V("int_y", "Int")
    a = V("int_a", "Nat")
    b = V("int_b", "Nat")
    c = V("int_c", "Nat")
    d = V("int_d", "Nat")
    zero_nat = Const("0")
    one_nat = App("S", zero_nat)
    z0 = Const("z0")
    z1 = Const("z1")

    def succ(term: Term) -> Term:
        return App("S", term)

    def add_nat(left: Term, right: Term) -> Term:
        return App("add", left, right)

    def mul_nat(left: Term, right: Term) -> Term:
        return App("mul", left, right)

    def zint(pos_nat: Term, neg_nat: Term) -> Term:
        return App("zint", pos_nat, neg_nat)

    def zadd(left: Term, right: Term) -> Term:
        return App("zadd", left, right)

    def zmul(left: Term, right: Term) -> Term:
        return App("zmul", left, right)

    def zneg(term: Term) -> Term:
        return App("zneg", term)

    return Theory(
        name=name,
        version=version,
        depends_on=("core.nat",),
        sort_signatures={
            "z0": SortSignature((), TypeConst("Int")),
            "z1": SortSignature((), TypeConst("Int")),
            "zint": SortSignature(
                (TypeConst("Nat"), TypeConst("Nat")), TypeConst("Int")
            ),
            "zadd": SortSignature(
                (TypeConst("Int"), TypeConst("Int")), TypeConst("Int")
            ),
            "zmul": SortSignature(
                (TypeConst("Int"), TypeConst("Int")), TypeConst("Int")
            ),
            "zneg": SortSignature((TypeConst("Int"),), TypeConst("Int")),
        },
        rules=(
            Rule(z0, zint(zero_nat, zero_nat), skip_decrease_check=True),
            Rule(z1, zint(one_nat, zero_nat), skip_decrease_check=True),
            Rule(zadd(z0, y), y, skip_decrease_check=True),
            Rule(zadd(y, z0), y, skip_decrease_check=True),
            Rule(
                zadd(zint(a, b), zint(c, d)),
                zint(add_nat(a, c), add_nat(b, d)),
                skip_decrease_check=True,
            ),
            Rule(zneg(z0), z0),
            Rule(zneg(zint(a, b)), zint(b, a)),
            Rule(zmul(z0, y), z0, skip_decrease_check=True),
            Rule(zmul(y, z0), z0, skip_decrease_check=True),
            Rule(zmul(z1, y), y, skip_decrease_check=True),
            Rule(zmul(y, z1), y, skip_decrease_check=True),
            Rule(
                zmul(zint(a, b), zint(c, d)),
                zint(
                    add_nat(mul_nat(a, c), mul_nat(b, d)),
                    add_nat(mul_nat(a, d), mul_nat(b, c)),
                ),
                skip_decrease_check=True,
            ),
            Rule(zint(succ(a), succ(b)), zint(a, b)),
        ),
        precedence={"zneg": 5, "zmul": 4, "zadd": 3, "zint": 2},
        assoc=("zadd", "zmul"),
        comm=("zadd", "zmul"),
    )


def list_theory(name: str = "core.list", version: str = "1.0.0") -> Theory:
    """Return a standard list-processing theory."""

    a = TypeVar("A")
    head = V("list_xh")
    tail = V("list_xt", "List")
    xs = V("list_xs", "List")
    nil = Const("nil")

    def cons(left: Term, right: Term) -> Term:
        return App("cons", left, right)

    def append(left: Term, right: Term) -> Term:
        return App("append", left, right)

    def length(term: Term) -> Term:
        return App("length", term)

    zero = Const("0")

    def succ(term: Term) -> Term:
        return App("S", term)

    return Theory(
        name=name,
        version=version,
        sort_arities={"List": 1},
        sort_signatures={
            "nil": SortSignature((), TypeConst("List", (a,))),
            "cons": SortSignature(
                (a, TypeConst("List", (a,))), TypeConst("List", (a,))
            ),
            "append": SortSignature(
                (TypeConst("List", (a,)), TypeConst("List", (a,))),
                TypeConst("List", (a,)),
            ),
            "length": SortSignature((TypeConst("List", (a,)),), TypeConst("Nat")),
        },
        rules=(
            Rule(append(nil, xs), xs),
            Rule(append(cons(head, tail), xs), cons(head, append(tail, xs))),
            Rule(length(nil), zero),
            Rule(length(cons(head, tail)), succ(length(tail))),
        ),
        schemes=(list_induction_scheme(),),
        precedence={"append": 3, "length": 3, "cons": 2},
    )


def map_theory(name: str = "core.map", version: str = "1.0.0") -> Theory:
    """Return a finite-map theory with get/put operations and optional values."""

    k = TypeVar("K")
    v = TypeVar("V")
    m = V("map_m", "Map")
    j = V("map_j")
    key = V("map_k")
    val = V("map_v")

    empty = Const("empty")

    def put(map_term: Term, key_term: Term, val_term: Term) -> Term:
        return App("put", map_term, key_term, val_term)

    def get(map_term: Term, key_term: Term) -> Term:
        return App("get", map_term, key_term)

    none = Const("none")

    def some(val_term: Term) -> Term:
        return App("some", val_term)

    def eq(a: Term, b: Term) -> Term:
        return App("eq", a, b)

    return Theory(
        name=name,
        version=version,
        sort_arities={"Map": 2, "Option": 1},
        sort_signatures={
            "empty": SortSignature((), TypeConst("Map", (k, v))),
            "put": SortSignature(
                (TypeConst("Map", (k, v)), k, v),
                TypeConst("Map", (k, v)),
            ),
            "get": SortSignature(
                (TypeConst("Map", (k, v)), k),
                TypeConst("Option", (v,)),
            ),
            "none": SortSignature((), TypeConst("Option", (v,))),
            "some": SortSignature((v,), TypeConst("Option", (v,))),
        },
        rules=(
            Rule(get(empty, key), none),
            Rule(get(put(m, key, val), key), some(val)),
            Rule(
                get(put(m, j, val), key), App("if", eq(j, key), some(val), get(m, key))
            ),
        ),
        precedence={"put": 2, "get": 2},
    )


def tree_theory(name: str = "core.tree", version: str = "1.0.0") -> Theory:
    """Return a binary-tree theory with leaf/node constructors."""

    a = TypeVar("A")
    left = V("tree_l", "Tree")
    val = V("tree_v")
    right = V("tree_r", "Tree")

    return Theory(
        name=name,
        version=version,
        depends_on=("core.nat",),
        sort_arities={"Tree": 1},
        sort_signatures={
            "leaf": SortSignature((), TypeConst("Tree", (a,))),
            "node": SortSignature(
                (TypeConst("Tree", (a,)), a, TypeConst("Tree", (a,))),
                TypeConst("Tree", (a,)),
            ),
        },
        rules=(),
        schemes=(tree_induction_scheme(),),
        precedence={"leaf": 1, "node": 1},
    )


def theory_from_module(module: ModuleType) -> Theory:
    """Load ``THEORY`` from a Python module object."""

    theory = getattr(module, "THEORY", None)
    if not isinstance(theory, Theory):
        raise ValueError("Theory module must export THEORY: Theory.")
    return theory


def load_theory_module(module_name: str) -> Theory:
    """Import a module by name and return its exported ``THEORY`` value."""

    return theory_from_module(importlib.import_module(module_name))


def get_theorem_environment(engine: Engine) -> "TheoremEnvironment":
    """Get or create the theorem environment attached to an engine."""

    if engine.theory is None:
        engine.theory = TheoremEnvironment(engine, engine.rules)
    return engine.theory


def register_recursive_definition(
    engine: Engine,
    name: str,
    equations: Tuple[Tuple[Term, Term], ...],
    scope: str = "definitions",
    signature: Optional[SortSignature] = None,
    precedence: Optional[int] = None,
) -> Tuple[Rule, ...]:
    """Register recursive definition equations as scoped rewrite rules."""

    return get_theorem_environment(engine).register_recursive_definition(
        name,
        equations,
        scope=scope,
        signature=signature,
        precedence=precedence,
    )


def _parse_version(version: str) -> Tuple[int, ...]:
    parts = version.split(".")
    if any((not part) or (not part.isdigit()) for part in parts):
        raise ValueError(f"Invalid version string: {version!r}")
    return tuple(int(part) for part in parts)


def _version_at_least(current: str, minimum: str) -> bool:
    current_parts = _parse_version(current)
    minimum_parts = _parse_version(minimum)
    size = max(len(current_parts), len(minimum_parts))
    current_parts = current_parts + (0,) * (size - len(current_parts))
    minimum_parts = minimum_parts + (0,) * (size - len(minimum_parts))
    return current_parts >= minimum_parts


def _parse_dependency_spec(spec: str) -> Tuple[str, Optional[str]]:
    spec = spec.strip()
    if not spec:
        raise ValueError("Empty theory dependency spec.")
    if ">=" in spec:
        name, minimum = spec.split(">=", 1)
        name = name.strip()
        minimum = minimum.strip()
        if not name or not minimum:
            raise ValueError(f"Invalid dependency spec: {spec!r}")
        return name, minimum
    return spec, None


def _check_theory_install_conflicts(
    engine: Engine,
    env: "TheoremEnvironment",
    theory: Theory,
    install_scope: str,
) -> None:
    installed_version = engine.installed_theories.get(theory.name)
    if installed_version is not None:
        if installed_version != theory.version:
            raise ValueError(
                f"Theory {theory.name} already installed at version {installed_version}; "
                f"cannot install incompatible version {theory.version}."
            )
        raise ValueError(f"Theory {theory.name}@{theory.version} is already installed.")

    for dep_spec in theory.depends_on:
        dep_name, dep_minimum = _parse_dependency_spec(dep_spec)
        current = engine.installed_theories.get(dep_name)
        if current is None:
            raise ValueError(f"Missing theory dependency: {dep_name}")
        if dep_minimum is not None and not _version_at_least(current, dep_minimum):
            raise ValueError(
                f"Theory dependency {dep_name}>={dep_minimum} not satisfied by installed "
                f"version {current}."
            )

    for symbol, signature in theory.sort_signatures.items():
        existing_signature = engine.get_sort_signature(symbol)
        if existing_signature is not None and existing_signature != signature:
            raise ValueError(
                f"Theory {theory.name} conflicts on symbol {symbol}: existing signature "
                f"{existing_signature} vs {signature}."
            )

    for sort_name, arity in theory.sort_arities.items():
        existing_arity = engine.sort_arities.get(sort_name)
        if existing_arity is not None and existing_arity != arity:
            raise ValueError(
                f"Theory {theory.name} conflicts on sort constructor {sort_name}: existing "
                f"arity {existing_arity} vs {arity}."
            )

    for symbol, rank in theory.precedence.items():
        existing_rank = engine.config.precedence.get(symbol)
        if existing_rank is not None and existing_rank != rank:
            raise ValueError(
                f"Theory {theory.name} conflicts on precedence for {symbol}: existing "
                f"{existing_rank} vs {rank}."
            )

    for symbol in theory.assoc:
        if symbol in engine.config.comm and symbol not in engine.config.assoc:
            raise ValueError(
                f"Theory {theory.name} requests associativity for {symbol} but engine marks "
                "it non-associative."
            )

    for symbol in theory.comm:
        if symbol in engine.config.comm and symbol not in engine.config.assoc:
            raise ValueError(
                f"Theory {theory.name} requests commutativity for non-associative symbol "
                f"{symbol}."
            )

    for lemma in theory.lemmas:
        existing_lemma = env.lemmas.get(lemma.name)
        if existing_lemma is not None and existing_lemma != lemma:
            raise ValueError(
                f"Theory {theory.name} conflicts on lemma name: {lemma.name}."
            )

    for definition_name, definition in theory.definitions.items():
        existing_definition = env.definitions.get(definition_name)
        if existing_definition is not None and existing_definition != definition:
            raise ValueError(
                f"Theory {theory.name} conflicts on definition name: {definition_name}."
            )

    for scope in theory.default_scopes:
        if scope == install_scope:
            continue
        existing_scope_rules = env.scoped_rule_sets.get(scope)
        if existing_scope_rules:
            raise ValueError(
                f"Theory {theory.name} default scope {scope!r} already exists with rules; "
                "scope collision is not allowed."
            )


def _clone_theorem_environment(
    engine: Engine,
    source: Optional["TheoremEnvironment"],
) -> Optional["TheoremEnvironment"]:
    if source is None:
        return None
    cloned = TheoremEnvironment(engine, list(source.base_rules))
    cloned.lemmas = dict(source.lemmas)
    cloned.definitions = dict(source.definitions)
    cloned.recursive_definitions = dict(source.recursive_definitions)
    cloned.lemma_rewrites = dict(source.lemma_rewrites)
    cloned.named_rules = dict(source.named_rules)
    cloned.lemma_rule_classes = dict(source.lemma_rule_classes)
    cloned.scoped_rule_sets = {
        scope: list(rules) for scope, rules in source.scoped_rule_sets.items()
    }
    cloned.active_scopes = set(source.active_scopes)
    return cloned


def _clone_engine_for_theory_preflight(engine: Engine) -> Engine:
    cloned_config = EngineConfig(
        precedence=dict(engine.config.precedence),
        assoc=set(engine.config.assoc),
        comm=set(engine.config.comm),
    )
    cloned = make_engine(
        rules=list(engine.rules),
        ctx=engine.ctx,
        fuel=engine.fuel,
        config=cloned_config,
        ground_cache={},
        schemes=dict(engine.schemes),
        sort_signatures=dict(engine.sort_signatures),
        sort_arities=dict(engine.sort_arities),
        installed_theories=dict(engine.installed_theories),
    )
    cloned.theory = _clone_theorem_environment(cloned, engine.theory)
    return cloned


def _install_theory_impl(
    engine: Engine, theory: Theory, activate_scopes: bool
) -> Tuple[str, ...]:
    env = get_theorem_environment(engine)
    install_scope = f"theory:{theory.name}"
    _check_theory_install_conflicts(engine, env, theory, install_scope)

    seen: set[str] = set()
    activated_list: list[str] = []
    for scope in (install_scope, *theory.default_scopes):
        env.create_scope(scope)
        if scope not in seen:
            seen.add(scope)
            activated_list.append(scope)
    activated = tuple(activated_list)

    engine.sort_arities.update(theory.sort_arities)

    for symbol in sorted(theory.sort_signatures):
        register_sort_signature(engine, symbol, theory.sort_signatures[symbol])

    engine.config.precedence.update(theory.precedence)
    engine.config.assoc.update(theory.assoc)
    engine.config.comm.update(theory.comm)

    for scheme in sorted(theory.schemes, key=lambda item: item.name):
        register_induction_scheme(engine, scheme)

    for name in sorted(theory.definitions):
        definition = theory.definitions[name]
        env.register_definition(
            name, definition.lhs, definition.rhs, scope=install_scope
        )

    for index, rule in enumerate(theory.rules):
        rule_name = f"theory.{theory.name}.{index}"
        env.register_rule(rule, scope=install_scope, label=rule_name, name=rule_name)

    for lemma in sorted(theory.lemmas, key=lambda item: item.name):
        env.register_lemma(lemma)
    if activate_scopes:
        for scope in activated:
            env.activate_scope(scope)
    engine.installed_theories[theory.name] = theory.version
    return activated


def install_theory(
    engine: Engine, theory: Theory, activate_scopes: bool = True
) -> Tuple[str, ...]:
    """Install a theory with conflict preflight, then mutate the real engine."""

    preflight = _clone_engine_for_theory_preflight(engine)
    _install_theory_impl(preflight, theory, activate_scopes=activate_scopes)
    return _install_theory_impl(engine, theory, activate_scopes=activate_scopes)


def _contains_symbol(term: Term, symbol: str) -> bool:
    match term:
        case Var():
            return False
        case Fun(sym, _):
            if sym == symbol:
                return True
            return any(_contains_symbol(arg, symbol) for arg in term.args)
    raise TypeError(f"Unsupported term type: {type(term)!r}")


def _select_induction_scheme(
    engine: Engine,
    var: Var,
    scheme: Optional[InductionScheme] = None,
    scheme_name: Optional[str] = None,
) -> InductionScheme:
    chosen = scheme
    if chosen is None and scheme_name is not None:
        chosen = get_induction_scheme(engine, scheme_name)
    if chosen is None and var.sort is not None:
        chosen = get_induction_scheme_for_sort(engine, var.sort)
    if chosen is None:
        raise ValueError(
            "No induction scheme provided and no scheme found for variable sort."
        )
    if not var_matches_scheme(var, chosen):
        raise ValueError(
            f"Variable {var.name} is incompatible with induction scheme {chosen.name}."
        )
    return chosen


def _orient_equality_as_rewrite(
    config: EngineConfig,
    lhs: Term,
    rhs: Term,
    orientation: str,
) -> Rule:
    if orientation == "auto":
        if _decreases(config, lhs, rhs):
            return Rule(lhs, rhs)
        if _decreases(config, rhs, lhs):
            return Rule(rhs, lhs)
        raise ValueError("Lemma cannot be oriented into a decreasing rewrite rule.")
    if orientation == "lhs_to_rhs":
        if not _decreases(config, lhs, rhs):
            raise ValueError("Requested orientation lhs_to_rhs is not decreasing.")
        return Rule(lhs, rhs)
    if orientation == "rhs_to_lhs":
        if not _decreases(config, rhs, lhs):
            raise ValueError("Requested orientation rhs_to_lhs is not decreasing.")
        return Rule(rhs, lhs)
    raise ValueError(f"Unknown orientation: {orientation}")


class TheoremEnvironment:
    """Manages scoped rules, definitions, and lemmas for one engine."""

    def __init__(self, engine: Engine, base_rules: list[Rule]):
        self.engine = engine
        self.base_rules: list[Rule] = list(base_rules)
        self.lemmas: Dict[str, Lemma] = {}
        self.lemma_rule_classes: Dict[str, Tuple[RuleClassSpec, ...]] = {}
        self.definitions: Dict[str, Rule] = {}
        self.recursive_definitions: Dict[str, Tuple[Rule, ...]] = {}
        self.lemma_rewrites: Dict[str, Rule] = {}
        self.named_rules: Dict[str, NamedRuleInfo] = {}
        self.scoped_rule_sets: Dict[str, list[str]] = {}
        self.active_scopes: set[str] = set()

    def _sanitize_rule_name(self, text: str) -> str:
        pieces: list[str] = []
        for char in text.strip():
            if char.isalnum() or char in "._-":
                pieces.append(char)
            else:
                pieces.append("-")
        cleaned = "".join(pieces).strip("._-")
        return cleaned or "rule"

    def _rule_head_symbol(self, rule: Rule) -> str:
        match rule.lhs:
            case Fun(symbol, _):
                return symbol
            case _:
                return "rule"

    def _auto_rule_name(self, rule: Rule, scope: str, label: str) -> str:
        base = self._sanitize_rule_name(label)
        if base == "theory-rule" or base == "rule":
            base = self._sanitize_rule_name(self._rule_head_symbol(rule))
        candidate = f"{self._sanitize_rule_name(scope)}.{base}"
        suffix = 1
        while candidate in self.named_rules:
            suffix += 1
            candidate = f"{self._sanitize_rule_name(scope)}.{base}.{suffix}"
        return candidate

    def _sync_engine_rules(self) -> None:
        # Rebuild active rules from base + active scopes to keep engine/index coherent.
        active_rules = list(self.base_rules)
        for scope, rule_names in self.scoped_rule_sets.items():
            if scope not in self.active_scopes:
                continue
            for rule_name in rule_names:
                entry = self.named_rules.get(rule_name)
                if entry is None:
                    continue
                if has_rule_class(entry.rule_classes, RuleClass.REWRITE):
                    active_rules.append(entry.rule)
        self.engine.reset_rules(active_rules)

    def _add_rule_to_scope(self, scope: str, rule_name: str) -> None:
        self.scoped_rule_sets.setdefault(scope, []).append(rule_name)
        if scope in self.active_scopes:
            self._sync_engine_rules()

    def create_scope(self, name: str) -> None:
        """Create an empty named scope if needed."""

        self.scoped_rule_sets.setdefault(name, [])

    def activate_scope(self, name: str) -> None:
        """Activate a scope and resynchronize engine rules."""

        if name not in self.scoped_rule_sets:
            raise ValueError(f"Unknown scope: {name}")
        self.active_scopes.add(name)
        self._sync_engine_rules()

    def deactivate_scope(self, name: str) -> None:
        """Deactivate a scope and resynchronize engine rules."""

        self.active_scopes.discard(name)
        self._sync_engine_rules()

    def is_theory_rule(self, rule: Rule) -> bool:
        """Check if a rule originates from the theory (not arbitrary)."""
        for entry in self.named_rules.values():
            if entry.rule is rule:
                return True
        return False

    def get_named_rule(self, name: str) -> Optional[Rule]:
        """Look up a named rule by name."""
        entry = self.named_rules.get(name)
        if entry is None:
            return None
        return entry.rule

    def get_named_rule_entry(self, name: str) -> Optional[NamedRuleInfo]:
        """Look up a named rule by name with full metadata."""

        return self.named_rules.get(name)

    def get_named_rule_info(self, name: str) -> Optional[Tuple[Rule, RuleSource]]:
        """Look up a named rule by name with its source."""
        entry = self.named_rules.get(name)
        if entry is None:
            return None
        return entry.rule, entry.source

    def get_named_rule_classes(self, name: str) -> Tuple[RuleClassSpec, ...]:
        """Return registered rule classes for a named rule."""

        entry = self.named_rules.get(name)
        if entry is None:
            return ()
        return entry.rule_classes

    def get_lemma_rule_classes(self, name: str) -> Tuple[RuleClassSpec, ...]:
        """Return registered rule classes for a lemma."""

        return self.lemma_rule_classes.get(name, ())

    def list_named_rule_entries(
        self,
        pattern: Optional[str] = None,
        rule_class: Optional[RuleClass] = None,
    ) -> Dict[str, NamedRuleInfo]:
        """List named rules with full metadata, optionally filtered."""

        out: Dict[str, NamedRuleInfo] = {}
        for name, entry in self.named_rules.items():
            if pattern is not None and not fnmatch(name, pattern):
                continue
            if rule_class is not None and not has_rule_class(
                entry.rule_classes, rule_class
            ):
                continue
            out[name] = entry
        return out

    def list_named_rules(
        self,
        pattern: Optional[str] = None,
        rule_class: Optional[RuleClass] = None,
    ) -> Dict[str, Tuple[Rule, RuleSource]]:
        """List all named rules, optionally filtered by pattern."""
        return {
            name: (entry.rule, entry.source)
            for name, entry in self.list_named_rule_entries(
                pattern=pattern, rule_class=rule_class
            ).items()
        }

    def register_lemma(
        self,
        lemma: Lemma,
        depth: int = 12,
        induction_depth: int = 2,
        rule_classes: Optional[Tuple[RuleClassInput, ...]] = None,
    ) -> None:
        """Validate and store a proved lemma."""

        if lemma.clause.assumptions:
            raise ValueError(
                "Only assumption-free lemmas can be registered in this minimal environment."
            )
        if lemma.clause.disequalities:
            raise ValueError(
                "Only disequality-free lemmas can be registered in this minimal environment."
            )
        if goal_equality(lemma.clause.goal) is None:
            raise ValueError("Lemma goal must be an equality.")
        _validate_clause_sorts(lemma.clause, self.engine, f"lemma {lemma.name}")
        if lemma.certificate.clause != lemma.clause:
            raise ValueError("Lemma certificate root does not match lemma clause.")
        if not check_certificate(
            lemma.certificate,
            self.engine,
            depth=depth,
            induction_depth=induction_depth,
        ):
            raise ValueError("Lemma certificate failed validation.")
        self.lemmas[lemma.name] = lemma
        self.lemma_rule_classes[lemma.name] = normalize_rule_classes(rule_classes)

    def register_rule(
        self,
        rule: Rule,
        scope: str = "theories",
        label: str = "theory rule",
        name: Optional[str] = None,
        rule_classes: Optional[Tuple[RuleClassInput, ...]] = None,
    ) -> str:
        """Validate and register a rule into a scope."""

        _validate_rule_sorts(rule, self.engine, label)
        final_name = name or self._auto_rule_name(rule, scope, label)
        self.named_rules[final_name] = NamedRuleInfo(
            rule=rule,
            source=RuleSource.THEORY,
            rule_classes=normalize_rule_classes(
                rule_classes, default=(rewrite_rule_class(),)
            ),
        )
        self._add_rule_to_scope(scope, final_name)
        return final_name

    def register_definition(
        self,
        name: str,
        lhs: Term,
        rhs: Term,
        scope: str = "definitions",
        rule_classes: Optional[Tuple[RuleClassInput, ...]] = None,
    ) -> None:
        """Register a non-recursive definition as a scoped rewrite rule."""

        match lhs:
            case Fun(symbol, _):
                pass
            case _:
                raise ValueError("Definition lhs must be a function application.")
        if _contains_symbol(rhs, symbol):
            raise ValueError(
                "Recursive definitions are not supported in this prover core."
            )
        if symbol not in self.engine.config.precedence:
            base = max(self.engine.config.precedence.values(), default=0)
            self.engine.config.precedence[symbol] = base + 1
        rule = Rule(lhs, rhs)
        _validate_rule_sorts(rule, self.engine, f"definition {name}")
        self.definitions[name] = rule
        rule_name = f"def-{name}"
        self.named_rules[rule_name] = NamedRuleInfo(
            rule=rule,
            source=RuleSource.DEFINITION,
            rule_classes=normalize_rule_classes(
                rule_classes, default=(rewrite_rule_class(),)
            ),
        )
        self._add_rule_to_scope(scope, rule_name)

    def register_recursive_definition(
        self,
        name: str,
        equations: Tuple[Tuple[Term, Term], ...],
        scope: str = "definitions",
        signature: Optional[SortSignature] = None,
        precedence: Optional[int] = None,
        rule_classes: Optional[Tuple[RuleClassInput, ...]] = None,
    ) -> Tuple[Rule, ...]:
        """Register recursive definition equations as scoped rewrite rules."""

        if not equations:
            raise ValueError("Recursive definitions require at least one equation.")
        if name in self.definitions:
            raise ValueError(
                f"Definition name already used by non-recursive definition: {name}"
            )

        if signature is not None:
            register_sort_signature(self.engine, name, signature)
        if precedence is not None:
            existing_rank = self.engine.config.precedence.get(name)
            if existing_rank is not None and existing_rank != precedence:
                raise ValueError(
                    f"Precedence conflict for {name}: existing {existing_rank} vs "
                    f"requested {precedence}."
                )
            self.engine.config.precedence[name] = precedence
        elif name not in self.engine.config.precedence:
            base = max(self.engine.config.precedence.values(), default=0)
            self.engine.config.precedence[name] = base + 1

        rules: list[Rule] = []
        for lhs, rhs in equations:
            match lhs:
                case Fun(symbol, _):
                    if symbol != name:
                        raise ValueError(
                            f"Recursive definition lhs uses {symbol}, expected {name}."
                        )
                case _:
                    raise ValueError(
                        "Recursive definition lhs must be a function application."
                    )
            rule = Rule(lhs, rhs)
            _validate_rule_sorts(rule, self.engine, f"recursive definition {name}")
            if not _decreases(self.engine.config, lhs, rhs):
                raise ValueError(
                    f"Recursive definition equation is not decreasing: {lhs} -> {rhs}"
                )
            rules.append(rule)

        existing = self.recursive_definitions.get(name)
        registered = tuple(rules)
        if existing is not None:
            if existing != registered:
                raise ValueError(f"Conflicting recursive definition for name: {name}")
            return existing

        self.recursive_definitions[name] = registered
        classes = normalize_rule_classes(rule_classes, default=(rewrite_rule_class(),))
        for index, rule in enumerate(registered):
            rule_name = f"def-{name}.{index}"
            self.named_rules[rule_name] = NamedRuleInfo(
                rule=rule,
                source=RuleSource.DEFINITION,
                rule_classes=classes,
            )
            self._add_rule_to_scope(scope, rule_name)
        return registered

    def register_lemma_rewrite(
        self,
        lemma_name: str,
        scope: str = "lemmas",
        orientation: str = "auto",
        rule_classes: Optional[Tuple[RuleClassInput, ...]] = None,
    ) -> Rule:
        """Orient and register a lemma equality as a rewrite rule."""

        lemma = self.lemmas.get(lemma_name)
        if lemma is None:
            raise ValueError(f"Unknown lemma: {lemma_name}")
        eq_goal = goal_equality(lemma.clause.goal)
        if eq_goal is None:
            raise ValueError("Lemma goal must be an equality.")
        lhs, rhs = eq_goal
        rule = _orient_equality_as_rewrite(self.engine.config, lhs, rhs, orientation)
        _validate_rule_sorts(rule, self.engine, f"lemma rewrite {lemma_name}")
        self.lemma_rewrites[lemma_name] = rule
        rule_name = f"lemma-{lemma_name}"
        self.named_rules[rule_name] = NamedRuleInfo(
            rule=rule,
            source=RuleSource.LEMMA,
            rule_classes=normalize_rule_classes(
                rule_classes, default=(rewrite_rule_class(),)
            ),
        )
        self._add_rule_to_scope(scope, rule_name)
        return rule
