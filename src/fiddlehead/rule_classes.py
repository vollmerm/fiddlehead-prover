from __future__ import annotations

"""Rule-class metadata for theorem-environment registrations."""

from dataclasses import dataclass
from enum import Enum, auto
from typing import Iterable, Optional, TypeAlias


class RuleClass(Enum):
    """High-level role assigned to a theorem-environment rule."""

    REWRITE = auto()
    FORWARD_CHAINING = auto()


@dataclass(frozen=True)
class RuleClassSpec:
    """Concrete rule-class annotation stored on a registration."""

    kind: RuleClass

    def __str__(self) -> str:
        return self.kind.name.lower().replace("_", "-")


RuleClassInput: TypeAlias = RuleClass | RuleClassSpec


def rewrite_rule_class() -> RuleClassSpec:
    return RuleClassSpec(RuleClass.REWRITE)


def forward_chaining_rule_class() -> RuleClassSpec:
    return RuleClassSpec(RuleClass.FORWARD_CHAINING)


def has_rule_class(
    rule_classes: Iterable[RuleClassSpec], rule_class: RuleClass
) -> bool:
    return any(spec.kind == rule_class for spec in rule_classes)


def normalize_rule_classes(
    rule_classes: Optional[Iterable[RuleClassInput]],
    default: Optional[Iterable[RuleClassInput]] = None,
) -> tuple[RuleClassSpec, ...]:
    """Normalize class inputs to a deduplicated tuple of specs."""

    items = default if rule_classes is None else rule_classes
    if items is None:
        return ()
    out: list[RuleClassSpec] = []
    seen: set[RuleClass] = set()
    for item in items:
        spec = item if isinstance(item, RuleClassSpec) else RuleClassSpec(item)
        if spec.kind in seen:
            continue
        seen.add(spec.kind)
        out.append(spec)
    return tuple(out)
