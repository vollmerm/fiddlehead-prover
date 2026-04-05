from __future__ import annotations

"""Tracing data structures for rewriting steps and proof trees."""

from dataclasses import dataclass
from typing import Protocol

from .syntax import Term


@dataclass
class TraceStep:
    """A single rewrite transition."""

    before: Term
    after: Term
    rule: object


class Trace:
    """Append-only collection of rewrite transitions."""

    def __init__(self) -> None:
        self.steps: list[TraceStep] = []

    def add(self, before: Term, after: Term, rule: object) -> None:
        self.steps.append(TraceStep(before, after, rule))


class ClauseLike(Protocol):
    goal: Term


@dataclass
class ProofNode:
    """Node in a high-level proof trace tree."""

    kind: str
    clause: ClauseLike
    note: str = ""
    children: list["ProofNode"] | None = None
    solved: bool | None = None

    def __post_init__(self) -> None:
        if self.children is None:
            self.children = []


@dataclass
class ProofTrace:
    """Container for one or more proof roots."""

    roots: list[ProofNode]

    def __init__(self) -> None:
        self.roots = []


def _new_node(kind: str, clause: ClauseLike, note: str = "") -> ProofNode:
    return ProofNode(kind=kind, clause=clause, note=note, children=[])


def render_proof_trace(trace: ProofTrace) -> str:
    """Render a readable tree view of a ``ProofTrace``."""

    lines: list[str] = []

    def visit(node: ProofNode, indent: int) -> None:
        pad = "  " * indent
        status = ""
        if node.solved is True:
            status = " [solved]"
        elif node.solved is False:
            status = " [failed]"
        note = f" :: {node.note}" if node.note else ""
        lines.append(f"{pad}- {node.kind}{status}{note} -> {node.clause.goal}")
        for child in node.children or []:
            visit(child, indent + 1)

    for root in trace.roots:
        visit(root, 0)
    return "\n".join(lines)
