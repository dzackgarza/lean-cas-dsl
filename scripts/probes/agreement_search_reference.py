"""Fair search over finite, source-authorized comparison derivation syntax.

This module implements enumeration and bounded-check scheduling, not mathematics
or a Lean proof checker. The fixed source environment supplies the permissible
syntax constructors and the trusted checker for ONE complete, rigid goal. A leaf
is never that checker and supplies none of this input. The caller must retain the
actual source environment/goal, not just their displayed names or hashes.

Candidate rejection means only that this candidate is not a permitted proof.
Finite search exhaustion is always Pending, never no-reading or disagreement.
A trusted checker must return within its reserved budget; resource exhaustion
must return Deferred, and an internal exception is propagated rather than used
as evidence. A production implementation uses the existing global resource
meter and synchronous Lean kernel checking. These are scheduler reference tests,
not proof that the production checker or original mathematical workload passes.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Generic, TypeVar

Context = TypeVar("Context")
Goal = TypeVar("Goal")
Proof = TypeVar("Proof")


@dataclass(frozen=True)
class Symbol:
    """An engineering syntax constructor; its ID refers to the frozen source."""
    source_id: str
    arity: int

    def __post_init__(self) -> None:
        if not self.source_id or self.arity < 0:
            raise ValueError("a symbol needs a source identity and nonnegative arity")


@dataclass(frozen=True)
class Term:
    symbol: int
    arguments: tuple[Term, ...] = ()


def code_at(index: int, alphabet_size: int) -> tuple[int, ...]:
    """Unrank all finite words in length-then-lexicographic order, including ()."""
    if index < 0 or alphabet_size <= 0:
        raise ValueError("invalid index or empty alphabet")
    length, block = 0, 1
    while index >= block:
        index -= block
        length += 1
        block *= alphabet_size
    digits = [0] * length
    for position in range(length - 1, -1, -1):
        index, digits[position] = divmod(index, alphabet_size)
    return tuple(digits)


def decode(code: tuple[int, ...], alphabet: tuple[Symbol, ...]) -> Term | None:
    """Decode prefix-arity syntax without recursion or implicit symbol lookup."""
    if not code:
        return None
    frames: list[tuple[int, list[Term]]] = []
    root: Term | None = None
    for token in code:
        if root is not None or token < 0 or token >= len(alphabet):
            return None
        frames.append((token, []))
        while frames and len(frames[-1][1]) == alphabet[frames[-1][0]].arity:
            symbol, arguments = frames.pop()
            term = Term(symbol, tuple(arguments))
            if frames:
                frames[-1][1].append(term)
            else:
                root = term
    return root if not frames else None


@dataclass(frozen=True)
class Accepted(Generic[Proof]):
    """Only the trusted, source-bound checker may issue this response."""
    proof: Proof


@dataclass(frozen=True)
class Rejected:
    """A definite rejection of this finite proof candidate, not of the goal."""
    reason: str


@dataclass(frozen=True)
class Deferred:
    """No verdict on this candidate within its allocated checking budget."""
    reason: str = "checking resource exhausted"


@dataclass(frozen=True)
class Found(Generic[Context, Goal, Proof]):
    context: Context
    goal: Goal
    code: tuple[int, ...]
    term: Term
    proof: Proof


@dataclass(frozen=True)
class Pending:
    pairs_visited: int
    checker_calls: int
    reserved_budget: int


@dataclass(frozen=True)
class _Problem(Generic[Context, Goal]):
    context: Context
    goal: Goal
    alphabet: tuple[Symbol, ...]


class AgreementSearch(Generic[Context, Goal, Proof]):
    """Dovetail candidate index i and checking effort k along i+k diagonals.

    In the unbounded schedule, every (i,k) pair occurs once and receives budget
    k+1. Therefore any permitted finite proof accepted at finite effort is found.
    `advance` is explicitly resource-bounded and returns Pending on interruption.
    It reserves requested budget before each call; it never increases the caller's
    allocation or interprets Pending/Deferred/Rejected as semantic disagreement.

    The checker receives the unchanged context, complete goal and whole term.
    Alphabet indices are meaningful only under this frozen source alphabet.
    """
    __slots__ = ("_problem", "_checker", "diagonal", "position", "terms", "rejected", "found")

    @property
    def context(self) -> Context:
        return self._problem.context

    @property
    def goal(self) -> Goal:
        return self._problem.goal

    @property
    def alphabet(self) -> tuple[Symbol, ...]:
        return self._problem.alphabet

    def __init__(
        self,
        context: Context,
        goal: Goal,
        alphabet: tuple[Symbol, ...],
        checker: Callable[[Context, Goal, tuple[Symbol, ...], Term, int],
                          Accepted[Proof] | Rejected | Deferred],
    ) -> None:
        if not alphabet or len({s.source_id for s in alphabet}) != len(alphabet):
            raise ValueError("the frozen alphabet must be nonempty with unique identities")
        self._problem = _Problem(context, goal, tuple(alphabet))
        self._checker = checker
        self.diagonal = 0
        self.position = 0
        self.terms: dict[int, Term | None] = {}
        self.rejected: dict[int, str] = {}
        self.found: Found[Context, Goal, Proof] | None = None

    def _next_pair(self) -> None:
        self.position += 1
        if self.position > self.diagonal:
            self.diagonal += 1
            self.position = 0

    def advance(self, *, max_pairs: int, budget: int) -> Found[Context, Goal, Proof] | Pending:
        """Advance under explicit limits. An internal checker failure propagates.

        A pair needing more budget is left pending at that exact pair; it is not
        silently skipped or treated as rejected. Calling with further resources
        is an explicit caller action, not an automatic retry of a CAS operation.
        """
        if max_pairs < 0 or budget < 0:
            raise ValueError("limits must be nonnegative")
        if self.found is not None:
            return self.found
        visited = calls = reserved = 0
        while visited < max_pairs:
            i = self.position
            effort = self.diagonal - i + 1
            if i not in self.terms:
                self.terms[i] = decode(code_at(i, len(self.alphabet)), self.alphabet)
            term = self.terms[i]
            if term is None or i in self.rejected:
                self._next_pair()
                visited += 1
                continue
            if effort > budget - reserved:
                break
            # Reservation is conservative: an entire quantum is charged even if
            # the checker finishes early. Production uses its actual global meter.
            reserved += effort
            calls += 1
            result = self._checker(self.context, self.goal, self.alphabet, term, effort)
            if isinstance(result, Accepted):
                self.found = Found(self.context, self.goal, code_at(i, len(self.alphabet)),
                                   term, result.proof)
                return self.found
            if isinstance(result, Rejected):
                self.rejected[i] = result.reason
            elif not isinstance(result, Deferred):
                raise TypeError("the trusted checker returned an invalid checking outcome")
            self._next_pair()
            visited += 1
        return Pending(visited, calls, reserved)
