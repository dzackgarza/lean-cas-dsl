"""Check complete finite induction covers of an exact source reading grammar.

This is kernel-internal reference code, not a leaf proof interface or a Lean
checker. The fixed problem supplies the exact grammar, source statements and
root judgment BEFORE any candidate is considered. Candidates supply terms only;
they cannot choose the meaning, premises, grammar or requested conclusion.

A successful cover includes every root-reachable production, including cyclic
alternatives, and a checked root implication. Induction on a finite derivation
then establishes the fixed root judgment for every represented route. Checking
an arbitrary finite subset or a pairwise equality cannot create a cover.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Generic, Hashable, TypeVar

from structural_routes_reference import PrefixRule, TraceGrammar, Word, compile_routes

Statement = TypeVar("Statement")
Source = TypeVar("Source")
Evidence = TypeVar("Evidence")
Proof = TypeVar("Proof")
Node = Hashable


@dataclass(frozen=True)
class Rule:
    """One exact production; action retains source occurrences and direction."""
    identity: Hashable
    parent: Node
    children: tuple[Node, ...]
    action: Hashable


@dataclass(frozen=True)
class RuleGoal(Generic[Statement]):
    rule: Rule
    premises: tuple[Statement, ...]
    conclusion: Statement


@dataclass(frozen=True)
class RootGoal(Generic[Statement]):
    premise: Statement
    conclusion: Statement


@dataclass(frozen=True)
class Checked(Generic[Proof]):
    """A term accepted at the exact requested goal by the internal checker."""
    proof: Proof


@dataclass(frozen=True)
class Invalid:
    """This cover/candidate is invalid; the mathematical query is not refuted."""
    reason: str


@dataclass(frozen=True)
class Pending:
    """No coverage judgment; includes incomplete evidence or resource limits."""
    reason: str


@dataclass(frozen=True)
class Candidate(Generic[Evidence]):
    # Only proof terms: no candidate-supplied source, goal or invariant fields.
    rules: tuple[tuple[Hashable, Evidence], ...]
    root: Evidence


@dataclass(frozen=True)
class FixedProblem(Generic[Source, Statement]):
    """Prepared privately from the accepted source and exact reading grammar.

    Source/Statement objects must themselves be immutable (native production
    uses the persistent Lean environment, closed expressions and rigid context).
    Arbitrary caller-selected predicates are not an interpretation authority.
    """
    source: Source
    start: Node
    rules: tuple[Rule, ...]
    statements: tuple[tuple[Node, Statement], ...]
    goal: Statement
    route_binding: tuple[tuple[PrefixRule, ...], Word, frozenset[Word]] | None = None

    def __post_init__(self) -> None:
        ids = [r.identity for r in self.rules]
        nodes = [n for n, _ in self.statements]
        if len(ids) != len(set(ids)) or len(nodes) != len(set(nodes)):
            raise ValueError("duplicate production identity or statement owner")
        known = set(nodes)
        if self.start not in known:
            raise ValueError("start has no fixed statement")
        if any(r.parent not in known or any(c not in known for c in r.children)
               for r in self.rules):
            raise ValueError("production mentions an undeclared nonterminal")

    def obligations(self) -> tuple[RuleGoal[Statement], ...]:
        # Reachability is syntactic and exhaustive; no candidate or checker
        # participates in deciding which production alternatives are retained.
        reachable = {self.start}
        changed = True
        while changed:
            changed = False
            for rule in self.rules:
                if rule.parent in reachable:
                    old = len(reachable)
                    reachable.update(rule.children)
                    changed |= len(reachable) != old
        statements = dict(self.statements)
        return tuple(RuleGoal(rule, tuple(statements[c] for c in rule.children),
                              statements[rule.parent])
                     for rule in self.rules if rule.parent in reachable)


def from_trace_grammar(
    source: Source,
    grammar: TraceGrammar,
    statements: tuple[tuple[Node, Statement], ...],
    goal: Statement,
) -> FixedProblem[Source, Statement]:
    """Snapshot the complete compiler-produced grammar, never a candidate view.

    Each production identity contains its parent and the complete production,
    not just the emitted edge label. The snapshot retains recursive alternatives
    and is unaffected by later mutation of the reference grammar's dictionary.
    Source statements must name every and only the actual grammar nonterminals.
    """
    nodes = [node for node, _ in statements]
    if len(nodes) != len(set(nodes)) or set(nodes) != set(grammar.productions):
        raise ValueError("statement owners differ from the exact grammar")
    rules = tuple(Rule((parent, production), parent, production.children,
                       production.emit)
                  for parent, productions in grammar.productions.items()
                  for production in productions)
    return FixedProblem(source, grammar.start, rules, statements, goal)


@dataclass(frozen=True)
class CompleteCover(Generic[Source, Statement, Proof]):
    problem: FixedProblem[Source, Statement]
    obligations: tuple[RuleGoal[Statement], ...]
    rule_proofs: tuple[Proof, ...]
    root_goal: RootGoal[Statement]
    root_proof: Proof


def check_cover(
    problem: FixedProblem[Source, Statement],
    candidate: Candidate[Evidence],
    check: Callable[[Source, RuleGoal[Statement] | RootGoal[Statement], Evidence, int],
                    Checked[Proof] | Invalid | Pending],
    *,
    budget: int,
    quantum: int = 1,
    efforts: tuple[int, ...] | None = None,
) -> CompleteCover[Source, Statement, Proof] | Invalid | Pending:
    """Verify every exact local implication and the requested root judgment.

    This reference conservatively reserves a quantum per checker invocation.
    The checker must meter generation and checking within that quantum. Runtime
    errors propagate; neither budget exhaustion nor a failed candidate is a
    semantic negative. Fair search over candidates/efforts is a separate owner.
    """
    if budget < 0 or quantum <= 0:
        raise ValueError("budget must be nonnegative and quantum positive")
    obligations = problem.obligations()
    ids = [identity for identity, _ in candidate.rules]
    if len(ids) != len(set(ids)):
        return Invalid("duplicate evidence for a production")
    expected = {goal.rule.identity for goal in obligations}
    provided = set(ids)
    if provided - expected:
        return Invalid("evidence names a production outside the exact root grammar")
    if expected - provided:
        return Pending("evidence does not cover every root-reachable production")
    root = RootGoal(dict(problem.statements)[problem.start], problem.goal)
    quanta = efforts if efforts is not None else (quantum,) * (len(obligations) + 1)
    if len(quanta) != len(obligations) + 1 or any(q <= 0 for q in quanta):
        raise ValueError("efforts must give a positive budget for every exact obligation")
    evidence = dict(candidate.rules)
    proofs: list[Proof] = []
    for goal, effort in zip((*obligations, root), quanta):
        if budget < effort:
            return Pending("coverage checking resource exhausted")
        budget -= effort
        term = candidate.root if isinstance(goal, RootGoal) else evidence[goal.rule.identity]
        result = check(problem.source, goal, term, effort)
        if isinstance(result, (Invalid, Pending)):
            return result
        if not isinstance(result, Checked):
            raise TypeError("the source checker returned an invalid outcome")
        proofs.append(result.proof)
    return CompleteCover(problem, obligations, tuple(proofs[:-1]), root, proofs[-1])


@dataclass(frozen=True)
class SelectionGoal:
    """The full source judgment and comparison program are fixed, not inferred
    from this route's endpoints or from a proof search's enumeration order.
    Native production fields are closed typed Lean expressions with full context.
    """
    route: Word
    judgment: Hashable
    comparison_program: Hashable


@dataclass(frozen=True)
class Selected(Generic[Source, Statement, Proof]):
    cover: CompleteCover[Source, Statement, Proof]
    goal: SelectionGoal
    occurrences: tuple


def prepare_selection(
    source: Source,
    rules: tuple[PrefixRule, ...],
    initial: Word,
    targets: frozenset[Word],
    statements: tuple[tuple[Node, Statement], ...],
    goal: SelectionGoal,
) -> FixedProblem:
    """Prepare from the original rule table; a caller cannot prune the grammar.

    A route is checked before coverage. In particular, a vacuous cover of an
    empty reading language cannot authorize execution of a nonexistent reading.
    This preparation does not assert mathematical agreement or pick a provider.
    """
    language = compile_routes(rules, initial, targets)
    language.reconstruct(goal.route)
    base = from_trace_grammar(source, language.grammar, statements, goal)
    return FixedProblem(base.source, base.start, base.rules, base.statements,
                        base.goal, (tuple(rules), tuple(initial), frozenset(targets)))


def authorize_selection(cover: CompleteCover) -> Selected | Invalid:
    """Require the exact checked coverage and a real member, not a raw count.

    The reference rechecks structural preparation against the original table.
    Native production retains the checked immutable preparation instead. Neither
    implementation calls a provider to determine mathematical selection.
    """
    p = cover.problem
    if not isinstance(p.goal, SelectionGoal) or p.route_binding is None:
        return Invalid("a generic coverage theorem is not a prepared selection")
    rules, initial, targets = p.route_binding
    language = compile_routes(rules, initial, targets)
    exact = from_trace_grammar(p.source, language.grammar, p.statements, p.goal)
    if p.start != exact.start or frozenset(p.rules) != frozenset(exact.rules):
        return Invalid("coverage used a different or pruned grammar")
    if cover.obligations != p.obligations() or len(cover.rule_proofs) != len(cover.obligations):
        return Invalid("checked coverage does not contain every prepared obligation")
    if cover.root_goal != RootGoal(dict(p.statements)[p.start], p.goal):
        return Invalid("checked root is not the complete fixed selection goal")
    try:
        occurrences = language.reconstruct(p.goal.route)
    except ValueError as error:
        return Invalid(str(error))
    return Selected(cover, p.goal, occurrences)
