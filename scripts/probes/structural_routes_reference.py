"""Exact first-hit route languages for finite ground-prefix structural rules.

Engineering reference for the source correspondence documented in issue #66.
It decides structural reachability and represents *all* finite first-hit traces.
It neither identifies mathematical meanings nor accepts provider proof data.

A rule lhs -> rhs applies at a word prefix. Words encode an entire residual
category atom followed by its inner-to-outer unary constructor context. The
production adapter must retain exact source identities, parameters and roles.
Strings below are model symbols, not names from which semantics are inferred.

Construction: annotate the pushdown stack by a bottom-up target DFA, make target
configurations absorbing, and compute productive empty-stack summaries. Keep
all productive grammar alternatives, not only first-discovery witnesses.
The algorithms have no route/stack depth cutoff. Resource exhaustion must not
be translated into mathematical absence or ambiguity by a production caller.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Callable, Hashable, Iterable

Word = tuple[str, ...]
State = int
Symbol = Hashable
Summary = tuple[State, Symbol, State]


@dataclass(frozen=True)
class PrefixRule:
    name: str
    lhs: Word
    rhs: Word

    def __post_init__(self) -> None:
        if not self.name or not self.lhs or not self.rhs:
            raise ValueError("source rules require an identity and nonempty endpoints")
        if not all(isinstance(x, str) and x for x in self.lhs + self.rhs):
            raise ValueError("source symbols must be nonempty strings")


@dataclass(frozen=True)
class Transition:
    source: State
    pop: Symbol
    target: State
    push: tuple[Symbol, ...]
    emit: str | None = None


@dataclass(frozen=True)
class Production:
    """A source trace symbol, possibly epsilon, followed by child summaries."""
    emit: str | None
    children: tuple[Summary, ...]


@dataclass
class TraceGrammar:
    start: Summary
    productions: dict[Summary, frozenset[Production]]

    def shortest(self) -> Word | None:
        """Least trace in shortlex order, or None iff the language is empty."""
        best: dict[Summary, Word] = {}
        changed = True
        while changed:
            changed = False
            for lhs, alternatives in self.productions.items():
                for alternative in alternatives:
                    if not all(child in best for child in alternative.children):
                        continue
                    word = (() if alternative.emit is None else (alternative.emit,))
                    word += tuple(x for child in alternative.children for x in best[child])
                    old = best.get(lhs)
                    if old is None or (len(word), word) < (len(old), old):
                        best[lhs] = word
                        changed = True
        return best.get(self.start)

    def intersects_dfa(
        self,
        states: tuple[int, ...],
        initial: int,
        accepting: frozenset[int],
        step: Callable[[int, str], int],
    ) -> bool:
        """Exact CFL/regular intersection emptiness via finite relations.

        For each nonterminal N, R_N(p,q) means some N-word takes DFA p to q.
        Production interpretation is relational composition, iterated to its
        least fixed point. No generation or sampling of grammar words occurs.
        """
        state_set = frozenset(states)
        if len(state_set) != len(states) or initial not in state_set or not accepting <= state_set:
            raise ValueError("invalid finite automaton state set")
        alphabet = {a.emit for alternatives in self.productions.values() for a in alternatives if a.emit is not None}
        moves = {(p, a): step(p, a) for p in states for a in alphabet}
        if not all(q in state_set for q in moves.values()):
            raise ValueError("DFA transition leaves its state set")
        relations = {nt: set() for nt in self.productions}
        changed = True
        while changed:
            changed = False
            for lhs, alternatives in self.productions.items():
                for alternative in alternatives:
                    edges = {(p, p) for p in states} if alternative.emit is None else {(p, moves[p, alternative.emit]) for p in states}
                    for child in alternative.children:
                        rhs = relations.get(child, set())
                        edges = {(p, r) for p, q in edges for q2, r in rhs if q == q2}
                        if not edges:
                            break
                    before = len(relations[lhs])
                    relations[lhs].update(edges)
                    changed |= len(relations[lhs]) != before
        return any(p == initial and q in accepting for p, q in relations.get(self.start, set()))

    def contains(self, word: Word) -> bool:
        dead = len(word) + 1
        states = tuple(range(dead + 1))
        def step(position: int, letter: str) -> int:
            return position + 1 if position < len(word) and word[position] == letter else dead
        return self.intersects_dfa(states, 0, frozenset({len(word)}), step)

    def finite_words(self) -> frozenset[Word] | None:
        """Enumerate the exact raw language if finite; None means infinite.

        A productive dependency cycle is length-growing exactly when some
        edge has a terminal or a nonempty sibling derivation in its context.
        Silent recursive parses alone do not imply infinitely many words.
        """
        productive: set[Summary] = set()
        nonempty: set[Summary] = set()
        changed = True
        while changed:
            changed = False
            for lhs, alternatives in self.productions.items():
                for alternative in alternatives:
                    if all(child in productive for child in alternative.children):
                        if lhs not in productive:
                            productive.add(lhs)
                            changed = True
                        if (alternative.emit is not None or any(child in nonempty for child in alternative.children)) and lhs not in nonempty:
                            nonempty.add(lhs)
                            changed = True
        graph: dict[Summary, set[Summary]] = defaultdict(set)
        growing = []
        for lhs, alternatives in self.productions.items():
            for alternative in alternatives:
                if not all(child in productive for child in alternative.children):
                    continue
                for i, child in enumerate(alternative.children):
                    graph[lhs].add(child)
                    if alternative.emit is not None or any(other in nonempty for j, other in enumerate(alternative.children) if i != j):
                        growing.append((lhs, child))
        def reachable(source: Summary) -> set[Summary]:
            seen = {source}
            work = [source]
            while work:
                for target in graph.get(work.pop(), ()):
                    if target not in seen:
                        seen.add(target)
                        work.append(target)
            return seen
        live = reachable(self.start)
        for source, target in growing:
            if source in live and source in reachable(target):
                return None
        # Absence of a growing cycle proves that this monotone finite-language
        # fixed point terminates. Do not truncate its words or derivations.
        languages: dict[Summary, set[Word]] = {nt: set() for nt in live}
        changed = True
        while changed:
            changed = False
            for lhs in live:
                for alternative in self.productions.get(lhs, ()):
                    if not all(child in productive for child in alternative.children):
                        continue
                    words = {() if alternative.emit is None else (alternative.emit,)}
                    for child in alternative.children:
                        words = {prefix + suffix for prefix in words for suffix in languages[child]}
                    before = len(languages[lhs])
                    languages[lhs].update(words)
                    changed |= len(languages[lhs]) != before
        return frozenset(languages.get(self.start, set()))

    def distinct_word_count(self) -> int:
        """0, 1 or 2 (meaning >=2) *raw traces*, never semantic meanings."""
        witness = self.shortest()
        if witness is None:
            return 0
        dead = len(witness) + 1
        states = tuple(range(dead + 1))
        def step(position: int, letter: str) -> int:
            return position + 1 if position < len(witness) and witness[position] == letter else dead
        accepts_other = frozenset(p for p in states if p != len(witness))
        return 2 if self.intersects_dfa(states, 0, accepts_other, step) else 1


@dataclass(frozen=True)
class RouteOccurrence:
    rule: str
    source: Word
    target: Word
    outer_context: Word


@dataclass
class RouteLanguage:
    rules: tuple[PrefixRule, ...]
    initial: Word
    targets: frozenset[Word]
    grammar: TraceGrammar
    controls: int
    transition_count: int

    def reconstruct(self, trace: Word) -> tuple[RouteOccurrence, ...]:
        """Reconstruct formal source occurrences, never lost runtime values."""
        by_name = {rule.name: rule for rule in self.rules}
        at = self.initial
        out = []
        for name in trace:
            if at in self.targets:
                raise ValueError("route continues after a first binding")
            rule = by_name.get(name)
            if rule is None or at[:len(rule.lhs)] != rule.lhs:
                raise ValueError("trace is not a composable source derivation")
            context = at[len(rule.lhs):]
            target = rule.rhs + context
            out.append(RouteOccurrence(name, at, target, context))
            at = target
        if at not in self.targets:
            raise ValueError("route does not reach an owner/binding")
        return tuple(out)


class _TargetDFA:
    def __init__(self, targets: frozenset[tuple[Symbol, ...]]):
        reversed_targets = {tuple(reversed(word)) for word in targets}
        prefixes = {()}
        for word in reversed_targets:
            prefixes.update(word[:i] for i in range(len(word) + 1))
        # Ordering affects only internal identity, never route choice.
        self.prefixes = sorted(prefixes, key=lambda p: (len(p), repr(p)))
        self.index = {p: i for i, p in enumerate(self.prefixes)}
        self.dead = len(self.prefixes)
        self.states = tuple(range(self.dead + 1))
        self.initial = self.index[()]
        self.accepting = frozenset(self.index[word] for word in reversed_targets)

    def step(self, state: int, letter: Symbol) -> int:
        if state == self.dead:
            return self.dead
        return self.index.get(self.prefixes[state] + (letter,), self.dead)


def _productive_grammar(transitions: tuple[Transition, ...], start: Summary) -> TraceGrammar:
    """All productive PDA-to-CFG productions, with push words of length <=2."""
    finishes: dict[tuple[State, Symbol], set[State]] = defaultdict(set)
    changed = True
    while changed:
        changed = False
        for rule in transitions:
            if not rule.push:
                ends = {rule.target}
            elif len(rule.push) == 1:
                ends = set(finishes[rule.target, rule.push[0]])
            else:
                ends = {end for middle in tuple(finishes[rule.target, rule.push[0]]) for end in tuple(finishes[middle, rule.push[1]])}
            destination = finishes[rule.source, rule.pop]
            before = len(destination)
            destination.update(ends)
            changed |= len(destination) != before
    alternatives: dict[Summary, set[Production]] = defaultdict(set)
    for rule in transitions:
        if not rule.push:
            alternatives[rule.source, rule.pop, rule.target].add(Production(rule.emit, ()))
        elif len(rule.push) == 1:
            for end in finishes[rule.target, rule.push[0]]:
                alternatives[rule.source, rule.pop, end].add(Production(rule.emit, ((rule.target, rule.push[0], end),)))
        else:
            first, second = rule.push
            for middle in finishes[rule.target, first]:
                for end in finishes[middle, second]:
                    alternatives[rule.source, rule.pop, end].add(Production(rule.emit, ((rule.target, first, middle), (middle, second, end))))
    # Remove unreachable grammar nodes, but never an alternative of a reachable one.
    reached = {start}
    work = [start]
    while work:
        for alternative in alternatives.get(work.pop(), ()):
            for child in alternative.children:
                if child not in reached:
                    reached.add(child)
                    work.append(child)
    return TraceGrammar(start, {nt: frozenset(alternatives.get(nt, ())) for nt in reached})


def compile_routes(rules: Iterable[PrefixRule], initial: Word, targets: Iterable[Word]) -> RouteLanguage:
    """Compile the exact complete first-hit relation to a finite trace grammar."""
    rules = tuple(rules)
    targets = frozenset(tuple(word) for word in targets)
    if not initial or any(not word for word in targets):
        raise ValueError("source category words must be nonempty")
    if len({rule.name for rule in rules}) != len(rules):
        raise ValueError("source rule identities must be unique")
    words = (initial, *targets, *(word for rule in rules for word in (rule.lhs, rule.rhs)))
    if not all(isinstance(x, str) and x for word in words for x in word):
        raise ValueError("source symbols must be nonempty strings")
    bottom: Symbol = ("private", "bottom")
    start_symbol: Symbol = ("private", "start")
    source_alphabet: tuple[Symbol, ...] = tuple(sorted({x for word in words for x in word})) + (bottom,)
    dfa = _TargetDFA(frozenset(word + (bottom,) for word in targets))
    annotated = tuple((letter, summary) for letter in source_alphabet for summary in dfa.states)

    def annotate(word: tuple[Symbol, ...], below: int) -> tuple[Symbol, ...]:
        reversed_out = []
        state = below
        for letter in reversed(word):
            reversed_out.append((letter, state))
            state = dfa.step(state, letter)
        return tuple(reversed(reversed_out))

    normal, drain, final, init = 0, 1, 2, 3
    next_state = 4
    transitions: list[Transition] = []

    def fresh() -> int:
        nonlocal next_state
        state = next_state
        next_state += 1
        return state

    def emit_push(source: int, pop: Symbol, target: int, push: tuple[Symbol, ...], emit: str | None) -> None:
        # Normalize a long push through private controls; all intermediate
        # transitions are silent and cannot start another source rule or accept.
        if len(push) <= 2:
            transitions.append(Transition(source, pop, target, push, emit))
            return
        control = fresh()
        transitions.append(Transition(source, pop, control, push[-2:], emit))
        for i in range(len(push) - 3, -1, -1):
            following = target if i == 0 else fresh()
            transitions.append(Transition(control, push[i + 1], following, (push[i], push[i + 1]), None))
            control = following

    for rule in rules:
        matching = [normal] + [fresh() for _ in rule.lhs[1:]]
        for i, expected in enumerate(rule.lhs):
            for summary in dfa.states:
                if i == 0 and dfa.step(summary, expected) in dfa.accepting:
                    continue
                top: Symbol = (expected, summary)
                if i + 1 < len(rule.lhs):
                    transitions.append(Transition(matching[i], top, matching[i + 1], (), None))
                else:
                    emit_push(matching[i], top, normal, annotate(rule.rhs, summary), rule.name)
    for top in annotated:
        letter, summary = top
        if letter == bottom:
            transitions.append(Transition(drain, top, final, (), None))
        else:
            transitions.append(Transition(drain, top, drain, (), None))
            if dfa.step(summary, letter) in dfa.accepting:
                transitions.append(Transition(normal, top, drain, (), None))
    emit_push(init, start_symbol, normal, annotate(initial + (bottom,), dfa.initial), None)
    unique_transitions = tuple(dict.fromkeys(transitions))
    start = (init, start_symbol, final)
    grammar = _productive_grammar(unique_transitions, start)
    return RouteLanguage(rules, initial, targets, grammar, next_state, len(unique_transitions))
