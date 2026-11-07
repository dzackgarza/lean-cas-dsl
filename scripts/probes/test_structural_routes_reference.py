"""Independent finite checks of the unbounded first-hit grammar algorithm.

Bounded source execution is only a test oracle. compile_routes and its grammar
queries use finite saturation, not a chosen path or stack-depth bound.
"""
from __future__ import annotations

import itertools
import random
import unittest

from structural_routes_reference import PrefixRule, Production, TraceGrammar, compile_routes


def bounded_source_traces(rules, initial, targets, bound):
    """Separate direct evaluator of the original prefix-rule definition."""
    targets = set(targets)
    frontier = [(initial, ())]
    accepted = set()
    for _ in range(bound + 1):
        following = []
        for word, trace in frontier:
            if word in targets:
                accepted.add(trace)
            elif len(trace) < bound:
                for rule in rules:
                    n = len(rule.lhs)
                    if word[:n] == rule.lhs:
                        following.append((rule.rhs + word[n:], trace + (rule.name,)))
        frontier = following
    return accepted


def graph_reachable(edges, initial, targets):
    seen = {initial}
    work = [initial]
    while work:
        at = work.pop()
        if at in targets:
            return True
        for a, b in edges:
            if a == at and b not in seen:
                seen.add(b)
                work.append(b)
    return False


class StructuralRouteTests(unittest.TestCase):
    def test_every_three_vertex_graph_reachability(self):
        vertices = ('A', 'B', 'C')
        possible = tuple(itertools.product(vertices, repeat=2))
        for mask in range(1 << len(possible)):
            edges = tuple(edge for i, edge in enumerate(possible) if mask & (1 << i))
            rules = tuple(PrefixRule(f'e{i}', (a,), (b,)) for i, (a, b) in enumerate(edges))
            for subset in range(1, 8):
                targets = {v for i, v in enumerate(vertices) if subset & (1 << i)}
                for initial in vertices:
                    language = compile_routes(rules, (initial,), ((v,) for v in targets))
                    observed = language.grammar.shortest()
                    with self.subTest(mask=mask, targets=targets, initial=initial):
                        self.assertEqual(observed is not None, graph_reachable(edges, initial, targets))
                        if observed is not None:
                            language.reconstruct(observed)

    def test_unbounded_growth_and_balanced_traces(self):
        rules = (PrefixRule('push', ('A',), ('A', 'c')),
                 PrefixRule('switch', ('A',), ('B',)),
                 PrefixRule('pop', ('B', 'c'), ('B',)))
        language = compile_routes(rules, ('A',), (('B',),))
        self.assertEqual(language.grammar.shortest(), ('switch',))
        self.assertEqual(language.grammar.distinct_word_count(), 2)
        for n in range(18):
            word = ('push',) * n + ('switch',) + ('pop',) * n
            self.assertTrue(language.grammar.contains(word))
            actual = language.reconstruct(word)
            self.assertEqual(actual[n].outer_context, ('c',) * n)
            if n:
                self.assertFalse(language.grammar.contains(word[:-1]))
        self.assertFalse(language.grammar.contains(('switch', 'push')))

    def test_first_binding_changes_language_not_just_endpoint(self):
        rules = (PrefixRule('push', ('A',), ('A', 'c')),
                 PrefixRule('switch', ('A',), ('B',)),
                 PrefixRule('pop', ('B', 'c'), ('B',)))
        language = compile_routes(rules, ('A',), (('B',), ('A', 'c')))
        expected = {('push',), ('switch',)}
        for n in range(5):
            for word in itertools.product(('push', 'switch', 'pop'), repeat=n):
                self.assertEqual(language.grammar.contains(word), word in expected)
        with self.assertRaises(ValueError):
            language.reconstruct(('push', 'switch', 'pop'))

    def test_ungrounded_growth_is_proved_empty(self):
        language = compile_routes((PrefixRule('grow', ('A',), ('A', 'c')),), ('A',), (('B',),))
        self.assertIsNone(language.grammar.shortest())
        self.assertEqual(language.grammar.distinct_word_count(), 0)
        self.assertFalse(language.grammar.contains(()))

    def test_empty_targets_and_initial_owner(self):
        rules = (PrefixRule('loop', ('A',), ('A',)),)
        absent = compile_routes(rules, ('A',), ())
        self.assertEqual(absent.grammar.distinct_word_count(), 0)
        present = compile_routes(rules, ('A',), (('A',),))
        self.assertEqual(present.grammar.shortest(), ())
        self.assertEqual(present.grammar.distinct_word_count(), 1)
        self.assertFalse(present.grammar.contains(('loop',)))
        self.assertEqual(present.reconstruct(()), ())

    def test_long_prefix_rules_do_not_interleave(self):
        rules = (PrefixRule('long', ('A', 'c', 'd'), ('B', 'e', 'f', 'g')),
                 PrefixRule('finish', ('B', 'e', 'f', 'g'), ('Z',)),
                 PrefixRule('intruder', ('c',), ('Z',)))
        good = compile_routes(rules, ('A', 'c', 'd'), (('Z',),))
        self.assertEqual(good.grammar.shortest(), ('long', 'finish'))
        self.assertEqual(good.grammar.distinct_word_count(), 1)
        bad = compile_routes(rules, ('A', 'c', 'x'), (('Z',),))
        self.assertIsNone(bad.grammar.shortest())
        self.assertFalse(bad.grammar.contains(('intruder',)))

    def test_deep_initial_context_without_default_fuel(self):
        rules = (PrefixRule('shrink', ('A', 'c'), ('A',)),)
        language = compile_routes(rules, ('A',) + ('c',) * 80, (('A',),))
        self.assertEqual(language.grammar.shortest(), ('shrink',) * 80)
        self.assertEqual(language.grammar.distinct_word_count(), 1)

    def test_distinct_source_ids_survive_same_endpoints(self):
        rules = (PrefixRule('left', ('A',), ('B',)), PrefixRule('right', ('A',), ('B',)))
        language = compile_routes(rules, ('A',), (('B',),))
        self.assertEqual(language.grammar.distinct_word_count(), 2)
        self.assertTrue(language.grammar.contains(('left',)))
        self.assertTrue(language.grammar.contains(('right',)))
        self.assertNotEqual(language.reconstruct(('left',)), language.reconstruct(('right',)))

    def test_duplicate_parses_are_not_distinct_trace_words(self):
        a, b, s = (0, 'a', 0), (0, 'b', 0), (0, 's', 0)
        grammar = TraceGrammar(s, {s: frozenset({Production(None, (a,)), Production(None, (b,))}),
                                  a: frozenset({Production('x', ())}), b: frozenset({Production('x', ())})})
        self.assertEqual(grammar.distinct_word_count(), 1)
        self.assertEqual(grammar.shortest(), ('x',))
        self.assertTrue(grammar.contains(('x',)))

    def test_seeded_random_prefix_systems_exact_bounded_membership(self):
        rng = random.Random(404716)
        endpoints = (('A',), ('B',), ('A', 'c'), ('B', 'c'), ('A', 'd'), ('B', 'd'), ('A', 'c', 'd'))
        for trial in range(40):
            rules = tuple(PrefixRule(f'r{i}', rng.choice(endpoints), rng.choice(endpoints)) for i in range(3))
            initial = rng.choice(endpoints)
            targets = frozenset(rng.sample(endpoints, rng.randrange(1, 3)))
            language = compile_routes(rules, initial, targets)
            expected = bounded_source_traces(rules, initial, targets, 4)
            for n in range(5):
                for trace in itertools.product(('r0', 'r1', 'r2'), repeat=n):
                    with self.subTest(trial=trial, trace=trace):
                        self.assertEqual(language.grammar.contains(trace), trace in expected)
            for trace in expected:
                language.reconstruct(trace)

    def test_repeated_cycle_justification_not_dropped(self):
        rules = (PrefixRule('loop', ('A',), ('A',)), PrefixRule('exit', ('A',), ('B',)))
        language = compile_routes(rules, ('A',), (('B',),))
        for n in range(20):
            self.assertTrue(language.grammar.contains(('loop',) * n + ('exit',)))
        self.assertEqual(language.grammar.distinct_word_count(), 2)

    def test_exact_finite_language_and_silent_cycles(self):
        a, s = (0, 'a', 0), (0, 's', 0)
        silent = TraceGrammar(s, {s: frozenset({Production(None, (s,)), Production('x', ()), Production('y', ())})})
        self.assertEqual(silent.finite_words(), frozenset({('x',), ('y',)}))
        growing = TraceGrammar(s, {s: frozenset({Production(None, (a, s)), Production(None, ())}), a: frozenset({Production('x', ())})})
        self.assertIsNone(growing.finite_words())
        dead = TraceGrammar(s, {s: frozenset({Production('x', (s,))})})
        self.assertEqual(dead.finite_words(), frozenset())
        diamond = (PrefixRule('ab', ('A',), ('B',)), PrefixRule('ac', ('A',), ('C',)), PrefixRule('bd', ('B',), ('D',)), PrefixRule('cd', ('C',), ('D',)))
        language = compile_routes(diamond, ('A',), (('D',),))
        self.assertEqual(language.grammar.finite_words(), frozenset({('ab', 'bd'), ('ac', 'cd')}))
        looping = compile_routes((PrefixRule('loop', ('A',), ('A',)), PrefixRule('exit', ('A',), ('B',))), ('A',), (('B',),))
        self.assertIsNone(looping.grammar.finite_words())

    def test_input_validation_and_no_fake_derivations(self):
        with self.assertRaises(ValueError):
            PrefixRule('empty', (), ('A',))
        rule = PrefixRule('x', ('A',), ('B',))
        with self.assertRaises(ValueError):
            compile_routes((rule, rule), ('A',), (('B',),))
        language = compile_routes((rule,), ('A',), (('B',),))
        for trace in ((), ('unknown',), ('x', 'x')):
            with self.assertRaises(ValueError):
                language.reconstruct(trace)
        with self.assertRaises(ValueError):
            language.grammar.intersects_dfa((0,), 0, frozenset({0}), lambda p, a: 9)


if __name__ == '__main__':
    unittest.main(verbosity=2)
