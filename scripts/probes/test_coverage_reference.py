"""Hostile coverage-boundary tests; not the project's mathematical acceptance.

The example interpretation is integer trace weight. The goal and its local
invariants are fixed before proof candidates. Its source checker verifies the
actual production equation, not a candidate-supplied predicate or expected value.
"""
from dataclasses import FrozenInstanceError, replace
from itertools import product
import unittest

from coverage_reference import (
    Candidate, Checked, CompleteCover, FixedProblem, Invalid, Pending,
    RootGoal, Rule, RuleGoal, check_cover, from_trace_grammar,
    SelectionGoal, Selected, prepare_selection, authorize_selection,
)


SOURCE = ("fixed trace interpretation", (("push", 1), ("pop", -1), ("switch", 0), ("bad", 2)))
RULES = (
    Rule("base", "S", (), "switch"),
    Rule("nest", "S", ("P", "S", "Q"), "epsilon"),
    Rule("left", "P", (), "push"),
    Rule("right", "Q", (), "pop"),
)
STATEMENTS = (("S", 0), ("P", 1), ("Q", -1))


def fixed_problem(rules=RULES, goal=0, statements=STATEMENTS, source=SOURCE):
    return FixedProblem(source, "S", rules, statements, goal)


def term_for(goal):
    # Proof syntax is fully goal-bound. It contains no alternative denotation.
    return ("check source arithmetic", goal)


def candidate_for(problem):
    root = RootGoal(dict(problem.statements)[problem.start], problem.goal)
    return Candidate(tuple((g.rule.identity, term_for(g)) for g in problem.obligations()), term_for(root))


def check_weight(source, goal, evidence, budget):
    if budget < 1:
        return Pending("budget")
    if evidence != term_for(goal):
        return Invalid("proof does not have this complete source goal")
    if isinstance(goal, RootGoal):
        valid = goal.premise == goal.conclusion
    else:
        weights = dict(source[1])
        if goal.rule.action in ("epsilon", None):
            weight = 0
        elif goal.rule.action in weights:
            weight = weights[goal.rule.action]
        else:
            return Invalid("unknown source action")
        valid = weight + sum(goal.premises) == goal.conclusion
    return Checked((source, goal)) if valid else Invalid("source equation is false")


class CoverageTests(unittest.TestCase):
    def test_infinite_balanced_language_has_complete_finite_cover(self):
        p = fixed_problem()
        result = check_cover(p, candidate_for(p), check_weight, budget=5)
        self.assertIsInstance(result, CompleteCover)
        self.assertEqual(tuple(g.rule.identity for g in result.obligations), ("base", "nest", "left", "right"))
        self.assertEqual(len(result.rule_proofs), 4)
        # Separate finite observations of the unbounded inductive family.
        for n in range(100):
            trace = ("push",) * n + ("switch",) + ("pop",) * n
            self.assertEqual(sum(dict(SOURCE[1])[letter] for letter in trace), 0)

    def test_pairwise_or_prefix_evidence_cannot_complete_aggregate(self):
        p = fixed_problem()
        c = candidate_for(p)
        calls = []
        result = check_cover(p, Candidate(c.rules[:1], c.root),
                             lambda *args: calls.append(args) or Checked("fake"), budget=20)
        self.assertIsInstance(result, Pending)
        self.assertEqual(calls, [])

    def test_omitted_recursive_alternative_is_not_inferred_from_base(self):
        p = fixed_problem()
        c = candidate_for(p)
        self.assertIsInstance(check_cover(p, Candidate(tuple(x for x in c.rules if x[0] != "nest"), c.root),
                                          check_weight, budget=20), Pending)

    def test_each_reachable_alternative_is_checked(self):
        p = fixed_problem(RULES + (Rule("bad branch", "S", (), "bad"),))
        self.assertIsInstance(check_cover(p, candidate_for(p), check_weight, budget=20), Invalid)

    def test_duplicate_identity_and_extra_evidence_are_rejected(self):
        p = fixed_problem()
        c = candidate_for(p)
        for extras in ((c.rules[0],), (("foreign", "arbitrary"),)):
            self.assertIsInstance(check_cover(p, Candidate(c.rules + extras, c.root), check_weight, budget=20), Invalid)

    def test_distinct_occurrences_are_not_merged_by_equal_action(self):
        p = fixed_problem(RULES + (Rule("other base occurrence", "S", (), "switch"),))
        c = candidate_for(p)
        self.assertEqual(len(c.rules), 5)
        self.assertIsInstance(check_cover(p, c, check_weight, budget=6), CompleteCover)
        self.assertIsInstance(check_cover(p, Candidate(c.rules[:-1], c.root), check_weight, budget=6), Pending)

    def test_root_conclusion_cannot_be_replaced_by_easier_invariant(self):
        p = fixed_problem(goal=1)
        self.assertIsInstance(check_cover(p, candidate_for(p), check_weight, budget=5), Invalid)
        old = candidate_for(fixed_problem())
        self.assertIsInstance(check_cover(p, old, check_weight, budget=5), Invalid)

    def test_changed_source_invalidates_old_proofs(self):
        old = fixed_problem()
        new = fixed_problem(source=("changed source", (("push", 1), ("pop", 0), ("switch", 0), ("bad", 2))))
        self.assertIsInstance(check_cover(new, candidate_for(old), check_weight, budget=20), Invalid)

    def test_child_order_and_action_are_part_of_the_exact_goal(self):
        old = fixed_problem()
        swapped = tuple(Rule(r.identity, r.parent, tuple(reversed(r.children)), r.action)
                        if r.identity == "nest" else r for r in RULES)
        new = fixed_problem(swapped)
        self.assertIsInstance(check_cover(new, candidate_for(old), check_weight, budget=20), Invalid)
        self.assertIsInstance(check_cover(new, candidate_for(new), check_weight, budget=20), CompleteCover)

    def test_unreachable_rule_does_not_become_an_unrelated_prerequisite(self):
        p = fixed_problem(RULES + (Rule("unrelated", "U", (), "bad"),),
                          statements=STATEMENTS + (("U", 0),))
        self.assertEqual(len(p.obligations()), 4)
        self.assertIsInstance(check_cover(p, candidate_for(p), check_weight, budget=5), CompleteCover)

    def test_actual_transitive_child_closure(self):
        rules = (Rule("s", "S", ("A",), "epsilon"), Rule("a", "A", ("B",), "epsilon"),
                 Rule("b", "B", (), "switch"), Rule("cycle", "A", ("S",), "epsilon"))
        p = fixed_problem(rules, statements=(("S", 0), ("A", 0), ("B", 0)))
        self.assertEqual(len(p.obligations()), 4)
        self.assertIsInstance(check_cover(p, candidate_for(p), check_weight, budget=5), CompleteCover)

    def test_resource_limits_do_not_create_success_or_semantic_negative(self):
        p = fixed_problem()
        for budget in range(5):
            calls = []
            def check(*args):
                calls.append(args[-1])
                return check_weight(*args)
            result = check_cover(p, candidate_for(p), check, budget=budget)
            self.assertIsInstance(result, Pending)
            self.assertLessEqual(sum(calls), budget)
        self.assertIsInstance(check_cover(p, candidate_for(p), lambda *_: Pending("deferred"), budget=20), Pending)

    def test_checker_failure_is_not_misclassified(self):
        p = fixed_problem()
        def broken(*_):
            raise RuntimeError("source service failed")
        with self.assertRaisesRegex(RuntimeError, "source service failed"):
            check_cover(p, candidate_for(p), broken, budget=20)
        with self.assertRaises(TypeError):
            check_cover(p, candidate_for(p), lambda *_: True, budget=20)

    def test_invalid_problem_and_limits(self):
        for rules in (RULES + (RULES[0],), (Rule("bad", "S", ("missing",), "epsilon"),)):
            with self.assertRaises(ValueError):
                fixed_problem(rules)
        with self.assertRaises(ValueError):
            fixed_problem(statements=(("P", 1),))
        with self.assertRaises(ValueError):
            fixed_problem(statements=STATEMENTS + (("S", 1),))
        p = fixed_problem()
        for budget, quantum in ((-1, 1), (1, 0)):
            with self.assertRaises(ValueError):
                check_cover(p, candidate_for(p), check_weight, budget=budget, quantum=quantum)
        with self.assertRaises(FrozenInstanceError):
            p.goal = 1

    def test_all_subsets_of_local_evidence_have_exact_completion_condition(self):
        p = fixed_problem()
        c = candidate_for(p)
        for mask in range(16):
            subset = tuple(x for i, x in enumerate(c.rules) if mask & (1 << i))
            result = check_cover(p, Candidate(subset, c.root), check_weight, budget=20)
            self.assertEqual(isinstance(result, CompleteCover), mask == 15)

    def test_source_fixed_equations_over_all_small_weights(self):
        # Independent exhaustive arithmetic calculation of every local condition.
        for a, b, root_weight in product(range(-2, 3), repeat=3):
            source = ("arithmetic", (("push", a), ("pop", b), ("switch", root_weight)))
            p = fixed_problem(goal=root_weight, source=source,
                              statements=(("S", root_weight), ("P", a), ("Q", b)))
            result = check_cover(p, candidate_for(p), check_weight, budget=20)
            self.assertEqual(isinstance(result, CompleteCover), a + b == 0)


    def test_real_compiler_infinite_route_language_is_fully_covered(self):
        from structural_routes_reference import PrefixRule, TraceGrammar, compile_routes
        rules = (PrefixRule("push", ("A",), ("A", "c")),
                 PrefixRule("switch", ("A",), ("B",)),
                 PrefixRule("pop", ("B", "c"), ("B",)))
        language = compile_routes(rules, ("A",), (("B",),))
        grammar = language.grammar
        self.assertIsNone(grammar.finite_words())
        # Propose one potential per stack summary. Every production, not the
        # samples used to propose it, must pass the actual source equation.
        weights = dict(SOURCE[1])
        statements = []
        for node in grammar.productions:
            witness = TraceGrammar(node, grammar.productions).shortest()
            self.assertIsNotNone(witness)
            statements.append((node, sum(weights[label] for label in witness)))
        problem = from_trace_grammar(SOURCE, grammar, tuple(statements), 0)
        candidate = candidate_for(problem)
        result = check_cover(problem, candidate, check_weight, budget=10000)
        self.assertIsInstance(result, CompleteCover)
        self.assertEqual(len(result.obligations), sum(map(len, grammar.productions.values())))
        self.assertIs(result.problem.source, SOURCE)
        # Changing the mutable reference graph cannot change the prepared goal.
        old_rules = problem.rules
        grammar.productions.clear()
        self.assertEqual(problem.rules, old_rules)
        self.assertIsInstance(check_cover(problem, candidate, check_weight, budget=10000), CompleteCover)

    def test_changed_binding_is_recompiled_and_cannot_reuse_old_cover(self):
        from structural_routes_reference import PrefixRule, TraceGrammar, compile_routes
        rules = (PrefixRule("push", ("A",), ("A", "c")),
                 PrefixRule("switch", ("A",), ("B",)),
                 PrefixRule("pop", ("B", "c"), ("B",)))
        grammar = compile_routes(rules, ("A",), (("B",), ("A", "c"))).grammar
        self.assertEqual(grammar.finite_words(), frozenset({("push",), ("switch",)}))
        statements = tuple((node, sum(dict(SOURCE[1])[label]
                                     for label in TraceGrammar(node, grammar.productions).shortest()))
                           for node in grammar.productions)
        p = from_trace_grammar(SOURCE, grammar, statements, 0)
        # An earlier binding adds the weight-one route. A sampled zero route
        # cannot be laundered into proof of the unchanged whole-family goal.
        self.assertIsInstance(check_cover(p, candidate_for(p), check_weight, budget=10000), Invalid)

    def test_adapter_cannot_omit_a_statement_owner(self):
        from structural_routes_reference import PrefixRule, compile_routes
        grammar = compile_routes((PrefixRule("switch", ("A",), ("B",)),),
                                 ("A",), (("B",),)).grammar
        all_statements = tuple((node, 0) for node in grammar.productions)
        for statements in (all_statements[:-1], all_statements + (("foreign", 0),)):
            with self.assertRaises(ValueError):
                from_trace_grammar(SOURCE, grammar, statements, 0)


    def selection_problem(self):
        from structural_routes_reference import PrefixRule, TraceGrammar, compile_routes
        rules = (PrefixRule("push", ("A",), ("A", "c")),
                 PrefixRule("switch", ("A",), ("B",)),
                 PrefixRule("pop", ("B", "c"), ("B",)))
        targets = frozenset({("B",)})
        grammar = compile_routes(rules, ("A",), targets).grammar
        statements = tuple((node, sum(dict(SOURCE[1])[letter]
                                     for letter in TraceGrammar(node, grammar.productions).shortest()))
                           for node in grammar.productions)
        goal = SelectionGoal(("push", "switch", "pop"),
                             ("fixed complete weight-zero reading", "rigid source context"),
                             ("retained comparison", "source-directed action"))
        return prepare_selection(SOURCE, rules, ("A",), targets, statements, goal)

    def selection_checker(self, expected_goal):
        def check(source, goal, evidence, budget):
            if isinstance(goal, RootGoal):
                if goal.conclusion != expected_goal or evidence != term_for(goal):
                    return Invalid("wrong whole selection goal or evidence")
                if goal.premise != 0:
                    return Invalid("wrong source interpretation")
                return Checked((source, goal))
            return check_weight(source, goal, evidence, budget)
        return check

    def test_selected_judgment_and_comparison_program_survive(self):
        p = self.selection_problem()
        cover = check_cover(p, candidate_for(p), self.selection_checker(p.goal), budget=10000)
        result = authorize_selection(cover)
        self.assertIsInstance(result, Selected)
        self.assertIs(result.goal, p.goal)
        self.assertEqual(tuple(x.rule for x in result.occurrences), p.goal.route)
        self.assertEqual(result.occurrences[1].outer_context, ("c",))
        self.assertEqual(result.goal.comparison_program, ("retained comparison", "source-directed action"))

    def test_vacuous_coverage_is_not_a_selected_reading(self):
        p = fixed_problem(rules=(), statements=(("S", 0),))
        cover = check_cover(p, candidate_for(p), check_weight, budget=1)
        self.assertIsInstance(cover, CompleteCover)
        self.assertIsInstance(authorize_selection(cover), Invalid)
        from structural_routes_reference import PrefixRule, compile_routes
        rules = (PrefixRule("push", ("A",), ("A", "c")),)
        grammar = compile_routes(rules, ("A",), (("B",),)).grammar
        with self.assertRaises(ValueError):
            prepare_selection(SOURCE, rules, ("A",), frozenset({("B",)}),
                              tuple((node, 0) for node in grammar.productions),
                              SelectionGoal((), "invented reading", "invented comparison"))

    def test_pruned_grammar_cannot_authorize_selection(self):
        p = self.selection_problem()
        cover = check_cover(p, candidate_for(p), self.selection_checker(p.goal), budget=10000)
        # Privileged state corruption must still fail the structural recheck.
        changed = replace(p, rules=p.rules[:-1])
        self.assertIsInstance(authorize_selection(replace(cover, problem=changed)), Invalid)

    def test_root_and_complete_evidence_are_rechecked(self):
        p = self.selection_problem()
        cover = check_cover(p, candidate_for(p), self.selection_checker(p.goal), budget=10000)
        for changed in (replace(cover, rule_proofs=cover.rule_proofs[:-1]),
                        replace(cover, root_goal=RootGoal(0, "easier goal"))):
            self.assertIsInstance(authorize_selection(changed), Invalid)

    def test_fair_discovery_coverage_and_selection_are_connected(self):
        from agreement_search_reference import Accepted, AgreementSearch, Deferred, Found, Rejected, Symbol
        p = self.selection_problem()
        complete = candidate_for(p)
        def check(source, goal, alphabet, term, effort):
            self.assertIs(source, p.source)
            self.assertIs(goal, p.goal)
            candidate = complete if term.symbol == 1 else Candidate(complete.rules[:1], complete.root)
            result = check_cover(p, candidate, self.selection_checker(p.goal), budget=effort)
            if isinstance(result, CompleteCover):
                return Accepted(result)
            if isinstance(result, Invalid):
                return Rejected(result.reason)
            return Deferred(result.reason)
        search = AgreementSearch(p.source, p.goal, (Symbol("source.prefix", 0), Symbol("source.cover", 0)), check)
        result = search.advance(max_pairs=10000, budget=1000000)
        self.assertIsInstance(result, Found)
        self.assertEqual(result.term.symbol, 1)
        self.assertIsInstance(authorize_selection(result.proof), Selected)
        self.assertIs(result.goal, p.goal)

    def test_distinct_exact_efforts_need_no_monotonicity_assumption(self):
        p = fixed_problem()
        goals = (*p.obligations(), RootGoal(0, 0))
        efforts = tuple(range(1, len(goals) + 1))
        required = dict(zip(goals, efforts))
        def check(source, goal, evidence, budget):
            return check_weight(source, goal, evidence, budget) if budget == required[goal] else Pending("different exact effort")
        result = check_cover(p, candidate_for(p), check, budget=sum(efforts), efforts=efforts)
        self.assertIsInstance(result, CompleteCover)
        self.assertIsInstance(check_cover(p, candidate_for(p), check, budget=100, quantum=5), Pending)
        for bad in ((1,), (0,) * len(goals)):
            with self.assertRaises(ValueError):
                check_cover(p, candidate_for(p), check, budget=100, efforts=bad)


if __name__ == "__main__":
    unittest.main(verbosity=2)
