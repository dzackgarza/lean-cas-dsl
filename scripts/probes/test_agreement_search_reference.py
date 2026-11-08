"""Mechanical scheduler tests, not mathematical comparison oracles."""
import itertools
import unittest

from agreement_search_reference import (
    Accepted, AgreementSearch, Deferred, Found, Pending, Rejected, Symbol, Term,
    code_at, decode,
)


class AgreementSearchTests(unittest.TestCase):
    def test_shortlex_unranking(self):
        for alphabet_size in range(1, 5):
            expected = [word for length in range(6)
                        for word in itertools.product(range(alphabet_size), repeat=length)]
            self.assertEqual([code_at(i, alphabet_size) for i in range(len(expected))], expected)

    def test_exact_prefix_decode(self):
        alphabet = (Symbol("source.atom", 0), Symbol("core.binary", 2), Symbol("core.unary", 1))
        self.assertEqual(decode((1, 0, 2, 0), alphabet), Term(1, (Term(0), Term(2, (Term(0),)))))
        for word in ((), (1, 0), (0, 0), (1, 0, 0, 0), (9,), (-1,)):
            self.assertIsNone(decode(word, alphabet))
        # Decoder does not impose the host recursion limit on proof syntax.
        self.assertIsNotNone(decode((2,) * 2500 + (0,), alphabet))

    def test_context_and_goal_are_retained(self):
        context = ("accepted release", ("rigid ring", "selected diagram"))
        goal = ("whole-family equation", ("universe u", "source X", "parameter n"))
        calls = []
        def check(ctx, target, alphabet, term, effort):
            self.assertIs(ctx, context)
            self.assertIs(target, goal)
            calls.append(term)
            return Accepted(("checked proof", term))
        search = AgreementSearch(context, goal, (Symbol("source.equality", 0),), check)
        result = search.advance(max_pairs=20, budget=20)
        self.assertIsInstance(result, Found)
        self.assertEqual(result.code, (0,))
        self.assertEqual(result.proof, ("checked proof", Term(0)))
        self.assertEqual(len(calls), 1)
        self.assertIs(search.advance(max_pairs=0, budget=0), result)

    def test_deferred_earlier_candidate_does_not_starve_later_proof(self):
        alphabet = (Symbol("source.expensive", 0), Symbol("source.valid", 0))
        checked = []
        def check(ctx, goal, alphabet, term, effort):
            checked.append((term.symbol, effort))
            if term.symbol == 0 or effort < 4:
                return Deferred()
            return Accepted("whole checked source proof")
        search = AgreementSearch("source", "fixed goal", alphabet, check)
        result = search.advance(max_pairs=100, budget=10000)
        self.assertIsInstance(result, Found)
        self.assertEqual(result.term, Term(1))
        self.assertIn((1, 4), checked)
        self.assertTrue(any(symbol == 0 for symbol, _ in checked))

    def test_every_small_finite_candidate_and_effort_is_reached(self):
        alphabet = (Symbol("source.nullary", 0), Symbol("core.unary", 1))
        wanted = [(i, decode(code_at(i, 2), alphabet)) for i in range(40)]
        for index, term in wanted:
            if term is None:
                continue
            for required in range(1, 6):
                def check(ctx, goal, alphabet, candidate, effort, term=term, required=required):
                    return Accepted((candidate, effort)) if candidate == term and effort >= required else Deferred()
                search = AgreementSearch("source", "fixed goal", alphabet, check)
                pairs = (index + required + 2) * (index + required + 3) // 2
                result = search.advance(max_pairs=pairs, budget=10**7)
                self.assertIsInstance(result, Found)
                self.assertEqual(result.term, term)

    def test_rejection_is_cached_but_resource_exhaustion_is_not(self):
        calls = {0: [], 1: []}
        def check(ctx, goal, alphabet, term, effort):
            calls[term.symbol].append(effort)
            return Rejected("this candidate is ill-typed") if term.symbol == 0 else Deferred()
        search = AgreementSearch("source", "fixed goal", (Symbol("bad", 0), Symbol("pending", 0)), check)
        self.assertIsInstance(search.advance(max_pairs=100, budget=10000), Pending)
        self.assertEqual(len(calls[0]), 1)
        self.assertGreater(len(calls[1]), 1)
        self.assertIsNone(search.found)

    def test_budget_is_reserved_not_expanded(self):
        spent = []
        def check(ctx, goal, alphabet, term, effort):
            spent.append(effort)
            return Deferred()
        search = AgreementSearch("source", "goal", (Symbol("pending", 0),), check)
        result = search.advance(max_pairs=1000, budget=7)
        self.assertIsInstance(result, Pending)
        self.assertEqual(sum(spent), result.reserved_budget)
        self.assertLessEqual(sum(spent), 7)
        cursor = (search.diagonal, search.position)
        self.assertIsInstance(search.advance(max_pairs=1000, budget=0), Pending)
        self.assertEqual((search.diagonal, search.position), cursor)

    def test_bounded_exhaustion_never_produces_semantic_negative(self):
        search = AgreementSearch("source", "goal", (Symbol("candidate", 0),),
                                 lambda *_: Rejected("not this proof"))
        result = search.advance(max_pairs=200, budget=200)
        self.assertIsInstance(result, Pending)
        self.assertIsNone(search.found)

    def test_internal_error_is_not_a_rejected_candidate(self):
        def broken(*_):
            raise RuntimeError("kernel service failed")
        search = AgreementSearch("source", "goal", (Symbol("candidate", 0),), broken)
        with self.assertRaisesRegex(RuntimeError, "kernel service failed"):
            search.advance(max_pairs=10, budget=10)
        self.assertFalse(search.rejected)
        self.assertIsNone(search.found)

    def test_alphabet_permutation_does_not_change_exact_goal_or_source_evidence(self):
        for names in (("slow", "source.proof"), ("source.proof", "slow")):
            alphabet = tuple(Symbol(name, 0) for name in names)
            def check(ctx, goal, alphabet, term, effort):
                return Accepted((ctx, goal, alphabet[term.symbol].source_id)) if alphabet[term.symbol].source_id == "source.proof" else Deferred()
            result = AgreementSearch("same source", "same goal", alphabet, check).advance(max_pairs=50, budget=500)
            self.assertIsInstance(result, Found)
            self.assertEqual(result.proof, ("same source", "same goal", "source.proof"))

    def test_compound_proof_code_is_not_flattened(self):
        alphabet = (Symbol("source.atom", 0), Symbol("core.binary", 2))
        required = Term(1, (Term(0), Term(0)))
        search = AgreementSearch("source", "goal", alphabet,
            lambda ctx, goal, alphabet, term, effort: Accepted(term) if term == required else Rejected("not this proof"))
        result = search.advance(max_pairs=300, budget=3000)
        self.assertIsInstance(result, Found)
        self.assertEqual(result.code, (1, 0, 0))
        self.assertEqual(result.proof, required)

    def test_source_goal_and_alphabet_cannot_be_reassigned(self):
        search = AgreementSearch("source", "goal", (Symbol("proof", 0),), lambda *_: Deferred())
        for field, value in (("context", "different source"), ("goal", "easier goal"),
                             ("alphabet", (Symbol("other", 0),)), ("checker", lambda *_: Accepted("fake"))):
            with self.assertRaises(AttributeError):
                setattr(search, field, value)

    def test_invalid_api_inputs(self):
        with self.assertRaises(ValueError):
            Symbol("", 0)
        with self.assertRaises(ValueError):
            Symbol("bad", -1)
        for index, size in ((-1, 2), (0, 0)):
            with self.assertRaises(ValueError):
                code_at(index, size)
        with self.assertRaises(ValueError):
            AgreementSearch("source", "goal", (), lambda *_: Deferred())
        with self.assertRaises(ValueError):
            AgreementSearch("source", "goal", (Symbol("same", 0), Symbol("same", 1)), lambda *_: Deferred())
        search = AgreementSearch("source", "goal", (Symbol("ok", 0),), lambda *_: Deferred())
        with self.assertRaises(ValueError):
            search.advance(max_pairs=-1, budget=1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
