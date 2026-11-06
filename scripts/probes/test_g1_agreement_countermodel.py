"""Checks of the G1 countermodel; not evidence of a total agreement solver."""
import itertools
import unittest

from g1_agreement_countermodel import (
    DifferenceWitness, Instruction, Machine, SelectedRoute, Tower, Undetermined,
    accepts_first_hit, all_binary_maps, halt_after, inspect_prefix,
    loop_forever, machine_tower, preserves_base_points,
)


class CountermodelTests(unittest.TestCase):
    def test_exact_first_hit_language(self):
        for length in range(9):
            for word in itertools.product(("enter", "tail", "head"), repeat=length):
                expected = length >= 2 and word[0] == "enter" and word[-1] == "head" and all(x == "tail" for x in word[1:-1])
                with self.subTest(word=word):
                    self.assertEqual(accepts_first_hit(word), expected)

    def test_every_selected_route_is_retained(self):
        for n in range(100):
            self.assertTrue(accepts_first_hit(SelectedRoute(n).labels))
            self.assertEqual(SelectedRoute(n).labels.count("tail"), n)
        self.assertNotEqual(SelectedRoute(1), SelectedRoute(2))

    def test_halting_boundary_and_whole_families(self):
        for halt in range(65):
            machine = halt_after(halt)
            for n in range(67):
                with self.subTest(halt=halt, n=n):
                    expected = int(n >= halt + 1)
                    self.assertEqual(machine.marked_bit(n), expected)
                    self.assertEqual(SelectedRoute(n).whole_family(machine), (expected,))

    def test_no_finite_prefix_proves_agreement(self):
        for bound in range(65):
            machine = halt_after(bound + 1)
            self.assertIsInstance(inspect_prefix(machine, bound), Undetermined)
            witness = inspect_prefix(machine, bound + 2)
            self.assertIsInstance(witness, DifferenceWitness)
            self.assertEqual(witness.left_family, (0,))
            self.assertEqual(witness.right_family, (1,))

    def test_nonhalting_prefix_is_not_mislabelled(self):
        machine = loop_forever()
        for n in range(100):
            self.assertEqual(machine.marked_bit(n), 0)
        self.assertEqual(inspect_prefix(machine, 100), Undetermined(100))

    def test_forgetting_retains_carrier_and_base_points(self):
        for n in range(20):
            tower = machine_tower(halt_after(7))
            for _ in range(n):
                tower = tower.tail()
            self.assertEqual(tower.head(), ((0, 1), 0, 1, int(n >= 8)))
            for k in range(20):
                self.assertEqual(tower.points(k), int(k + n >= 8))

    def test_one_object_source_has_only_identity_endomorphism(self):
        # Exhaust every Bool -> Bool function. Preserving both fixed points
        # forces the identity, independently of the selected infinite sequence.
        self.assertEqual([f for f in all_binary_maps() if preserves_base_points(f)], [(0, 1)])

    def test_forgetful_actions_on_maps_are_unchanged(self):
        # For each map X -> Y and point choices, preserving all named source
        # points entails preserving every point retained by either reduct.
        domain = (0, 1)
        codomain = (0, 1, 2)
        for f in itertools.product(codomain, repeat=2):
            for a, b, p, q in itertools.product(domain, repeat=4):
                source = Tower(domain, a, b, lambda n, p=p, q=q: (p, q)[n % 2])
                target = Tower(codomain, f[a], f[b], lambda n, source=source, f=f: f[source.points(n)])
                for n in range(8):
                    self.assertEqual(f[source.tail().points(n)], target.tail().points(n))
                self.assertEqual(f[source.head()[3]], target.head()[3])

    def test_all_small_transition_tables_against_independent_stepper(self):
        # Two states and a binary tape: 2*2=4 keys. For each key choose
        # halt, stay-in-0, move-to-1, or stay-in-1. All 4^4 tables are used.
        options = (None, Instruction(0, 0, 0), Instruction(1, 1, 1), Instruction(1, 0, -1))
        keys = tuple(itertools.product(range(2), range(2)))
        for choices in itertools.product(options, repeat=4):
            rows = tuple((q, a, ins) for (q, a), ins in zip(keys, choices) if ins is not None)
            machine = Machine(rows)
            table = {(q, a): ins for q, a, ins in rows}
            state = head = 0
            tape = {}
            halted = False
            for bound in range(13):
                ins = table.get((state, tape.get(head, 0)))
                halted = halted or ins is None
                self.assertEqual(machine.halts_within(bound), halted)
                if not halted:
                    tape[head] = ins.write
                    state = ins.next_state
                    head += ins.move

    def test_invalid_data_rejected(self):
        with self.assertRaises(ValueError):
            SelectedRoute(-1)
        with self.assertRaises(ValueError):
            Instruction(0, 3, 0)
        with self.assertRaises(ValueError):
            Machine(((0, 0, Instruction(0, 0, 0)), (0, 0, Instruction(0, 0, 0))))
        with self.assertRaises(ValueError):
            loop_forever().halts_within(-1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
