"""Finite engineering model for issue #69's observation/liveness correction.

These tests are not Lean/SDK execution or independent mathematical acceptance.
The model fixes immutable references first; observations have no callback or
execution capability. Computational use checks the selected dependency closure.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from types import MappingProxyType
import unittest


@dataclass(frozen=True)
class Ref:
    key: str
    role: str


@dataclass(frozen=True)
class Node:
    role: str
    kind: str
    fields: tuple[Ref, ...] = ()
    dependencies: tuple[Ref, ...] = ()
    owners: frozenset[str] = frozenset()


@dataclass(frozen=True)
class Descriptor:
    type_text: str
    field_labels: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if type(self.type_text) is not str or type(self.field_labels) is not tuple:
            raise TypeError('descriptors contain data, not render callbacks')
        if any(type(label) is not str for label in self.field_labels):
            raise TypeError('field labels must be inert strings')


class Unavailable(Exception):
    pass


class NeedsExecution(Exception):
    pass


class View:
    """A fixed snapshot or transaction-local graph supplied explicitly by its owner."""
    def __init__(self, nodes: dict[str, Node], descriptors: dict[str, Descriptor]):
        if set(nodes) != set(descriptors):
            raise ValueError('each visible node needs its inspection descriptor')
        for node in nodes.values():
            if node.kind not in ('portable', 'record', 'owned', 'closure', 'lazy'):
                raise ValueError('unknown operational node form')
            if node.kind != 'record' and node.fields:
                raise ValueError('only locally stored records have field references')
            for ref in node.fields + node.dependencies:
                if ref.key not in nodes or nodes[ref.key].role != ref.role:
                    raise ValueError('missing reference or mismatched prepared role')
        self.nodes = MappingProxyType(dict(nodes))
        self.descriptors = MappingProxyType(dict(descriptors))

    def node(self, ref: Ref) -> Node:
        node = self.nodes.get(ref.key)
        if node is None or node.role != ref.role:
            raise Unavailable('reference is not visible at its exact prepared role')
        return node

    def inspect(self, ref: Ref) -> Descriptor:
        self.node(ref)
        return self.descriptors[ref.key]

    def locate(self, ref: Ref, path: tuple[int, ...]) -> Ref:
        """Follow stored field identities only; never force an owned/lazy object."""
        self.node(ref)
        for slot in path:
            node = self.node(ref)
            if node.kind != 'record':
                raise NeedsExecution('no stored field at this position')
            if type(slot) is not int or not 0 <= slot < len(node.fields):
                raise Unavailable('not a declared field slot')
            ref = node.fields[slot]
            self.node(ref)
        return ref

    def required_owners(self, roots: tuple[Ref, ...]) -> frozenset[str]:
        """Complete operational closure of the chosen use, including all captures."""
        work = list(roots)
        seen: set[Ref] = set()
        owners: set[str] = set()
        while work:
            ref = work.pop()
            if ref in seen:
                continue
            node = self.node(ref)
            seen.add(ref)
            owners.update(node.owners)
            work.extend(node.dependencies)
            work.extend(node.fields)
        return frozenset(owners)

    def use(self, roots: tuple[Ref, ...], live: frozenset[str]) -> tuple[Ref, ...]:
        if not self.required_owners(roots) <= live:
            raise Unavailable('required generation is unavailable before dispatch')
        return roots


class ObservationContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.p = Ref('p', 'integer')
        self.h = Ref('h', 'selected map')
        self.r = Ref('r', 'joint result')
        self.c = Ref('c', 'capturing function')
        self.nodes = {
            'p': Node(self.p.role, 'portable'),
            'h': Node(self.h.role, 'owned', owners=frozenset({'engine:1'})),
            'r': Node(self.r.role, 'record', fields=(self.p, self.h)),
            'c': Node(self.c.role, 'closure', dependencies=(self.h,)),
        }
        self.docs = {key: Descriptor(node.role) for key, node in self.nodes.items()}
        self.view = View(self.nodes, self.docs)

    def test_portable_sibling_survives_owner_loss(self):
        actual = self.view.locate(self.r, (0,))
        self.assertIs(actual, self.p)
        self.assertEqual(self.view.use((actual,), frozenset()), (self.p,))

    def test_expired_selected_field_is_not_revived(self):
        actual = self.view.locate(self.r, (1,))
        self.assertIs(actual, self.h)
        with self.assertRaises(Unavailable):
            self.view.use((actual,), frozenset({'engine:2'}))

    def test_full_aggregate_still_requires_its_owners(self):
        with self.assertRaises(Unavailable):
            self.view.use((self.r,), frozenset())
        self.assertEqual(self.view.use((self.r,), frozenset({'engine:1'})), (self.r,))

    def test_all_declared_captures_remain_required(self):
        with self.assertRaises(Unavailable):
            self.view.use((self.c,), frozenset())
        self.assertEqual(self.view.required_owners((self.c,)), frozenset({'engine:1'}))

    def test_transitive_capture_and_argument_owners(self):
        outer = Ref('outer', 'export')
        argument = Ref('arg', 'argument')
        nodes = dict(self.nodes)
        nodes['outer'] = Node(outer.role, 'owned', dependencies=(self.c,), owners=frozenset({'producer:1'}))
        nodes['arg'] = Node(argument.role, 'owned', owners=frozenset({'argument:1'}))
        view = View(nodes, {k: Descriptor(n.role) for k, n in nodes.items()})
        needed = frozenset({'engine:1', 'producer:1', 'argument:1'})
        self.assertEqual(view.required_owners((outer, argument)), needed)
        for flags in product((False, True), repeat=3):
            live = frozenset(x for x, flag in zip(sorted(needed), flags) if flag)
            if all(flags):
                self.assertEqual(view.use((outer, argument), live), (outer, argument))
            else:
                with self.assertRaises(Unavailable): view.use((outer, argument), live)

    def test_nested_local_records_do_not_force_dead_siblings(self):
        root = Ref('root', 'outer record')
        nodes = dict(self.nodes)
        nodes['root'] = Node(root.role, 'record', fields=(self.h, self.r))
        view = View(nodes, {k: Descriptor(n.role) for k, n in nodes.items()})
        self.assertEqual(view.use((view.locate(root, (1, 0)),), frozenset()), (self.p,))

    def test_lazy_or_owned_projection_is_not_an_observation(self):
        for kind in ('owned', 'lazy'):
            ref = Ref('x', 'unmaterialized')
            view = View({'x': Node(ref.role, kind, owners=frozenset({'p:1'}))}, {'x': Descriptor(ref.role)})
            with self.assertRaises(NeedsExecution): view.locate(ref, (0,))

    def test_equal_roles_do_not_merge_distinct_values(self):
        other = Ref('other', self.p.role)
        nodes = dict(self.nodes)
        nodes['other'] = Node(other.role, 'portable')
        nodes['r'] = Node(self.r.role, 'record', fields=(self.p, other))
        view = View(nodes, {k: Descriptor(n.role) for k, n in nodes.items()})
        self.assertNotEqual(view.locate(self.r, (0,)), view.locate(self.r, (1,)))

    def test_receipt_association_is_not_whole_reply_liveness(self):
        # A previously admitted joint completion retains both actual output roots.
        receipt_roots = (self.p, self.h)
        self.assertEqual(self.view.use((receipt_roots[0],), frozenset()), (self.p,))
        with self.assertRaises(Unavailable): self.view.use((receipt_roots[1],), frozenset())
        self.assertEqual(receipt_roots, (self.p, self.h))

    def test_old_snapshot_cannot_find_new_values(self):
        old = View({'p': self.nodes['p']}, {'p': self.docs['p']})
        with self.assertRaises(Unavailable): old.locate(self.r, (0,))
        with self.assertRaises(Unavailable): old.use((self.h,), frozenset({'engine:1'}))

    def test_wrong_role_and_undeclared_field_are_rejected(self):
        with self.assertRaises(Unavailable): self.view.node(Ref('p', 'another meaning'))
        for path in ((2,), (-1,), (True,)):
            with self.assertRaises(Unavailable): self.view.locate(self.r, path)

    def test_inert_inspection_cannot_reach_registered_callbacks(self):
        effects = []
        def extension_printer():
            effects.append('owner closed')
            return 'pretty type'
        # This is the unsafe architectural path, modeled as an ordinary callback.
        self.assertEqual(extension_printer(), 'pretty type')
        self.assertEqual(effects, ['owner closed'])
        effects.clear()
        for _ in range(5):
            self.assertEqual(self.view.inspect(self.h), self.docs['h'])
        self.assertEqual(effects, [])

    def test_descriptors_cannot_hide_deferred_rendering(self):
        with self.assertRaises(TypeError): Descriptor(lambda: 'executed later')
        with self.assertRaises(TypeError): Descriptor('type', (lambda: 'field',))

    def test_snapshot_is_not_mutated_by_later_input_changes(self):
        self.nodes.clear()
        self.docs['p'] = Descriptor('changed')
        self.assertEqual(self.view.inspect(self.p).type_text, 'integer')
        self.assertEqual(self.view.locate(self.r, (0,)), self.p)

    def test_missing_descriptor_cannot_publish_partial_query_view(self):
        with self.assertRaises(ValueError): View(self.nodes, {'p': self.docs['p']})

    def test_inspection_of_expired_value_does_not_claim_live_execution(self):
        self.assertEqual(self.view.inspect(self.h).type_text, self.h.role)
        with self.assertRaises(Unavailable): self.view.use((self.h,), frozenset())


if __name__ == '__main__':
    unittest.main(verbosity=2)
