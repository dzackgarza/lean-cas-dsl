"""Generated category SDK controls on real public metadata and framed sessions.

Usage: python scripts/test_category_interfaces.py CONTRACT_ROOT EXPORTED_API_JSON
These are interface/ownership controls, not mathematical backend acceptance.
"""

from __future__ import annotations

import json
import importlib.util
import os
from pathlib import Path
import sys
import unittest

if __name__ == "__main__":
    os.environ["CAS_LEAF_CONTRACT_PATH"] = str(Path(sys.argv.pop(1)).resolve(strict=True))
    os.environ["CAS_DECLARED_API_PATH"] = str(Path(sys.argv.pop(1)).resolve(strict=True))

from test_protocol_v2 import CONTRACTS, ROOT, Peer, scope_ref

sys.path.insert(0, str(CONTRACTS / "python"))
import cas_port
import cas_session

API_PATH = Path(os.environ.get("CAS_DECLARED_API_PATH",
                              str(CONTRACTS / "api" / "declared-ports.json")))


class ExportAdmissionBoundary(unittest.TestCase):
    def test_missing_admission_cannot_publish(self):
        spec = importlib.util.spec_from_file_location("export_api", CONTRACTS / "tools" / "export_api.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        with self.assertRaisesRegex(RuntimeError, "cell.example#component"):
            module.validate_addresses({"operations": [], "inputForms": [],
                "missingAdmissions": [{"operation": "cell.example#component",
                                       "reason": "no current kernel admission"}]})

    def test_dependent_input_requires_its_complete_native_context(self):
        spec = importlib.util.spec_from_file_location("export_api", CONTRACTS / "tools" / "export_api.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        form = {"input": "construction#input", "category": None,
                "categoryExpression": None}
        document = {"operations": [], "inputForms": [form]}
        with self.assertRaisesRegex(RuntimeError, "complete category context"):
            module.validate_addresses(document)
        form["nativeContext"] = {"declaration": "source.declaration",
            "universeParameters": [], "signature": "Type",
            "nativeType": {"roots": [0], "nodes": [{"sort": {"level": {"zero": {}}}}]}}
        module.validate_addresses(document)
        form["nativeContext"]["nativeType"]["roots"] = [1]
        with self.assertRaisesRegex(RuntimeError, "complete category context"):
            module.validate_addresses(document)

    def test_shared_input_keeps_all_native_contexts(self):
        spec = importlib.util.spec_from_file_location("export_api", CONTRACTS / "tools" / "export_api.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        contexts = [{"declaration": name, "universeParameters": [], "signature": "Type",
                     "nativeType": {"roots": [0], "nodes": [{"sort": {"level": {"zero": {}}}}]}}
                    for name in ("source.computation", "source.evidence")]
        form = {"input": "lift#input", "category": None, "categoryExpression": None,
                "nativeContext": None, "nativeContexts": contexts}
        document = {"operations": [], "inputForms": [form]}
        module.validate_addresses(document)
        contexts[1]["nativeType"]["roots"] = [1]
        with self.assertRaisesRegex(RuntimeError, "complete category context"):
            module.validate_addresses(document)
        form["categoryExpression"] = "selected.complete.category"
        with self.assertRaisesRegex(RuntimeError, "complete category context"):
            module.validate_addresses(document)


class CategoryInterfaces(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.document = json.loads(API_PATH.read_text(encoding="utf-8"))
        cls.api = cas_port.load_interfaces(cls.document)

    def test_original_dependent_family_and_complete_constructor_arguments(self):
        groups = self.api.category("cat.groups")
        trivial = groups.family("morphism", "mor.groups.trivial")
        signature = next(item for item in trivial.signatures
                         if item["declaration"] == "CasCatalogue.Algebra.FiniteGroups.trivial")
        parameters = [item for item in signature["parameters"] if item["explicit"]]
        # The independent declaration is `trivial (G H : GrpCat.{0}) : G ⟶ H`.
        # Both chosen groups are inputs even though the native body is constant.
        self.assertEqual([(item["name"], item["type"], item["proof"])
                          for item in parameters],
                         [("G", "GrpCat.{0}", False), ("H", "GrpCat.{0}", False)])
        self.assertEqual(signature["universeParameters"], [])
        symmetric = groups.family("object", "obj.groups.symmetric")
        source, target = symmetric.construct([3]), symmetric.construct([4])
        ordered = [source, target]
        selected = trivial.construct(ordered)
        self.assertEqual(selected, {"ctor": trivial.id, "args": [source, target]})
        source["args"][0] = 9
        self.assertEqual(selected["args"][0]["args"], [3])
        with self.assertRaises(KeyError):
            groups.family("object", "obj.sets.polynomials")
        with self.assertRaises(KeyError):
            self.api.category("Groups")

    def test_complete_registered_requests_keep_native_contexts(self):
        forms = {form["input"]: form for form in self.document["inputForms"]}
        entries = {(entry["kind"], entry["id"]): entry
                   for entry in self.document["entries"]}
        for kind, identifier, input_form in (
                ("binder", "bind.sets.finite_sum", "bind.sets.finite_sum"),
                ("binder", "bind.sets.finite_product", "bind.sets.finite_product"),
                ("morphism", "mor.groups.trivial", "mor.groups.trivial"),
                ("limit", "lim.sets.product", "cat.sets")):
            with self.subTest(kind=kind, identifier=identifier):
                declaration = entries[kind, identifier]["declarations"][0]["declaration"]
                contexts = forms[input_form]["nativeContexts"]
                original = next(item for item in contexts
                                if item["declaration"] == declaration)
                self.assertTrue(original["signature"])
                self.assertIsInstance(original["universeParameters"], list)
                self.assertEqual(len(original["nativeType"]["roots"]), 1)
                self.assertTrue(original["nativeType"]["nodes"])
                self.assertIn(identifier, {row["operation"]
                                           for row in self.document["operations"]})

    def test_universal_family_keeps_actual_earlier_cone_and_complete_native_record(self):
        sets = self.api.category("cat.sets")
        for identifier, projection, callable_field in (
                ("lim.sets.product", "CategoryTheory.Limits.LimitCone.isLimit",
                 "CategoryTheory.Limits.IsLimit.lift"),
                ("colim.sets.coproduct", "CategoryTheory.Limits.ColimitCocone.isColimit",
                 "CategoryTheory.Limits.IsColimit.desc")):
            with self.subTest(identifier=identifier):
                family = sets.family("limit", identifier)
                detail, = family.details
                universal = detail["universal"]
                address = identifier + "#" + projection.rsplit(".", 1)[1]
                self.assertEqual(universal["operation"], address)
                self.assertEqual(universal["input"], address + "#input")
                self.assertEqual(universal["path"], [projection])
                self.assertIn(identifier, family.operations)
                self.assertIn(address, family.operations)
                cone, = universal["precedingFields"]
                self.assertFalse(cone["proof"])
                self.assertEqual(cone["sourceIndex"], 0)
                self.assertTrue(cone["type"])
                field = next(field for field in universal["fields"]
                             if field["projection"] == callable_field)
                self.assertFalse(field["proof"])
                self.assertEqual(field["path"], [projection, callable_field])
                self.assertEqual(field["operation"], address)
                self.assertEqual(field["wireIndex"], 0)
                self.assertTrue(any(field["proof"] for field in universal["fields"]))
                for suffix in ("#leg", "#apex", "#map"):
                    self.assertNotIn(identifier + suffix, family.operations)

    def test_creation_publishes_whole_record_with_unchanged_raw_target_inputs(self):
        details = next(row for row in self.document["lifts"]
                       if row["id"] == "lift.finite_sets.pullbacks")
        creation = details["creation"]
        self.assertEqual(creation["operation"], details["id"])
        self.assertEqual(creation["input"], details["id"] + "#input")
        self.assertEqual(len(creation["inputs"]), 2)
        self.assertTrue(all(not field["proof"] for field in creation["inputs"]))
        self.assertIn("CategoryTheory.Limits.Cone", creation["inputs"][0]["type"])
        self.assertIn("CategoryTheory.Limits.IsLimit", creation["inputs"][1]["type"])
        self.assertTrue(creation["selectedContext"])
        fields = []
        pending = list(creation["fields"])
        while pending:
            field = pending.pop(0)
            fields.append(field)
            pending.extend(field.get("fields", []))
        for suffix in ("liftedCone", "validLift", "makesLimit"):
            selected = [field for field in fields
                        if field["projection"].rsplit(".", 1)[1] == suffix]
            self.assertTrue(selected, suffix)
            self.assertTrue(all(not field["proof"] for field in selected))
        self.assertTrue(all("operation" not in field for field in fields))
        operations = {row["operation"] for row in self.document["operations"]}
        self.assertIn(details["id"], operations)
        for suffix in ("#creation", "#liftedCone", "#validLift", "#makesLimit", "#leg", "#apex"):
            self.assertNotIn(details["id"] + suffix, operations)
        forms = {row["input"] for row in self.document["inputForms"]}
        self.assertIn(details["id"] + "#input", forms)
        datatypes = {row["declaration"]: row for row in self.document["datatypes"]}
        result = datatypes["CategoryTheory.LiftsToLimit"]
        native_fields = result["constructors"][0]["fields"]
        self.assertTrue(any(field["name"] == "makesLimit" and not field["proof"]
                            for field in native_fields))

    def test_category_constructors_are_separate_from_object_constructors(self):
        groups = self.api.category("cat.groups")
        descriptor = groups.select([])
        arrow = self.api.category_constructors["ctor.arrow"]
        self.assertEqual(arrow.construct([descriptor]),
                         {"ctor": "constructedCategory", "args": ["ctor.arrow", [descriptor]]})
        with self.assertRaises(ValueError):
            arrow.construct([])
        with self.assertRaises(ValueError):
            arrow.construct([groups.family("object", "obj.groups.symmetric").construct([3])])
        with self.assertRaises(ValueError):
            groups.family("category", "cat.groups").construct([])

    def test_typed_identity_collision_and_ambiguity_rejection(self):
        crystals = self.api.category("cat.crystals")
        self.assertEqual(crystals.family("category", "cat.crystals").kind, "category")
        self.assertEqual(crystals.family("opaque", "cat.crystals").kind, "opaque")
        changed = json.loads(json.dumps(self.document))
        view = next(row for row in changed["categoryInterfaces"]
                    if any(category["id"] == "cat.crystals" for category in row["categories"]))
        original = next(row for row in view["entries"] if row["kind"] == "category")
        view["entries"].append(original)
        with self.assertRaises(ValueError):
            cas_port.load_interfaces(changed)

    def test_functor_actions_and_requests_retain_explicit_complete_input(self):
        functor = self.api.category("cat.rings").family(
            "functor", "fun.rings.multiplicative_monoid")
        operation = "fun.rings.multiplicative_monoid#map"
        input_form = "fun.rings.multiplicative_monoid#input"
        self.assertIn(operation, functor.operations)
        action = {"ctor": functor.id, "args": []}
        source = {"ctor": "obj.rings.integers", "args": []}
        target = {"ctor": "obj.rings.rationals", "args": []}
        arrow = {"ctor": "typedMap", "args": [source, target, scope_ref(3)]}
        image_source, image_target = scope_ref(5), scope_ref(6)
        packet = {"ctor": "apply", "args": [
            operation, [], {"ctor": "map", "args": [action, arrow]},
            image_source, image_source, image_target,
            {"ctor": "identity", "args": [image_source, image_source]}]}
        described = functor.call(input_form, packet, operation=operation)
        self.assertEqual(described, cas_port.deferred_call(
            operation, input_form, packet))
        self.assertEqual(cas_port.functor_map_invocation(described["args"], functor.id),
                         tuple(packet["args"]))
        packet["args"][1].append(False)
        self.assertEqual(described["args"]["args"][1], [])
        with self.assertRaises(ValueError):
            functor.call("unpublished-input", packet, operation=operation)
        with self.assertRaises(ValueError):
            functor.call("cat.rings", packet, operation="mor.groups.trivial")
        family = self.api.category("cat.sets").family("object", "obj.sets.polynomials")
        self.assertIn("obj.sets.polynomials#application", family.operations)
        self.assertEqual(cas_port.object_field(family.field("constants", [])),
                         ("obj.sets.polynomials", "constants", []))
        with self.assertRaises(ValueError):
            family.field("invented", [])

    def test_result_helpers_require_actual_scope_and_explicit_capture(self):
        family = self.api.category("cat.groups").family("morphism", "mor.groups.trivial")
        with self.assertRaises(TypeError):
            family.result(scope_ref(9))
        with self.assertRaises(ValueError):
            family.result(cas_session.Proxy())
        peer = Peer(self, command=[
            "uv", "run", "--frozen", "--project", str(CONTRACTS), "python",
            str(ROOT / "scripts" / "probes" / "protocol_v2_peer.py"),
            "--category-interface", str(API_PATH)])
        peer.negotiate()
        suspended = peer.invoke(0, "category_result", {"value": scope_ref(9)})
        self.assertEqual(suspended["status"], "suspended")
        self.assertEqual(suspended["captures"], [scope_ref(9)])
        self.assertEqual(suspended["calls"], [
            {"op": "$cas.project", "args": {"value": scope_ref(9), "field": 0}}])
        reply = peer.send({"protocol": 2, "request_id": 1, "op": "$cas.resume",
                          "scope_id": "fresh-category", "continuation": suspended["continuation"],
                          "captures": [scope_ref(0)], "results": [scope_ref(1)]})
        self.assertEqual(reply, {"request_id": 1, "status": "ok", "exports": [],
                                "value": {"original": scope_ref(0), "child": scope_ref(1)}})
        self.assertEqual(peer.invoke(2, "category_expired", {})["status"], "error")


if __name__ == "__main__":
    unittest.main()

