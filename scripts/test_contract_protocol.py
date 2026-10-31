"""Engineering checks for the public port reference implementation, not CAS answers.

Usage: python3 scripts/test_contract_protocol.py /path/to/contracts/python/cas_port.py
Discovery uses CAS_LEAF_CONTRACT_PATH or the checkout selected in lake-manifest.json.
"""

import importlib.util
import io
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch


def helper_path():
    # A unittest discovery argument is not a contract path. Direct invocation
    # retains its explicit source selection; discovery uses the built tuple.
    if __name__ == "__main__" and len(sys.argv) > 1 and not sys.argv[1].startswith("-"):
        return Path(sys.argv.pop(1))
    if selected := os.environ.get("CAS_LEAF_CONTRACT_PATH"):
        return Path(selected) / "python" / "cas_port.py"
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    entry = next(row for row in manifest["packages"] if row["name"] == "cas_leaf_contracts")
    if entry["type"] == "path":
        directory = root / entry["dir"]
    else:
        directory = root / manifest.get("packagesDir", ".lake/packages") / entry["name"]
        directory /= entry.get("subDir") or ""
    return directory / "python" / "cas_port.py"


contract_path = helper_path().resolve(strict=True)
spec = importlib.util.spec_from_file_location("cas_contract_port_under_test", contract_path)
port = importlib.util.module_from_spec(spec)
spec.loader.exec_module(port)


def frame(value):
    payload = json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return str(len(payload)).encode("ascii") + b"\n" + payload


def node(tag, *arguments):
    return {"ctor": tag, "args": list(arguments)}


class ContractProtocol(unittest.TestCase):
    def read(self, data):
        with patch.object(port.sys, "stdin", SimpleNamespace(buffer=io.BytesIO(data))):
            return port.read_frame()

    def test_frames_count_bytes_and_reject_bad_headers(self):
        value = {"op": "probe", "args": "ℤ → ℚ"}
        self.assertEqual(self.read(frame(value)), value)
        self.assertIsNone(self.read(b""))
        for header in (b"", b"-1", b"+1", b" 1", b"1 ", b"1.0", "١".encode()):
            with self.subTest(header=header), self.assertRaises(ValueError):
                self.read(header + b"\n0")
        for truncated in (b"1", b"3\n{}"):
            with self.subTest(truncated=truncated), self.assertRaises(EOFError):
                self.read(truncated)

    def test_serve_preserves_every_supplied_argument(self):
        arguments = (0, False, [], {}, None, "")
        requests = [
            {"request_id": index, "op": "probe", "args": value}
            for index, value in enumerate(arguments)
        ]
        requests += [
            {"request_id": 6, "op": "probe"},
            {"request_id": 7, "op": "unregistered", "args": {}},
        ]
        supplied, received = io.BytesIO(b"".join(map(frame, requests))), io.BytesIO()
        with patch.object(port.sys, "stdin", SimpleNamespace(buffer=supplied)), \
                patch.object(port.sys, "stdout", SimpleNamespace(buffer=received)):
            port.serve("protocol-probe", "0", "0", {"probe": lambda value: value})
        replies = []
        with patch.object(port.sys, "stdin", SimpleNamespace(buffer=io.BytesIO(received.getvalue()))):
            while (reply := port.read_frame()) is not None:
                replies.append(reply)
        self.assertEqual(replies[0]["op"], "ready")
        for index, value in enumerate(arguments):
            self.assertEqual(replies[index + 1], {"request_id": index, "status": "ok", "value": value})
            self.assertIs(type(replies[index + 1]["value"]), type(value))
        self.assertEqual(replies[7]["status"], "error")
        self.assertEqual(replies[7]["kind"], "ValueError")
        self.assertEqual(replies[8], {"request_id": 7, "status": "unsupported", "op": "unregistered"})

    def test_typed_maps_keep_both_endpoints_and_callable(self):
        source, target = node("obj.sets.fin", 2), node("obj.sets.fin", 3)
        callable_data = port.opaque_data("owned-on-original-connection")
        self.assertEqual(port.typed_map(port.map_data(source, target, callable_data)),
                         (source, target, callable_data))
        for malformed in (node("typedMap", source, target),
                          node("typedMap", source, target, callable_data, source),
                          node("map", source, target, callable_data)):
            with self.subTest(malformed=malformed), self.assertRaises(ValueError):
                port.typed_map(malformed)
        for token in ("", None, 0):
            with self.subTest(token=token), self.assertRaises(ValueError):
                port.opaque_data(token)

    def test_point_and_admission_contexts_are_complete(self):
        source, target = node("obj.sets.fin", 2), node("obj.sets.fin", 3)
        invocation = node("apply", "op.probe", [], node("opaqueData", "map"),
                          source, source, target, node("opaqueData", "point"))
        self.assertEqual(port.point_invocation(invocation, "op.probe"), tuple(invocation["args"]))
        with self.assertRaises(ValueError):
            port.point_invocation(invocation, "op.other")
        admission = node("admittedPoint", "obj.probe", [], source, source, target,
                         node("opaqueData", "original-point"))
        self.assertEqual(port.admitted_point(admission), tuple(admission["args"]))
        for reader, value in ((port.point_invocation, invocation), (port.admitted_point, admission)):
            for fields in (value["args"][:-1], value["args"] + [None]):
                with self.subTest(reader=reader.__name__, fields=fields), self.assertRaises(ValueError):
                    reader({"ctor": value["ctor"], "args": fields})

    def test_comparison_invocations_keep_direction_and_complete_endpoints(self):
        source, target = node("obj.probe.first", 3), node("obj.probe.second", 3)
        point = port.opaque_data("original-point")
        for inverse in (False, True):
            first, second = (target, source) if inverse else (source, target)
            request = node("presentationApply", [3], inverse, first, second, point)
            self.assertEqual(port.presentation_invocation(request), tuple(request["args"]))
        malformed = [
            node("presentationApply", [], False, source, target),
            node("presentationApply", [], False, source, target, point, None),
            node("presentationApply", {}, False, source, target, point),
            node("presentationApply", [], 0, source, target, point),
            node("presentationApply", [], "false", source, target, point),
            node("apply", [], False, source, target, point),
        ]
        for request in malformed:
            with self.subTest(request=request), self.assertRaises(ValueError):
                port.presentation_invocation(request)

    def test_operation_parameters_and_operands_stay_ordered(self):
        operation = node("operationExpression", "op.probe", [node("obj.probe"), 4],
                         [node("numeral", 2)])
        self.assertEqual(port.operation_expression(operation), tuple(operation["args"]))
        for parameters, operands in (({}, []), ([], {}), (None, [])):
            with self.subTest(parameters=parameters, operands=operands), self.assertRaises(ValueError):
                port.operation_expression(node("operationExpression", "op.probe", parameters, operands))

    def test_input_references_keep_request_positions_separate_from_results(self):
        first = port.input_ref(["args", 4, 0])
        second = port.input_ref(["sourceImage"])
        self.assertEqual(port.input_ref_path(first), ["args", 4, 0])
        self.assertIsNone(port.result_ref_index(first))
        self.assertIsNone(port.input_ref_path(port.result_ref(0)))
        call = port.deferred_call("fun.probe", "fun.probe#input", node("pair", first, second))
        program = port.deferred_data([call], node("pair", port.result_ref(0), second))
        self.assertEqual(port.deferred_computation(program), (program["args"][0], program["args"][1]))
        # An original input does not consume a result index or permit a forward call.
        with self.assertRaises(ValueError):
            port.deferred_data([port.deferred_call("fun.probe", "fun.probe#input",
                node("pair", first, port.result_ref(0)))], second)
        malformed = [node("inputRef"), node("inputRef", "args"),
            node("inputRef", ["args"], []), node("inputRef", ["args", -1]),
            node("inputRef", [True]), node("inputRef", [1.5]),
            node("inputRef", [None]), {**first, "owner": "copied"}]
        for value in malformed:
            with self.subTest(value=value), self.assertRaises(ValueError):
                port.deferred_data([], node("pair", second, value))

    def test_lift_fields_retain_actual_images_and_ordered_parameters(self):
        source = node("opaqueData", "selected-source")
        source_image = node("opaqueData", "actual-source-image")
        apex = node("opaqueData", "actual-lift-apex")
        comparison_image = node("opaqueData", "actual-comparison-image")
        base_object = node("opaqueData", "actual-base-apex")
        base = node("subobject", base_object, source_image, node("opaqueData", "base-inclusion"))
        outputs = [apex, port.map_data(apex, source, node("opaqueData", "inclusion")),
                   port.map_data(comparison_image, base_object, node("opaqueData", "forward")),
                   port.map_data(base_object, comparison_image, node("opaqueData", "backward"))]
        parameters = [node("obj.probe", 7), node("opaqueData", "selected-parameter")]
        for index, field in enumerate(("obj", "hom", "forward", "backward")):
            packet = node("monoLiftInput", "lift.probe", node("fun.probe"), source, base, outputs[:index])
            packet.update(parameters=parameters, sourceImage=source_image)
            if index == 3:
                packet["comparisonImage"] = comparison_image
            decoded = port.lift_input(packet, "lift.probe#" + field)
            self.assertIs(decoded[3], source)
            self.assertEqual(decoded[5], outputs[:index])
            self.assertIs(port.lift_parameters(packet), parameters)
            self.assertEqual(port.lift_images(packet),
                             (source_image, comparison_image if index == 3 else None))
            with self.assertRaises(ValueError):
                port.lift_input(packet, "lift.other#" + field)
        factor = node("liftFactorInput", "lift.probe", node("fun.probe"), source, base, outputs,
                      port.map_data(source_image, base_object, node("opaqueData", "base-map")),
                      port.map_data(source, source, node("opaqueData", "cone")))
        factor.update(parameters=parameters, sourceImage=source_image, comparisonImage=comparison_image)
        self.assertEqual(port.lift_factor_input(factor, "lift.probe#factor"), tuple(factor["args"]))
        self.assertEqual(port.lift_images(factor), (source_image, comparison_image))
        for field in ("sourceImage", "comparisonImage"):
            malformed = {key: value for key, value in factor.items() if key != field}
            with self.subTest(field=field), self.assertRaises(ValueError):
                port.lift_factor_input(malformed, "lift.probe#factor")
        for field in ("sourceImage", "comparisonImage"):
            with self.subTest(null=field), self.assertRaises(ValueError):
                port.lift_factor_input({**factor, field: None}, "lift.probe#factor")

    def test_lift_images_reject_incomplete_or_premature_contexts(self):
        original = node("arrow", node("source"), node("target"), node("map"))
        base = node("subobject", node("base"), node("image"), node("inclusion"))
        image = node("arrow", node("source-image"), node("target-image"), node("map-image"))
        request = node("liftInput", "lift.probe", node("fun.probe"), original, base, [])
        request["sourceImage"] = image
        self.assertEqual(port.lift_images(request), (image, None))
        # Legacy framing remains admitted only when the image slots are absent.
        legacy = {key: value for key, value in request.items() if key != "sourceImage"}
        self.assertEqual(port.lift_images(legacy), (None, None))
        for malformed in ({**request, "sourceImage": node("object")},
                          {**request, "comparisonImage": node("too-early")},
                          {**legacy, "comparisonImage": node("unassociated")},
                          {**request, "args": request["args"][:-1]},
                          {**request, "args": request["args"][:-1] + [[0, 1, 2, 3]]}):
            with self.subTest(malformed=malformed), self.assertRaises(ValueError):
                port.lift_images(malformed)


if __name__ == "__main__":
    unittest.main()
