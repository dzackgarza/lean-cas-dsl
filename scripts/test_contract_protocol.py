"""Engineering checks for the public port reference implementation, not CAS answers.

Usage: python3 scripts/test_contract_protocol.py /path/to/contracts/python/cas_port.py
"""

import importlib.util
import io
import json
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch


contract_path = Path(sys.argv.pop(1)).resolve(strict=True)
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


if __name__ == "__main__":
    unittest.main()
