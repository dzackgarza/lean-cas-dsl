#!/usr/bin/env python3
"""Executable spec of the Sage adapter's wire protocol.

Deliberately raw JSON: this is an independent oracle, so its frame codec must
NOT be deduplicated with the adapter's. Run it directly (`python3
tests/roundtrip.py`); it spawns `sage -python backends/sage_adapter.py` itself.

Missing `sage` is a loud failure, never a skip: a backend the routes claim is
registered but that cannot run is exactly the condition this test exists to
catch.
"""

import json
import pathlib
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ADAPTER = ROOT / "backends" / "sage_adapter.py"
OPS = ["factor_int", "factor_poly_q", "mat_det_q", "mat_inv_q"]


def read_frame(stream):
    line = b""
    while True:
        ch = stream.read(1)
        if not ch:
            raise EOFError("adapter closed stdout (length line so far: %r)" % line)
        if ch == b"\n":
            break
        line += ch
    n = int(line)
    buf = b""
    while len(buf) < n:
        chunk = stream.read(n - len(buf))
        if not chunk:
            raise EOFError("adapter closed stdout mid-frame")
        buf += chunk
    return json.loads(buf.decode("utf-8"))


def write_frame(stream, obj):
    payload = json.dumps(obj).encode("utf-8")
    stream.write(str(len(payload)).encode("ascii") + b"\n" + payload)
    stream.flush()


class Adapter:
    def __init__(self, proc):
        self.proc = proc
        self.next_id = 1

    def call(self, op, args, request_id=None):
        rid = self.next_id if request_id is None else request_id
        self.next_id = max(self.next_id, rid) + 1
        write_frame(self.proc.stdin, {"request_id": rid, "op": op, "args": args})
        reply = read_frame(self.proc.stdout)
        assert reply["request_id"] == rid, "reply echoed %r, expected %r" % (
            reply.get("request_id"),
            rid,
        )
        return reply

    def ok(self, op, args):
        reply = self.call(op, args)
        assert reply["status"] == "ok", "%s failed: %r" % (op, reply)
        return reply["value"]


def rat(j):
    assert j["t"] == "rat", "expected a rational, got %r" % (j,)
    return "%s/%s" % (j["num"], j["den"])


def int_v(j):
    assert j["t"] == "int", "expected an integer, got %r" % (j,)
    return j["v"]


def factor_dict(value, decode):
    return {decode(base): mult for base, mult in value["factors"]}


def check_ready(adapter):
    ready = read_frame(adapter.proc.stdout)
    assert ready["op"] == "ready", ready
    assert ready["protocol"] == 1, ready
    assert ready["backend"] == "sage", ready
    assert ready["backend_version"], "empty backend_version"
    assert ready["adapter_version"], "empty adapter_version"
    missing = set(OPS) - set(ready["capabilities"])
    assert not missing, "ready frame omits capabilities %s" % sorted(missing)
    print("ready: sage %s / adapter %s" % (ready["backend_version"], ready["adapter_version"]))


def check_factor_int(adapter):
    value = adapter.ok("factor_int", {"n": "360"})
    assert value["t"] == "factorization", value
    assert value["dom"] == {"d": "int"}, value
    assert int_v(value["unit"]) == "1", value["unit"]
    assert factor_dict(value, int_v) == {"2": 3, "3": 2, "5": 1}, value

    value = adapter.ok("factor_int", {"n": "-12"})
    assert int_v(value["unit"]) == "-1", value["unit"]
    assert factor_dict(value, int_v) == {"2": 2, "3": 1}, value
    print("factor_int: ok")


def check_factor_poly_q(adapter):
    # x^3 - 2x + 1, ascending coefficients
    coeffs = [["1", "1"], ["-2", "1"], ["0", "1"], ["1", "1"]]
    value = adapter.ok(
        "factor_poly_q",
        {"coeffs": [{"t": "rat", "num": n, "den": d} for n, d in coeffs]},
    )
    assert value["t"] == "factorization", value
    assert rat(value["unit"]) == "1/1", value["unit"]
    got = set()
    for base, mult in value["factors"]:
        assert base["t"] == "poly" and base["coeff"] == {"d": "rat"}, base
        got.add((tuple(rat(c) for c in base["coeffs"]), mult))
    expected = {
        (("-1/1", "1/1"), 1),
        (("-1/1", "1/1", "1/1"), 1),
    }
    assert got == expected, "got %r, expected %r" % (got, expected)
    print("factor_poly_q: ok")


def q(n, d=1):
    return {"t": "rat", "num": str(n), "den": str(d)}


def check_matrices(adapter):
    rows = [[q(1), q(2)], [q(3), q(4)]]
    assert rat(adapter.ok("mat_det_q", {"rows": rows})) == "-2/1"

    inv = adapter.ok("mat_inv_q", {"rows": rows})
    assert inv["t"] == "mat" and inv["n"] == 2 and inv["entry"] == {"d": "rat"}, inv
    got = [[rat(x) for x in row] for row in inv["rows"]]
    assert got == [["-2/1", "1/1"], ["3/2", "-1/2"]], got

    singular = adapter.call("mat_inv_q", {"rows": [[q(1), q(2)], [q(2), q(4)]]})
    assert singular["status"] == "error", singular
    assert singular["kind"] == "not_invertible", singular
    assert singular["message"], "empty error message"
    print("mat_det_q / mat_inv_q: ok")


def check_unsupported(adapter):
    reply = adapter.call("no_such_op", {}, request_id=4242)
    assert reply["status"] == "unsupported", reply
    assert reply["op"] == "no_such_op", reply
    print("unsupported op: ok")


def main():
    sage = shutil.which("sage")
    if sage is None:
        sys.exit(
            "FAIL: `sage` is not on PATH. The Sage adapter cannot be exercised; "
            "install SageMath or fix PATH (this test never skips)."
        )
    if not ADAPTER.is_file():
        sys.exit("FAIL: adapter missing at %s" % ADAPTER)

    proc = subprocess.Popen(
        [sage, "-python", str(ADAPTER)],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        cwd=str(ROOT),
    )
    adapter = Adapter(proc)
    try:
        check_ready(adapter)
        check_factor_int(adapter)
        check_factor_poly_q(adapter)
        check_matrices(adapter)
        check_unsupported(adapter)
    except BaseException:
        proc.kill()
        proc.wait()
        raise

    proc.stdin.close()
    code = proc.wait(timeout=30)
    assert code == 0, "adapter exited %r on stdin EOF, expected 0" % code
    print("clean shutdown: ok")
    print("roundtrip: all checks passed")


if __name__ == "__main__":
    main()
