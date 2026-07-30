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
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent.parent
ADAPTER = ROOT / "backends" / "sage_adapter.py"
OPS = [
    "factor_int",
    "factor_poly_q",
    "factor_poly_z",
    "factor_poly_c",
    "gcd_int",
    "is_prime_int",
    "roots_poly_z",
    "roots_poly_q",
    "roots_poly_c",
    "mat_det_q",
    "mat_inv_q",
    "mat_charpoly_q",
    "poly_companion_q",
    "approx_real",
]


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


def exact(j):
    """An exact number from the wire: a rational, or `a + b*sqrt(d)`.

    Nothing here parses a decimal, because nothing on this wire carries one:
    a QQbar element that reached the caller as a printed approximation would
    fail this decode outright.
    """
    if j["t"] == "rat":
        return rat(j)
    assert j["t"] == "alg", "expected an exact number, got %r" % (j,)
    return "%s + %s*sqrt(%s)" % (rat(j["a"]), rat(j["b"]), j["d"])


def near_sqrt(n, decimal, eps):
    """|sqrt(n) - decimal| < eps, in exact integer arithmetic.

    Squaring is what makes this an independent check: no float, and no reuse
    of the caller's own certificate. `lo < sqrt n` is `lo < 0 or lo^2 < n`,
    and `sqrt n < hi` is `hi > 0 and hi^2 > n`.
    """
    lo, hi = Fraction(decimal) - eps, Fraction(decimal) + eps
    return (lo < 0 or lo * lo < n) and hi > 0 and hi * hi > n


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


def check_factor_poly_z(adapter):
    def factors(value):
        got = set()
        for base, mult in value["factors"]:
            assert base["t"] == "poly" and base["coeff"] == {"d": "int"}, base
            got.add((tuple(int_v(c) for c in base["coeffs"]), mult))
        return got

    # x^3 - 2x + 1, ascending integer coefficients
    value = adapter.ok(
        "factor_poly_z",
        {"coeffs": [{"t": "int", "v": v} for v in ("1", "-2", "0", "1")]},
    )
    assert value["t"] == "factorization", value
    assert value["dom"] == {"d": "poly", "coeff": {"d": "int"}}, value
    assert int_v(value["unit"]) == "1", value["unit"]
    assert factors(value) == {(("-1", "1"), 1), (("-1", "1", "1"), 1)}, value

    # unit and content: -2x - 2 = (-1) * 2 * (x + 1); the content's prime
    # appears as a constant-polynomial factor, passed through unchanged
    value = adapter.ok(
        "factor_poly_z",
        {"coeffs": [{"t": "int", "v": "-2"}, {"t": "int", "v": "-2"}]},
    )
    assert int_v(value["unit"]) == "-1", value["unit"]
    assert factors(value) == {(("2",), 1), (("1", "1"), 1)}, value
    print("factor_poly_z: ok")


def check_factor_poly_c(adapter):
    # SPEC.md §Polynomials: x^3 - 2x + 1 over the algebraic numbers SPLITS,
    # into (x - 1) and the two factors whose roots are (-1 +/- sqrt 5)/2.
    # Each factor is monic, so its constant term is the negated root — and it
    # is EXACT: an approximation could not be written in this form at all.
    value = adapter.ok(
        "factor_poly_c",
        {"coeffs": [{"t": "int", "v": v} for v in ("1", "-2", "0", "1")]},
    )
    assert value["t"] == "factorization", value
    assert value["dom"] == {"d": "poly", "coeff": {"d": "complex"}}, value
    assert rat(value["unit"]) == "1/1", value["unit"]
    got = set()
    for base, mult in value["factors"]:
        assert base["t"] == "poly" and base["coeff"] == {"d": "complex"}, base
        got.add((tuple(exact(c) for c in base["coeffs"]), mult))
    expected = {
        (("-1/1", "1/1"), 1),
        (("1/2 + -1/2*sqrt(5)", "1/1"), 1),
        (("1/2 + 1/2*sqrt(5)", "1/1"), 1),
    }
    assert got == expected, "got %r, expected %r" % (got, expected)

    # …and a factor this presentation cannot carry is a LOUD refusal rather
    # than a decimal: x^5 - 1 has roots of degree 4 over QQ
    reply = adapter.call(
        "factor_poly_c",
        {"coeffs": [{"t": "int", "v": v} for v in ("-1", "0", "0", "0", "0", "1")]},
    )
    assert reply["status"] == "error", reply
    assert reply["kind"] == "not_expressible", reply
    print("factor_poly_c: ok")


def check_roots_poly_c(adapter):
    def elems(value):
        assert value["t"] == "set" and value["dom"] == {"d": "complex"}, value
        return sorted(exact(e) for e in value["elems"])

    # x^2 - 2 has NO rational root (checked above) and exactly two in C
    value = adapter.ok("roots_poly_c", {"coeffs": [q(-2), q(0), q(1)]})
    assert elems(value) == ["0/1 + -1/1*sqrt(2)", "0/1 + 1/1*sqrt(2)"], value

    # x^2 + 1: the imaginary unit and its conjugate, as a NEGATIVE radicand
    value = adapter.ok("roots_poly_c", {"coeffs": [q(1), q(0), q(1)]})
    assert elems(value) == ["0/1 + -1/1*sqrt(-1)", "0/1 + 1/1*sqrt(-1)"], value

    # an ASYMMETRIC root, so a branch flip cannot permute the expected set
    # into itself: x - (1 + 2i) has the one root 1 + 2i and not its conjugate
    value = adapter.ok(
        "roots_poly_c",
        {
            "coeffs": [
                {"t": "alg", "a": q(-1), "b": q(-2), "d": "-1"},
                {"t": "rat", "num": "1", "den": "1"},
            ]
        },
    )
    assert elems(value) == ["1/1 + 2/1*sqrt(-1)"], value

    # a surd on the way IN as well as out: (x - sqrt 2)(x + sqrt 2) = x^2 - 2
    value = adapter.ok(
        "roots_poly_c",
        {
            "coeffs": [
                {"t": "alg", "a": q(0), "b": q(-1), "d": "2"},
                {"t": "rat", "num": "1", "den": "1"},
            ]
        },
    )
    assert elems(value) == ["0/1 + 1/1*sqrt(2)"], value
    print("roots_poly_c: ok")


def q(n, d=1):
    return {"t": "rat", "num": str(n), "den": str(d)}


def check_gcd_int(adapter):
    assert int_v(adapter.ok("gcd_int", {"a": "84", "b": "30"})) == "6"
    # gcd(0, n) = n, and a negative argument does not make the gcd negative
    assert int_v(adapter.ok("gcd_int", {"a": "0", "b": "-7"})) == "7"
    print("gcd_int: ok")


def check_is_prime_int(adapter):
    def is_prime(n):
        value = adapter.ok("is_prime_int", {"n": str(n)})
        assert value["t"] == "bool", value
        return value["v"]

    assert is_prime(7) is True
    assert is_prime(8) is False
    # the boundary cases the METHOD declares (normalized primality: −7 is
    # irreducible but 7 is the normalized representative of its associate
    # class), pinned here so backend and declaration cannot drift apart
    assert is_prime(1) is False
    assert is_prime(0) is False
    assert is_prime(-7) is False
    # a magnitude no 64-bit path could carry: 2^127 − 1 is a Mersenne prime
    assert is_prime(2**127 - 1) is True
    print("is_prime_int: ok")


def check_roots(adapter):
    def elems(value, decode):
        assert value["t"] == "set", value
        return [decode(e) for e in value["elems"]]

    # x^3 - 2x + 1 over ZZ: 1 is the only root in ZZ
    value = adapter.ok(
        "roots_poly_z",
        {"coeffs": [{"t": "int", "v": v} for v in ("1", "-2", "0", "1")]},
    )
    assert value["dom"] == {"d": "int"}, value
    assert elems(value, int_v) == ["1"], value

    # x^2 - 2 over QQ: NO rational root. The empty set is the answer, and the
    # op must say so rather than failing or reaching for an extension.
    value = adapter.ok(
        "roots_poly_q",
        {"coeffs": [q(-2), q(0), q(1)]},
    )
    assert value["dom"] == {"d": "rat"}, value
    assert elems(value, rat) == [], value

    # …and a rational root of a rational polynomial IS found: 2x - 1
    value = adapter.ok("roots_poly_q", {"coeffs": [q(-1), q(2)]})
    assert elems(value, rat) == ["1/2"], value

    # every element is a root of the zero polynomial: not a set to return
    reply = adapter.call("roots_poly_z", {"coeffs": []})
    assert reply["status"] == "error", reply
    assert reply["kind"] == "not_a_set", reply
    print("roots_poly_z / roots_poly_q: ok")


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


def check_charpoly_and_companion(adapter):
    """SPEC.md's `C := r.companion_matrix()`, `C.charpoly() = r`.

    The two ops are inverse to each other on this fixture, which is what makes
    the pair checkable from outside: the companion matrix of x^3 - 2x + 1 has
    that polynomial as its characteristic polynomial, and its trace and
    determinant are the two coefficient facts SPEC.md asserts (0 and -1).
    Which of Sage's four companion LAYOUTS comes back is the adapter's own
    convention, so nothing here reads the entries positionally.
    """
    # x^2 - 3x + 2, whose charpoly is itself: an independent small case
    two_by_two = [[q(0), q(-2)], [q(1), q(3)]]
    cp = adapter.ok("mat_charpoly_q", {"rows": two_by_two})
    assert cp["t"] == "poly" and cp["coeff"] == {"d": "rat"}, cp
    assert [rat(c) for c in cp["coeffs"]] == ["2/1", "-3/1", "1/1"], cp

    # SPEC.md's own cubic, ascending: 1 - 2x + 0x^2 + x^3
    coeffs = [q(1), q(-2), q(0), q(1)]
    comp = adapter.ok("poly_companion_q", {"coeffs": coeffs})
    assert comp["t"] == "mat" and comp["n"] == 3, comp
    entries = [[Fraction(rat(x)) for x in row] for row in comp["rows"]]
    trace = sum(entries[i][i] for i in range(3))
    assert trace == 0, "companion trace is %s, expected 0" % trace
    # …and its characteristic polynomial is the polynomial it came from
    back = adapter.ok("mat_charpoly_q", {"rows": comp["rows"]})
    assert [rat(c) for c in back["coeffs"]] == ["1/1", "-2/1", "0/1", "1/1"], back
    assert rat(adapter.ok("mat_det_q", {"rows": comp["rows"]})) == "-1/1"

    # a NON-MONIC polynomial has no companion matrix, and says so
    bad = adapter.call("poly_companion_q", {"coeffs": [q(1), q(2)]})
    assert bad["status"] == "error" and bad["kind"] == "not_monic", bad
    # …nor does a constant
    flat = adapter.call("poly_companion_q", {"coeffs": [q(1)]})
    assert flat["status"] == "error" and flat["kind"] == "no_companion", flat
    print("mat_charpoly_q / poly_companion_q: ok")


def check_approx_real(adapter):
    """SPEC.md's `map sqrt 2 to RR/O(1/10^10)`, at the wire.

    The reply is a CERTIFICATE — the exact value it is of, the digits, the
    tolerance requested and the one achieved — and every part of it is checked
    here against what an independent reader can compute: 10 digits of sqrt 2,
    a bound that is a strict power of ten no larger than the request, and the
    exact value echoed unchanged.
    """
    sqrt2 = {"t": "alg", "a": q(0), "b": q(1), "d": "2"}

    value = adapter.ok("approx_real", {"value": sqrt2, "eps": q(1, 10**10)})
    assert value["t"] == "approx", value
    assert value["exact"] == sqrt2, value
    # sqrt 2 = 1.41421356237…, truncated at the tenth digit
    assert value["decimal"] == "1.4142135623", value
    assert rat(value["eps"]) == "1/%d" % 10**10, value
    assert rat(value["achieved"]) == "1/%d" % 10**10, value
    # …and the bound is a real one, checked in exact integer arithmetic here
    # rather than taken from the reply: |sqrt 2 - 1.4142135623| < 10^-10
    assert near_sqrt(2, value["decimal"], Fraction(1, 10**10)), value
    assert not near_sqrt(2, value["decimal"], Fraction(1, 10**11)), value

    # a coarse request costs a short decimal, and the bound comes back with it
    value = adapter.ok("approx_real", {"value": sqrt2, "eps": q(1, 100)})
    assert value["decimal"] == "1.41", value
    assert rat(value["achieved"]) == "1/100", value
    assert near_sqrt(2, value["decimal"], Fraction(1, 100)), value

    # a NEGATIVE value truncates downward, so the digits shown stay a true
    # lower bound and the error stays inside the same interval
    value = adapter.ok(
        "approx_real",
        {"value": {"t": "alg", "a": q(0), "b": q(-1), "d": "2"}, "eps": q(1, 1000)},
    )
    # (three digits meet 1/1000, and floor takes -1.41421… down to -1.415)
    assert value["decimal"] == "-1.415", value
    assert near_sqrt(2, str(-Fraction(value["decimal"])), Fraction(1, 1000)), value
    assert Fraction(value["decimal"]) < 0, value

    # a rational is presented exactly, and the bound is still the strict one
    value = adapter.ok("approx_real", {"value": q(1, 3), "eps": q(1, 10)})
    assert value["decimal"] == "0.3", value
    assert rat(value["achieved"]) == "1/10", value
    assert abs(Fraction(1, 3) - Fraction("0.3")) < Fraction(1, 10), value
    value = adapter.ok("approx_real", {"value": q(1, 2), "eps": q(1, 10)})
    assert value["decimal"] == "0.5", value

    # a tolerance past the adapter's ceiling is a CAPABILITY refusal that names
    # what was asked for — never a coarser answer returned as if requested
    reply = adapter.call("approx_real", {"value": sqrt2, "eps": q(1, 10**2000)})
    assert reply["status"] == "error", reply
    assert reply["kind"] == "tolerance_not_met", reply
    # …in the caller's own spelling: two thousand literal zeros would be the
    # message a notebook publishes
    assert "O(1/10^{2000})" in reply["message"], reply
    assert "0000000000" not in reply["message"], reply
    assert str(1000) in reply["message"], reply

    # …and neither a non-positive tolerance nor a complex value is answered
    reply = adapter.call("approx_real", {"value": sqrt2, "eps": q(0)})
    assert reply["status"] == "error" and reply["kind"] == "bad_request", reply
    reply = adapter.call(
        "approx_real",
        {"value": {"t": "alg", "a": q(2), "b": q(2), "d": "-1"}, "eps": q(1, 10)},
    )
    assert reply["status"] == "error" and reply["kind"] == "not_real", reply
    print("approx_real: ok")


def check_unsupported(adapter):
    reply = adapter.call("no_such_op", {}, request_id=4242)
    assert reply["status"] == "unsupported", reply
    assert reply["op"] == "no_such_op", reply
    print("unsupported op: ok")


# --- the symbolic operations -----------------------------------------------

def _sym_var(n="t"):
    return {"s": "var", "n": n}


def _sym_num(n, d=1):
    return {"s": "num", "q": {"t": "rat", "num": str(n), "den": str(d)}}


def _sym_func(body, binder="t"):
    return {"binder": binder, "body": body}


def check_sym_limit(adapter):
    """SPEC.md §Elementary calculus' two limits, exactly.

    These are the TRUSTED replies: the caller has no exact computation that
    decides a limit, so this is where the answer is actually checked against
    the mathematics. `sin(t)/t → 1` at 0 and `1/t → 0` at infinity.
    """
    v = adapter.ok("sym_limit", {
        "f": _sym_func({"s": "div", "a": {"s": "app", "f": "sin", "a": _sym_var()},
                        "b": _sym_var()}),
        "point": _sym_num(0)})
    assert rat(v) == "1/1", v
    v = adapter.ok("sym_limit", {
        "f": _sym_func({"s": "div", "a": _sym_num(1), "b": _sym_var()}),
        "point": {"s": "const", "n": "infinity"}})
    assert rat(v) == "0/1", v
    # a name outside the shared vocabulary is refused HERE too, not only at
    # the caller: the closed list is what keeps the surface backend-blind
    reply = adapter.call("sym_limit", {
        "f": _sym_func({"s": "app", "f": "arctan", "a": _sym_var()}),
        "point": _sym_num(0)})
    assert reply["status"] == "error", reply
    assert "arctan" in reply["message"], reply
    # an OSCILLATING limit is the structured refusal its siblings get, not a
    # raw NotImplementedError from the conversion: sin(t) at infinity has no
    # exact value, and saying so is the answer
    reply = adapter.call("sym_limit", {
        "f": _sym_func({"s": "app", "f": "sin", "a": _sym_var()}),
        "point": {"s": "const", "n": "infinity"}})
    assert reply["status"] == "error", reply
    assert reply["kind"] == "not_exact", reply
    assert "does not converge" in reply["message"], reply
    print("sym_limit: ok")


def check_sym_definite_integral(adapter):
    """SPEC.md's `∫₀¹ t² dt = 1/3` and `∫₀^π sin(t) dt = 2`."""
    v = adapter.ok("sym_definite_integral", {
        "f": _sym_func({"s": "pow", "a": _sym_var(), "b": _sym_num(2)}),
        "lo": _sym_num(0), "hi": _sym_num(1)})
    assert rat(v) == "1/3", v
    v = adapter.ok("sym_definite_integral", {
        "f": _sym_func({"s": "app", "f": "sin", "a": _sym_var()}),
        "lo": _sym_num(0), "hi": {"s": "const", "n": "pi"}})
    assert rat(v) == "2/1", v
    print("sym_definite_integral: ok")


def check_sym_taylor(adapter):
    """SPEC.md's two expansions: e^t and sin(t) about 0, exactly.

    The coefficients are RATIONALS — 1/n! and the alternating odd ones — and
    a coefficient that is not one is a refusal rather than a decimal.
    """
    v = adapter.ok("sym_taylor", {
        "f": _sym_func({"s": "pow", "a": {"s": "const", "n": "e"}, "b": _sym_var()}),
        "point": _sym_num(0), "order": 6})
    assert v["gen"] == "terms", v
    got = [(c["num"], c["den"]) for c in v["cs"]]
    assert got == [("1", "1"), ("1", "1"), ("1", "2"), ("1", "6"),
                   ("1", "24"), ("1", "120")], got
    v = adapter.ok("sym_taylor", {
        "f": _sym_func({"s": "app", "f": "sin", "a": _sym_var()}),
        "point": _sym_num(0), "order": 8})
    got = [(c["num"], c["den"]) for c in v["cs"]]
    assert got == [("0", "1"), ("1", "1"), ("0", "1"), ("-1", "6"),
                   ("0", "1"), ("1", "120"), ("0", "1"), ("-1", "5040")], got
    print("sym_taylor: ok")


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
        check_factor_poly_z(adapter)
        check_factor_poly_c(adapter)
        check_roots_poly_c(adapter)
        check_gcd_int(adapter)
        check_is_prime_int(adapter)
        check_roots(adapter)
        check_matrices(adapter)
        check_charpoly_and_companion(adapter)
        check_approx_real(adapter)
        check_sym_limit(adapter)
        check_sym_definite_integral(adapter)
        check_sym_taylor(adapter)
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
