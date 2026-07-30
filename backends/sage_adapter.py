"""Python half of the direct Sage adapter (DESIGN.md, "The port and the Sage adapter").

Runs under `sage -python`: the parent spawns it with piped stdin/stdout and an
inherited stderr. stdout carries only frames (ASCII byte length, `\\n`, that many
bytes of UTF-8 JSON); stderr is the log stream.

The adapter builds native Sage parents and elements from typed requests and
returns typed values. It never receives generated Sage source and never proxies
another CAS. Factorization unit/order conventions are Sage's own and are passed
through unchanged (DESIGN.md decision 7).
"""

import json
import sys

try:
    from sage.all import Integer, Matrix, PolynomialRing, QQ, ZZ, factor, gcd
    from sage.version import version as SAGE_VERSION
except ImportError as exc:  # running outside `sage -python` is a wiring bug
    sys.stderr.write(
        "sage_adapter: SageMath is not importable (%s). This adapter must be run "
        "as `sage -python backends/sage_adapter.py`.\n" % exc
    )
    sys.exit(1)

ADAPTER_VERSION = "0.1.0"
PROTOCOL = 1


class BackendError(Exception):
    """A per-request failure with a backend-owned error kind."""

    def __init__(self, kind, message):
        super().__init__(message)
        self.kind = kind
        self.message = message


# --- framing ---------------------------------------------------------------


def _read_exact(n):
    buf = b""
    while len(buf) < n:
        chunk = sys.stdin.buffer.read(n - len(buf))
        if not chunk:
            raise EOFError("EOF mid-frame (wanted %d bytes, got %d)" % (n, len(buf)))
        buf += chunk
    return buf


def read_frame():
    """One frame, or None on clean EOF at a frame boundary."""
    line = b""
    while True:
        ch = sys.stdin.buffer.read(1)
        if not ch:
            if line:
                raise EOFError("EOF inside frame length %r" % line)
            return None
        if ch == b"\n":
            break
        line += ch
    return json.loads(_read_exact(int(line)).decode("utf-8"))


def write_frame(obj):
    payload = json.dumps(obj, separators=(",", ":")).encode("utf-8")
    sys.stdout.buffer.write(str(len(payload)).encode("ascii") + b"\n" + payload)
    sys.stdout.buffer.flush()


# --- typed values ----------------------------------------------------------

RAT_DOM = {"d": "rat"}
INT_DOM = {"d": "int"}
POLY_RAT_DOM = {"d": "poly", "coeff": RAT_DOM}
POLY_INT_DOM = {"d": "poly", "coeff": INT_DOM}


def enc_int(z):
    return {"t": "int", "v": str(Integer(z))}


def enc_rat(q):
    q = QQ(q)
    return {"t": "rat", "num": str(q.numerator()), "den": str(q.denominator())}


def dec_rat(j):
    if not isinstance(j, dict) or j.get("t") != "rat":
        raise BackendError("bad_request", "expected a rational value, got %r" % (j,))
    den = Integer(j["den"])
    if den <= 0:
        raise BackendError("bad_request", "rational denominator must be positive")
    return QQ((Integer(j["num"]), den))


def dec_int(j):
    if not isinstance(j, dict) or j.get("t") != "int":
        raise BackendError("bad_request", "expected an integer value, got %r" % (j,))
    return Integer(j["v"])


def dec_rows(j):
    if not isinstance(j, list) or not j:
        raise BackendError("bad_request", "expected a non-empty list of rows")
    return [[dec_rat(x) for x in row] for row in j]


def enc_poly_q(f):
    return {"t": "poly", "coeff": RAT_DOM, "coeffs": [enc_rat(c) for c in f.list()]}


def enc_poly_z(f):
    return {"t": "poly", "coeff": INT_DOM, "coeffs": [enc_int(c) for c in f.list()]}


# --- operations ------------------------------------------------------------


def op_factor_int(args):
    fac = factor(Integer(args["n"]))
    return {
        "t": "factorization",
        "unit": enc_int(fac.unit()),
        "factors": [[enc_int(p), int(m)] for p, m in fac],
        "dom": INT_DOM,
    }


def op_factor_poly_q(args):
    ring = PolynomialRing(QQ, "x")
    fac = ring([dec_rat(c) for c in args["coeffs"]]).factor()
    return {
        "t": "factorization",
        "unit": enc_rat(QQ(fac.unit())),
        "factors": [[enc_poly_q(g), int(m)] for g, m in fac],
        "dom": POLY_RAT_DOM,
    }


def op_factor_poly_z(args):
    fac = PolynomialRing(ZZ, "x")([dec_int(c) for c in args["coeffs"]]).factor()
    # over ZZ[x] the unit is ±1 and the content's prime factors appear as
    # constant polynomials among the factors; both pass through unchanged
    return {
        "t": "factorization",
        "unit": enc_int(ZZ(fac.unit())),
        "factors": [[enc_poly_z(g), int(m)] for g, m in fac],
        "dom": POLY_INT_DOM,
    }


def op_gcd_int(args):
    return enc_int(gcd(Integer(args["a"]), Integer(args["b"])))


def _roots(ring, coeffs, enc, dom):
    """The SET of roots in the polynomial's own coefficient ring.

    Sage's `roots()` returns (root, multiplicity) pairs over the base ring, so
    a polynomial with no root there — x^2 - 2 over QQ — yields the empty set.
    That is the answer, not a failure. Multiplicity is dropped: this op
    promises a set.
    """
    f = ring(coeffs)
    if f.is_zero():
        raise BackendError(
            "not_a_set", "every element is a root of the zero polynomial"
        )
    return {"t": "set", "elems": [enc(root) for root, _ in f.roots()], "dom": dom}


def op_roots_poly_z(args):
    return _roots(
        PolynomialRing(ZZ, "x"), [dec_int(c) for c in args["coeffs"]], enc_int, INT_DOM
    )


def op_roots_poly_q(args):
    return _roots(
        PolynomialRing(QQ, "x"), [dec_rat(c) for c in args["coeffs"]], enc_rat, RAT_DOM
    )


def op_mat_det_q(args):
    return enc_rat(Matrix(QQ, dec_rows(args["rows"])).det())


def op_mat_inv_q(args):
    mat = Matrix(QQ, dec_rows(args["rows"]))
    try:
        inv = mat.inverse()
    except ZeroDivisionError as exc:
        raise BackendError("not_invertible", str(exc))
    return {
        "t": "mat",
        "n": int(inv.nrows()),
        "entry": RAT_DOM,
        "rows": [[enc_rat(x) for x in row] for row in inv.rows()],
    }


OPS = {
    "factor_int": op_factor_int,
    "factor_poly_q": op_factor_poly_q,
    "factor_poly_z": op_factor_poly_z,
    "gcd_int": op_gcd_int,
    "roots_poly_z": op_roots_poly_z,
    "roots_poly_q": op_roots_poly_q,
    "mat_det_q": op_mat_det_q,
    "mat_inv_q": op_mat_inv_q,
}


def main():
    write_frame(
        {
            "op": "ready",
            "protocol": PROTOCOL,
            "backend": "sage",
            "backend_version": SAGE_VERSION,
            "adapter_version": ADAPTER_VERSION,
            "capabilities": sorted(OPS),
        }
    )
    while True:
        try:
            frame = read_frame()
        except Exception as exc:  # stream state is unrecoverable
            sys.stderr.write("sage_adapter: bad frame: %s\n" % exc)
            sys.exit(1)
        if frame is None:
            sys.exit(0)
        rid = frame.get("request_id")
        op = frame.get("op")
        if op not in OPS:
            write_frame({"request_id": rid, "status": "unsupported", "op": op})
            continue
        try:
            write_frame(
                {"request_id": rid, "status": "ok", "value": OPS[op](frame.get("args") or {})}
            )
        except BackendError as exc:
            write_frame(
                {
                    "request_id": rid,
                    "status": "error",
                    "kind": exc.kind,
                    "message": exc.message,
                }
            )
        except Exception as exc:
            write_frame(
                {
                    "request_id": rid,
                    "status": "error",
                    "kind": type(exc).__name__,
                    "message": str(exc),
                }
            )


if __name__ == "__main__":
    main()
