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
    from sage.all import (AA, Integer, Matrix, PolynomialRing, QQ, QQbar, SR,
                          ZZ, companion_matrix, factor, factorial, gcd,
                          integrate, limit, oo, pi, sin, var)
    from sage.version import version as SAGE_VERSION
except ImportError as exc:  # running outside `sage -python` is a wiring bug
    sys.stderr.write(
        "sage_adapter: SageMath is not importable (%s). This adapter must be run "
        "as `sage -python backends/sage_adapter.py`.\n" % exc
    )
    sys.exit(1)

ADAPTER_VERSION = "0.1.0"
PROTOCOL = 1

# Where a decimal presentation stops being one worth materializing. A loud
# ceiling like the caller's own caps, not a fallback: a tolerance past it is a
# capability refusal naming what was asked, never a coarser answer returned as
# if it had been requested.
MAX_DIGITS = 1000


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
COMPLEX_DOM = {"d": "complex"}
POLY_RAT_DOM = {"d": "poly", "coeff": RAT_DOM}
POLY_INT_DOM = {"d": "poly", "coeff": INT_DOM}
POLY_COMPLEX_DOM = {"d": "poly", "coeff": COMPLEX_DOM}


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


def enc_alg(alpha):
    """An exact algebraic number, as the caller's `a + b*sqrt(d)`.

    QQbar elements PRINT as decimal approximations, so nothing here reads a
    printed form: the coefficients come from the element's own minimal
    polynomial, and which of the two conjugate roots it is is settled by an
    exact QQbar comparison. Degree > 2 over QQ leaves the presentation and is
    a loud refusal — never a decimal, and never the wrong conjugate.
    """
    alpha = QQbar(alpha)
    if alpha in QQ:
        return enc_rat(QQ(alpha))
    f = alpha.minpoly()
    if f.degree() != 2:
        raise BackendError(
            "not_expressible",
            "the caller presents a + b*sqrt(d) over QQ; %s has minimal polynomial "
            "%s, of degree %d" % (alpha, f, f.degree()),
        )
    # monic over QQ: x^2 + p x + q, roots (-p +/- sqrt(p^2 - 4q))/2
    p, q = QQ(f[1]), QQ(f[0])
    disc = p * p - 4 * q
    a = -p / 2
    # sqrt(n/m) = sqrt(n*m)/m, with the square part of n*m moved out front
    nm = ZZ(disc.numerator()) * ZZ(disc.denominator())
    core = nm.squarefree_part()
    b = QQ(ZZ((nm / core).sqrt())) / (2 * disc.denominator())
    for sign in (1, -1):
        if QQbar(a) + sign * QQbar(b) * QQbar(core).sqrt() == alpha:
            return {"t": "alg", "a": enc_rat(a), "b": enc_rat(sign * b), "d": str(core)}
    raise BackendError(
        "not_expressible",
        "neither conjugate root of %s is %s: the exact form was not recovered"
        % (f, alpha),
    )


def dec_alg(j):
    """An exact number from the wire: an integer, a rational, or `a + b*sqrt(d)`."""
    if not isinstance(j, dict):
        raise BackendError("bad_request", "expected an exact number, got %r" % (j,))
    tag = j.get("t")
    if tag == "int":
        return QQbar(dec_int(j))
    if tag == "rat":
        return QQbar(dec_rat(j))
    if tag == "alg":
        d = Integer(j["d"])
        return QQbar(dec_rat(j["a"])) + QQbar(dec_rat(j["b"])) * QQbar(d).sqrt()
    raise BackendError("bad_request", "expected an exact number, got %r" % (j,))


def enc_poly_q(f):
    return {"t": "poly", "coeff": RAT_DOM, "coeffs": [enc_rat(c) for c in f.list()]}


def enc_poly_c(f):
    return {"t": "poly", "coeff": COMPLEX_DOM, "coeffs": [enc_alg(c) for c in f.list()]}


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


def op_factor_poly_c(args):
    """Factor over the algebraic numbers — SPEC.md's `map p to CC[x]` then
    `q.factor()`. Over a field the factors are monic, so the unit carries the
    leading coefficient; both are Sage's own conventions, passed through.
    """
    fac = PolynomialRing(QQbar, "x")([dec_alg(c) for c in args["coeffs"]]).factor()
    return {
        "t": "factorization",
        "unit": enc_alg(fac.unit()),
        "factors": [[enc_poly_c(g), int(m)] for g, m in fac],
        "dom": POLY_COMPLEX_DOM,
    }


def op_gcd_int(args):
    return enc_int(gcd(Integer(args["a"]), Integer(args["b"])))


def op_is_prime_int(args):
    """x is prime iff (x) is a nonzero prime ideal, so (-7) is prime because
    (-7) = (7). Sage's Integer.is_prime bakes positivity into the predicate;
    |x| adapts it to the true one — the executor computes the mathematics,
    the semantics never bends to a backend."""
    return {"t": "bool", "v": bool(Integer(args["n"]).abs().is_prime())}


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


def op_roots_poly_c(args):
    """The roots in ℂ, exactly. Over QQbar a nonzero polynomial splits, so
    this is where `x^2 - 2` finally has roots — the two irrational ones.
    """
    return _roots(
        PolynomialRing(QQbar, "x"),
        [dec_alg(c) for c in args["coeffs"]],
        enc_alg,
        COMPLEX_DOM,
    )


def tol_text(q):
    """A tolerance in the caller's own spelling — `1/10^{k}` for a reciprocal
    power of ten (mirrors Value.tolText). Printing 1/10^2000 as two thousand
    literal zeros lands in published notebook output; this does not.
    """
    den = q.denominator()
    if q.numerator() == 1 and den > 1:
        digits = str(den)
        if digits == "1" + "0" * (len(digits) - 1):
            return "1/10^{%d}" % (len(digits) - 1)
    return str(q)


def op_approx_real(args):
    """The decimal presentation of an exact REAL number, to a requested
    absolute tolerance (SPEC.md's `map x to RR/O(eps)`).

    The strategy is this adapter's own business and is named nowhere in the
    caller's surface: here it is exact truncation at the k-th decimal digit,
    with k the smallest exponent for which 10^-k meets the request, computed
    through Sage's exact algebraic reals (no float ever holds the value). The
    truncation error lies in [0, 10^-k), so 10^-k is a strict bound and is
    returned as the ACHIEVED tolerance — the caller verifies both it and the
    digits against the exact value it sent.

    A tolerance past MAX_DIGITS is a capability refusal naming what was asked,
    not a silently coarser answer; a value with an imaginary part is refused
    rather than projected to its real part.
    """
    x = dec_alg(args["value"])
    eps = dec_rat(args["eps"])
    if eps <= 0:
        raise BackendError(
            "bad_request", "a tolerance must be positive, got O(%s)" % tol_text(eps)
        )
    try:
        real = AA(x)
    except (TypeError, ValueError):
        raise BackendError(
            "not_real",
            "%s is not a real number: a decimal presents no complex value here" % x,
        )
    k, achieved = 0, QQ(1)
    while achieved > eps:
        if k >= MAX_DIGITS:
            raise BackendError(
                "tolerance_not_met",
                "a tolerance of O(%s) needs more than %d decimal digits, "
                "which is past this adapter's ceiling" % (tol_text(eps), MAX_DIGITS),
            )
        k, achieved = k + 1, achieved / 10
    m = (real * 10**k).floor()
    digits = str(abs(m)).rjust(k + 1, "0")
    point = len(digits) - k
    sign = "-" if m < 0 else ""
    decimal = sign + (digits if k == 0 else digits[:point] + "." + digits[point:])
    return {
        "t": "approx",
        "exact": args["value"],
        "decimal": decimal,
        "eps": enc_rat(eps),
        "achieved": enc_rat(achieved),
    }


def op_mat_det_q(args):
    return enc_rat(Matrix(QQ, dec_rows(args["rows"])).det())


def op_mat_charpoly_q(args):
    """The characteristic polynomial over QQ — SPEC.md's `C.charpoly() = r`.

    Monic of degree n by construction; the caller CHECKS both against the
    matrix it sent, so a reply of the wrong shape fails at that boundary.
    """
    return enc_poly_q(Matrix(QQ, dec_rows(args["rows"])).charpoly())


def op_poly_companion_q(args):
    """The companion matrix of a MONIC polynomial over QQ.

    Which of Sage's four layouts is used is this adapter's own convention
    (DESIGN.md decision 7), so the caller checks the three things every layout
    shares: the size, the trace, and the determinant. The last two, because
    the zero matrix has the right trace whenever a_{d-1} is 0.
    """
    f = PolynomialRing(QQ, "x")([dec_rat(c) for c in args["coeffs"]])
    if f.degree() < 1:
        raise BackendError(
            "no_companion",
            "a companion matrix belongs to a polynomial of degree at least 1, "
            "and %s has degree %s" % (f, f.degree()),
        )
    if not f.is_monic():
        raise BackendError(
            "not_monic",
            "the companion matrix is defined for a MONIC polynomial; %s has "
            "leading coefficient %s" % (f, f.leading_coefficient()),
        )
    m = companion_matrix(f, format="right")
    return {
        "t": "mat",
        "n": int(m.nrows()),
        "entry": RAT_DOM,
        "rows": [[enc_rat(x) for x in row] for row in m.rows()],
    }


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


# --- symbolic operations ---------------------------------------------------

# Which engine answers a symbolic LIMIT is this adapter's own business, and is
# named nowhere in the caller's surface — the discipline `approx_real` set for
# its numeric strategy. Sage's default is Maxima; this adapter asks SymPy,
# which ships with Sage and needs no external process.
#
# WORTH KNOWING, because it is why the choice is not merely a preference: the
# SageMath install this was developed against has a BROKEN Maxima — both the
# ECL library interface ("Module error: Don't know how to REQUIRE MAXIMA") and
# the `/bin/maxima` binary fail — so the default algorithm cannot run there at
# all. The definite integral and the Taylor expansion below avoid Maxima by
# construction rather than by option: one is Sage's own, and the other is
# computed from the definition through Pynac.
LIMIT_ALGORITHM = "sympy"

SYM_CONSTANTS = {"e": lambda: SR(1).exp(), "pi": lambda: pi,
                 "infinity": lambda: oo}
SYM_FUNCTIONS = {"sin": sin, "exp": lambda a: a.exp()}


def dec_sym(j, v):
    """A symbolic expression from the caller's TYPED TREE.

    Never a source string: the caller sends nodes and this builds a Sage
    expression from them, so neither end can widen the language unilaterally.
    A name outside the shared vocabulary is a loud refusal here as well as
    there — the check is on BOTH sides on purpose.
    """
    if not isinstance(j, dict):
        raise BackendError("bad_request", "expected a symbolic node, got %r" % (j,))
    tag = j.get("s")
    if tag == "var":
        return v
    if tag == "num":
        return SR(dec_rat(j["q"]))
    if tag == "const":
        name = j.get("n")
        if name not in SYM_CONSTANTS:
            raise BackendError(
                "bad_request",
                "%r is not one of the named constants this adapter presents (%s)"
                % (name, ", ".join(sorted(SYM_CONSTANTS))),
            )
        return SYM_CONSTANTS[name]()
    if tag == "app":
        name = j.get("f")
        if name not in SYM_FUNCTIONS:
            raise BackendError(
                "bad_request",
                "%r is not one of the named functions this adapter presents (%s)"
                % (name, ", ".join(sorted(SYM_FUNCTIONS))),
            )
        return SYM_FUNCTIONS[name](dec_sym(j["a"], v))
    if tag == "neg":
        return -dec_sym(j["a"], v)
    binops = {
        "add": lambda a, b: a + b, "sub": lambda a, b: a - b,
        "mul": lambda a, b: a * b, "div": lambda a, b: a / b,
        "pow": lambda a, b: a ** b,
    }
    if tag in binops:
        return binops[tag](dec_sym(j["a"], v), dec_sym(j["b"], v))
    raise BackendError("bad_request", "unknown symbolic node %r" % (tag,))


def _sym_func(args):
    """The caller's function, as (variable, expression)."""
    f = args["f"]
    v = var(str(f["binder"]))
    return v, dec_sym(f["body"], v)


def _enc_exact(x, what):
    """A symbolic RESULT as one of the exact values the caller presents.

    An answer this adapter cannot place in QQbar — an infinite limit, a
    divergent integral, an expression that did not close up — is a loud
    refusal naming what came back. Returning a decimal, or the unevaluated
    expression, would be a wrong answer wearing a right shape.
    """
    try:
        return enc_alg(QQbar(x))
    except (TypeError, ValueError, NotImplementedError):
        raise BackendError(
            "not_exact",
            "%s is %s, which is not an exact value this surface presents"
            % (what, x),
        )


def op_sym_limit(args):
    """lim_{v -> point} body, by Sage's symbolic limit.

    TRUSTED on the caller's side and this is the operation that is: there is
    no finite exact computation there that could check a limit, so what the
    caller verifies is the KIND of the reply. A limit that does not exist, or
    is infinite, is a refusal here rather than a value.
    """
    v, body = _sym_func(args)
    pt = dec_sym(args["point"], v)
    try:
        result = limit(body, algorithm=LIMIT_ALGORITHM, **{str(v): pt})
    except NotImplementedError:
        # an OSCILLATING limit: SymPy answers with an accumulation bound, which
        # has no Sage conversion. That is the same fact `_enc_exact` reports —
        # the answer is not an exact value this surface presents — so it folds
        # into the same structured refusal rather than escaping raw.
        raise BackendError(
            "not_exact",
            "the limit of %s does not converge to an exact value this surface "
            "presents" % body,
        )
    return _enc_exact(result, "the limit")


def op_sym_definite_integral(args):
    v, body = _sym_func(args)
    lo = dec_sym(args["lo"], v)
    hi = dec_sym(args["hi"], v)
    try:
        result = integrate(body, v, lo, hi)
    except ValueError as exc:
        raise BackendError("divergent", str(exc))
    return _enc_exact(result, "the definite integral")


def op_sym_taylor(args):
    """The Taylor coefficients about a point, exactly.

    Computed from the DEFINITION — the n-th coefficient is f^(n)(a)/n! —
    rather than from a series routine. Symbolic differentiation and
    substitution are Pynac's, so this needs no external CAS module at all,
    and every coefficient comes back as an exact rational or as a refusal.

    The ORDER is the caller's documented ceiling, not a negotiation: a series
    is presented by finitely many coefficients, and a truncation past them is
    the caller's loud refusal rather than a shorter answer from here.
    """
    v, body = _sym_func(args)
    pt = dec_sym(args["point"], v)
    order = int(args["order"])
    coeffs = []
    for n in range(order):
        c = body.derivative(v, n).subs({v: pt}) / factorial(n)
        if c not in QQ:
            raise BackendError(
                "not_exact",
                "the coefficient of t^%d is %s, which is not a rational" % (n, c),
            )
        coeffs.append(enc_rat(QQ(c)))
    return {"t": "series", "coeff": RAT_DOM, "gen": "terms", "cs": coeffs}


OPS = {
    "factor_int": op_factor_int,
    "factor_poly_q": op_factor_poly_q,
    "factor_poly_z": op_factor_poly_z,
    "factor_poly_c": op_factor_poly_c,
    "gcd_int": op_gcd_int,
    "is_prime_int": op_is_prime_int,
    "roots_poly_z": op_roots_poly_z,
    "roots_poly_q": op_roots_poly_q,
    "roots_poly_c": op_roots_poly_c,
    "mat_det_q": op_mat_det_q,
    "mat_charpoly_q": op_mat_charpoly_q,
    "poly_companion_q": op_poly_companion_q,
    "mat_inv_q": op_mat_inv_q,
    "approx_real": op_approx_real,
    "sym_limit": op_sym_limit,
    "sym_definite_integral": op_sym_definite_integral,
    "sym_taylor": op_sym_taylor,
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
