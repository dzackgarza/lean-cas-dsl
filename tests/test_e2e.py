"""End-to-end acceptance proof through the real Jupyter kernel protocol.

Drives the installed `casdsl` kernelspec with jupyter_client, exercising the
whole stack: ZMQ → nbdsl kernel → framed fds → Lean worker → CasDsl prelude
→ capability router → native/Sage executors. The cells and expected values
mirror notebooks/categorical-cas.ipynb (the installed-notebook boundary of
PLAN-CAS-VERTICAL-SLICE).

Run: .venv/bin/pytest tests/test_e2e.py
(after: .venv/bin/python -m nbdsl_kernel.install --project . \
    --prelude-module CasDsl.Notebook --name casdsl \
    --display-name "CasDsl (Lean 4)")
"""

from typing import Any, Iterator

import pytest
from jupyter_client.manager import start_new_kernel

Kernel = tuple[Any, Any]  # (KernelManager, BlockingKernelClient)

STARTUP = 600  # first execute waits for the worker's mathlib prelude import


@pytest.fixture(scope="module")
def kernel() -> Iterator[Kernel]:
    km, kc = start_new_kernel(kernel_name="casdsl", startup_timeout=60)
    yield km, kc
    kc.stop_channels()
    km.shutdown_kernel(now=False)


def run_cell(kc: Any, code: str,
             timeout: float = STARTUP) -> tuple[dict[str, Any], list[Any]]:
    msg_id = kc.execute(code)
    outputs = []
    while True:
        msg = kc.get_iopub_msg(timeout=timeout)
        if msg["parent_header"].get("msg_id") != msg_id:
            continue
        if (msg["msg_type"] == "status"
                and msg["content"]["execution_state"] == "idle"):
            break
        outputs.append(msg)
    while True:
        reply = kc.get_shell_msg(timeout=timeout)
        if reply["parent_header"].get("msg_id") == msg_id:
            return reply["content"], outputs


def all_text(outputs: list[Any]) -> str:
    """Every human-visible byte: streams, rich data, error tracebacks."""
    chunks = []
    for m in outputs:
        c = m["content"]
        if m["msg_type"] == "stream":
            chunks.append(c["text"])
        elif m["msg_type"] in ("display_data", "execute_result"):
            chunks.append(str(c.get("data", {})))
        elif m["msg_type"] == "error":
            chunks.append(c.get("evalue", ""))
            chunks.append("\n".join(c.get("traceback", [])))
    return "".join(chunks)


def bundles(outputs: list[Any]) -> list[dict[str, Any]]:
    """The MIME bundles a cell published — what a notebook front end renders."""
    return [m["content"]["data"] for m in outputs
            if m["msg_type"] in ("display_data", "execute_result")]


def bundle(kc: Any, code: str) -> dict[str, Any]:
    """The single MIME bundle of a successful display cell."""
    reply, outputs = run_cell(kc, code)
    assert reply["status"] == "ok", f"cell failed: {code!r}\n{all_text(outputs)}"
    bs = bundles(outputs)
    assert len(bs) == 1, f"{code!r} published {len(bs)} bundles, expected 1"
    return bs[0]


def ok(kc: Any, code: str) -> str:
    reply, outputs = run_cell(kc, code)
    text = all_text(outputs)
    assert reply["status"] == "ok", f"cell failed: {code!r}\n{text}"
    return text


def err(kc: Any, code: str) -> str:
    reply, outputs = run_cell(kc, code)
    assert reply["status"] == "error", f"cell unexpectedly ok: {code!r}"
    return all_text(outputs)


# -- 1 · trusted arithmetic and assertions --------------------------------

def test_assert_arithmetic(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert 2 + 3 = 5")
    ok(kc, "assert 2 + 3 = 0 in ℤ/5")


def test_assert_false_is_distinct_error(kernel: Kernel) -> None:
    _, kc = kernel
    text = err(kc, "assert 2 + 3 = 6")
    assert "false" in text.lower()


# -- 2 · backend-blind factorization --------------------------------------

def test_factor_integer(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let n := 360 in ℤ")
    text = ok(kc, "n.factor()")
    assert "2^3 * 3^2 * 5" in text


def test_explain_route_names_backend_in_diagnostics_only(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "#explain_route n.factor()")
    assert "sage" in text.lower()
    assert "factor" in text


def test_gcd_is_the_prefix_spelling_of_a_method(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert gcd(84, 30) = 6")          # SPEC.md writes it prefix
    text = err(kc, "assert gcd(84, 30) = 7")
    assert "false" in text.lower()
    # the prefix form IS the category method: the receiver spelling of the
    # same call resolves and routes identically
    ok(kc, "let a := 84 in ℤ")
    ok(kc, "assert a.gcd(30) = 6")
    text = ok(kc, "#explain_route a.gcd(30)")
    assert "sage" in text.lower() and "gcd" in text
    # the diagnostic explains the prefix spelling too — it is the same call,
    # rewritten by the same function `eval` dispatches on
    text = ok(kc, "#explain_route gcd(84, 30)")
    assert "sage" in text.lower() and "gcd" in text
    # …and a name that is neither a binding nor a declared method is still
    # the honest error: the prefix reading never invents an operation
    text = err(kc, "assert nosuchop(84, 30) = 6")
    assert "'nosuchop' is not bound" in text


# -- 3 · polynomials, embeddings, polynomial call -------------------------

def test_polynomial_factor_and_call(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let p(x) := x^3 - 2x + 1 in ℤ[x]")
    text = ok(kc, "p.factor()")  # routed where p lives since round three (#18)
    assert "x - 1" in text and "x^2 + x - 1" in text
    ok(kc, "let q := map p to ℚ[x]")
    text = ok(kc, "q.factor()")
    assert "x - 1" in text and "x^2 + x - 1" in text
    ok(kc, "assert q(1) = 0")


def test_the_indeterminate_and_the_polynomial_are_elements_of_the_ring(
        kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert x ∈ ℤ[x]")
    ok(kc, "assert p ∈ ℤ[x]")
    ok(kc, "assert p ∈ ℚ[x]")   # coefficient by coefficient, along ℤ ⊆ ℚ
    text = err(kc, "assert 1 / 2 ∈ ℤ[x]")
    assert "false" in text.lower()
    # NOTHING was published into the session by any of that: a bare `x` is
    # still unbound, and a name the ring was not written with is not its
    # indeterminate either
    text = err(kc, "x")
    assert "'x' is not bound" in text
    text = err(kc, "assert y ∈ ℤ[x]")
    assert "'y' is not bound" in text


def test_degree_is_one_operation_over_both_coefficient_rings(
        kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert p.deg() = 3")
    text = err(kc, "assert p.deg() = 2")
    assert "false" in text.lower()
    # SPEC.md §Differentials' ℚ[x] polynomial, in SPEC's own spelling. The
    # superscript binds tighter than implicit multiplication (#26), so `3x²`
    # is `3·(x²)`; until that was ruled this line was written `3*x²` here
    # with a comment saying so, because `3x²` bound `9x² + x + 1` silently.
    # `f(2) = 15` is SPEC's own check that tells the two apart — the wrong
    # reading gives 39.
    ok(kc, "let f := x ↦ 3x² + x + 1 in ℚ[x]")
    ok(kc, "assert f(2) = 15")
    ok(kc, "assert f.deg() = 2")
    text = err(kc, "assert f(2) = 39")
    assert "false" in text.lower()
    # both exponent spellings bind the same way, and unary minus stays OUT
    # of the implicit product
    ok(kc, "let twoXsq := x ↦ 2x^2 in ℚ[x]")
    ok(kc, "assert twoXsq(3) = 18")
    ok(kc, "let threeMinus := x ↦ 3-x in ℤ[x]")
    ok(kc, "assert threeMinus(1) = 2")


def test_the_universal_differential(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md §Differentials, verbatim. `Spec ℚ[x]` and `Schemes/ℚ` are
    # ascription TAGS: the membership is real and checked, the categorical
    # structure is deferred to CategoryGraph.
    text = ok(kc, "let X := Spec ℚ[x] in Schemes/ℚ")
    assert "Spec ℚ[x]" in text
    # the category is REGISTERED under an ASCII name (a Lean name may not
    # carry `ℚ`), and it reaches the mathematician in their own glyph — not
    # as the `Schemes/QQ` it is stored as
    text = err(kc, "let notAScheme := 3 in Schemes/ℚ")
    assert "Schemes/ℚ" in text and "Schemes/QQ" not in text
    # a bare `d` displays what the universal differential IS. It does NOT
    # name the session's `X` — a value carries no session — so it states the
    # general shape, which is what makes the display true whatever X is
    text = ok(kc, "d")
    assert "Ω¹" in text and "universal relative differential" in text
    assert "R → Ω¹_{R / k} ≅ R dx" in text
    # the two result shapes of ONE operation
    ok(kc, "assert d(f) = (6x + 1) dx")
    ok(kc, "assert (d/dx)(f) = 6x + 1")
    # a 1-form is not the polynomial that coefficients it
    text = err(kc, "assert d(f) = 6x + 1")
    assert "false" in text.lower()
    text = err(kc, "assert (d/dx)(f) = (6x + 1) dx")
    assert "false" in text.lower()
    # …and the wrong derivative
    text = err(kc, "assert (d/dx)(f) = 6x + 2")
    assert "false" in text.lower()
    # SPEC.md §Indefinite integration's kernel line
    ok(kc, "assert kernel(d/dx : ℚ[x] → ℚ[x]) = ℚ")


def test_the_differential_display(kernel: Kernel) -> None:
    _, kc = kernel
    # a 1-form typesets: the thin space is what separates a coefficient from
    # a differential in math mode
    b = bundle(kc, "d(f)")
    assert b["text/plain"] == "(6x + 1) dx"
    assert b["text/latex"] == "$$(6x + 1)\\,dx$$"
    b = bundle(kc, "X")
    assert b["text/latex"] == "$$\\mathrm{Spec}\\, \\mathbb{Q}[x]$$"


def test_the_indefinite_integral_is_a_coset(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md §Indefinite integration, verbatim. `∫ f dx` is the COMPLETE set
    # of primitives — a coset of ker(d/dx), which is what the `+ ℚ` says.
    text = ok(kc, "∫ f dx")
    assert "x^3 + (1/2)x^2 + x + ℚ" in text
    ok(kc, "assert ∫ f dx = x³ + (1/2)x² + x + ℚ")
    # the SET is what is asserted, so any representative writes the same coset
    ok(kc, "assert ∫ f dx = x³ + (1/2)x² + x + 7 + ℚ")
    text = err(kc, "assert ∫ f dx = x³ + x² + x + ℚ")
    assert "false" in text.lower()
    ok(kc, "assert |∫ f dx| = ℵ₀")
    # the comprehension picks the one primitive vanishing at 0 — solved for
    # the constant exactly, not searched
    ok(kc, "let Fs := {h ∈ ∫ f dx | h(0) = 0} in 𝒫(ℚ[x])")
    ok(kc, "assert Fs.cardinality() = 1")
    ok(kc, "let F := Fs[0] in ℚ[x]")
    ok(kc, "assert F(x) = x³ + (1/2)x² + x")
    ok(kc, "assert d(F) = f dx")
    ok(kc, "assert (d/dx)(F) = f")
    # the KERNEL is narrowed to the ones whose zero this presentation can
    # write: a coset over ℤ/5 is refused rather than mis-canonicalized
    text = err(kc, "assert ∫ f dx = x³ + ℤ/5")
    assert "ℤ/5" in text and "gap rather than a guess" in text
    # …and the CEILING is stated rather than fitted: a guard that does not
    # evaluate the binder at a point is a gap
    text = err(kc, "{h ∈ ∫ f dx | h = 0}")
    assert "EVALUATION guard" in text


def test_the_coset_typesets(kernel: Kernel) -> None:
    _, kc = kernel
    b = bundle(kc, "∫ f dx")
    assert b["text/latex"] == "$$x^{3} + (1/2)x^{2} + x + \\mathbb{Q}$$"


def test_a_limit_is_an_exact_value_or_a_named_refusal(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md §Elementary calculus, verbatim. A limit is a routed OPERATION
    # on a symbolic function expression; ℝ gains no analysis semantics from
    # it, and the ANSWER is one of the exact values this slice presents.
    ok(kc, "assert lim_{t → 0} sin(t)/t = 1")
    ok(kc, "assert lim_{t → ∞} 1/t = 0")
    # the negative: a wrong limit is FALSE, not unknown
    text = err(kc, "assert lim_{t → 0} sin(t)/t = 2")
    assert "false" in text.lower()
    text = err(kc, "assert lim_{t → ∞} 1/t = 1")
    assert "false" in text.lower()
    # …and the vocabulary is closed at the limit too
    text = err(kc, "lim_{t → 0} arctan(t)")
    assert "arctan" in text and "vocabulary" in text
    # …and an OSCILLATING limit survives `expectKind` into a cell error with
    # the adapter's own words, rather than a raw conversion failure. The
    # wire-level pin is in tests/roundtrip.py; this is the same refusal seen
    # from the surface, which is where a mathematician meets it.
    text = err(kc, "lim_{t → ∞} sin(t)")
    assert "does not converge" in text


def test_definite_integrals_are_exact(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md's own two, in both bound spellings: a superscript digit and
    # `^` against a symbolic constant
    ok(kc, "assert ∫₀¹ t² dt = 1/3")
    ok(kc, "assert ∫₀^π sin(t) dt = 2")
    text = err(kc, "assert ∫₀¹ t² dt = 1/2")
    assert "false" in text.lower()


def test_taylor_expansion_and_truncation(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md writes `t ↦ e^t`. `e` is bound to SPEC.md's own doubling map
    # earlier in this session (the collision documented above), so the
    # exponential is written with the spelling no binding can shadow. The
    # `e^t` spelling itself is pinned where the name is free.
    ok(kc, "let expf := t ↦ exp(t) in ℝ → ℝ")
    ok(kc, "let Tf := expf.taylor_expansion(0) in ℝ[[t]]")
    ok(kc, "assert Tf ∈ ℝ[[t]]")
    # the coefficients are EXACT rationals — 1/n!, never decimals
    ok(kc, "assert [t^3]Tf = 1/6")
    ok(kc, "assert [t^5]Tf = 1/120")
    text = err(kc, "assert [t^3]Tf = 1/7")
    assert "false" in text.lower()
    # the truncation is a REQUEST, and the display says how far it is known.
    # (This slice keeps ONE spelling for a rational coefficient — `(1/2)t^2`,
    # the same one `renderPolyWith` uses everywhere — where SPEC.md's own
    # §Elementary calculus writes `t²/2`. SPEC.md spells the same coefficient
    # the other way in §Indefinite integration, which is the one this surface
    # already followed.)
    text = ok(kc, "map Tf to ℝ[[t]]/(t^6)")
    assert "+ O(t^6)" in text
    for term in ["1 + t", "(1/2)t^2", "(1/6)t^3", "(1/24)t^4", "(1/120)t^5"]:
        assert term in text, text
    # SPEC.md's `t ↦ sin(t)` to t^8, in its own spelling
    ok(kc, "let g: ℝ → ℝ := t ↦ sin(t)")
    ok(kc, "let Tg := g.taylor_expansion(0) in ℝ[[t]]")
    ok(kc, "assert Tg ∈ ℝ[[t]]")
    text = ok(kc, "map Tg to ℝ[[t]]/(t^8)")
    # a negative rational coefficient is PARENTHESIZED, which is the same
    # convention the polynomial renderer already uses for one
    for term in ["t + ", "(-1/6)t^3", "(1/120)t^5", "(-1/5040)t^7", "+ O(t^8)"]:
        assert term in text, text
    # …and past the documented ceiling it REFUSES rather than shortening
    text = err(kc, "map Tg to ℝ[[t]]/(t^40)")
    assert "ceiling" in text and "12 terms" in text


def test_a_generating_series_and_its_truncation(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md §Ellipses' `∑_{n ∈ ℕ} n² tⁿ ∈ ℤ[[t]]`, whose RULE knows every
    # coefficient — which is why the bare display ends in `...` and the
    # truncation's ends in `O(t^5)`
    ok(kc, "let sq(t) = ∑_{n ∈ ℕ} n^2 t^n ∈ ℤ[[t]]")
    assert bundle(kc, "sq")["text/plain"] == "t + 4t^2 + 9t^3 + 16t^4 + ..."
    assert (bundle(kc, "map sq to ℤ[[t]] / O(t^5)")["text/plain"]
            == "t + 4t^2 + 9t^3 + 16t^4 + O(t^5)")
    ok(kc, "assert [t^2]sq = 4")
    text = err(kc, "assert [t^2]sq = 5")
    assert "false" in text.lower()
    # a truncation target written anywhere but after `map … to` is a loud
    # refusal, exactly as `ℝ/O(ε)` is
    text = err(kc, "assert sq ∈ ℤ[[t]]/(t^5)")
    assert "not a domain" in text


def test_a_binding_shadows_the_differential(kernel: Kernel) -> None:
    _, kc = kernel
    # `d` is a CONSTANT, so a `let` shadows it exactly as one shadows `i`.
    # (Bound last in this test on purpose — nothing below reads `d`.)
    ok(kc, "let d := 6 in ℤ")
    ok(kc, "assert d = 6")
    # …and with the name bound, `d/dx` is the division it always was: a
    # scalar over a 1-form, which has no common kind and says so
    text = err(kc, "d/dx")
    assert "not defined" in text


def test_roots_are_the_ones_in_the_coefficient_ring(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "p.roots()")      # x³ - 2x + 1 over ℤ; p(1) = 0
    assert "{1}" in text
    ok(kc, "assert 1 ∈ p.roots()")
    ok(kc, "assert p.roots() = {1}")
    text = err(kc, "assert 2 ∈ p.roots()")
    assert "false" in text.lower()
    # SPEC.md's q: x² - 2 has NO root in ℚ. The empty set is the answer —
    # not an error, and not a silent reach into an extension field.
    ok(kc, "let q := x ↦ x² - 2 in ℚ[x]")
    text = ok(kc, "q.roots()")
    assert "{}" in text
    ok(kc, "assert q.roots() = {}")
    text = err(kc, "assert p.roots() = {}")
    assert "false" in text.lower()


# -- 4 · exact matrix algebra ---------------------------------------------

def test_matrix_inverse_and_det(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let M := [1, 2; 3, 4] in Mat₂(ℚ)")
    text = ok(kc, "M.inverse()")
    assert "-2, 1" in text and "3/2, -1/2" in text
    ok(kc, "assert M.det() = -2")


# -- 5 · subcategory inheritance ------------------------------------------

def test_annihilator_inherited_through_subcategory(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let F := ℤ/4 in SmallModules(ℤ)")
    text = ok(kc, "F.annihilator()")
    assert "(4)" in text


# -- 6 · countable sets, ellipses, indexing -------------------------------

def test_progressions_membership_and_identity(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let X := {0, 1, 2, ...}")
    ok(kc, "assert X = ℕ")
    ok(kc, "let Y := {0, 2, 4, ...}")
    ok(kc, "assert 8 ∈ Y")
    ok(kc, "assert 9 ∉ Y")


def test_countable_indexing_and_cardinality(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "ℤ[3]")   # registered convention 0, 1, −1, 2, −2, …
    assert "2" in text
    text = ok(kc, "ℚ[3]")   # Cantor zigzag: 0, 1, −1, 1/2, … (#17)
    assert "1/2" in text
    text = ok(kc, "X.cardinality()")
    assert "ℵ₀" in text


# -- 7 · semantic availability ≠ computability ----------------------------

def test_capability_gap_is_structured_not_semantic(kernel: Kernel) -> None:
    _, kc = kernel
    # det is meaningful on any MatrixElems member; only ℚ entries are routed
    ok(kc, "let A := [1, 2; 3, 4] in Mat₂(ℤ/5)")
    text = err(kc, "A.det()")
    assert "NoImplementation" in text
    assert "det" in text
    # the gap is an execution-layer record, not a parse/type/category error
    assert "unknown" not in text.lower() or "method" not in text.lower()


def test_capability_gaps_audit_surface(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "#capability_gaps")
    assert "det" in text and "Mat₂(ℤ/5)" in text


def test_failed_cell_commits_nothing_prior_state_intact(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "n.factor()")  # n from test_factor_integer, still bound
    assert "2^3 * 3^2 * 5" in text


# -- 8 · transport along preferred functors --------------------------------

def test_cardinality_transported_along_forgetful_functor(kernel: Kernel) -> None:
    _, kc = kernel
    # F := ℤ/4 in SmallModules(ℤ), bound by the annihilator test; cardinality
    # is declared on Sets and arrives via UnderlyingSet : Modules → Sets
    text = ok(kc, "F.cardinality()")
    assert "4" in text
    ok(kc, "assert 2 ∈ F")


def test_transport_step_visible_only_in_diagnostics(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "#explain_route F.cardinality()")
    assert "UnderlyingSet" in text
    assert "Modules" in text and "Sets" in text


def test_transport_does_not_preempt_direct_resolution(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "F.annihilator()")  # still direct, through SmallModules ≤ Modules
    assert "(4)" in text


def test_bare_equality_is_category_bound(kernel: Kernel) -> None:
    _, kc = kernel
    # U(F) = {0,1,2,3} in Sets, but F is a module and bare `=` never inserts
    # the functor: cross-category equality is trivially false
    text = err(kc, "assert F = {0, 1, 2, 3}")
    assert "false" in text.lower()
    ok(kc, "assert F ≠ {0, 1, 2, 3}")
    # the Sets question is one explicit call away, receiver transported
    text = ok(kc, "F.set_eq({0, 1, 2, 3})")
    assert "true" in text


# -- 9 · functions ---------------------------------------------------------

def test_both_binder_spellings_denote_the_same_function(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "let h := t ↦ t² + 1 in ℝ → ℝ")
    assert "t ↦ t^2 + 1" in text and "ℝ → ℝ" in text
    ok(kc, "let hp(t) := t^2 + 1 in R->R")   # ASCII domain, superscript-free body
    ok(kc, "assert h = hp")


def test_function_evaluates_at_a_point(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert h(0) = 1")
    ok(kc, "assert h(3) = 10")
    text = err(kc, "assert h(3) = 11")
    assert "false" in text.lower()


def test_function_identity_is_normalized_not_sampled(kernel: Kernel) -> None:
    _, kc = kernel
    # both sides substitute a polynomial into the body; `t` is available
    # because a function binding it is in scope
    ok(kc, "assert h(-t) = h(t)")
    # the value really is the substituted body, not a number: a bare
    # polynomial renders in its own indeterminate `x`
    text = ok(kc, "h(-t)")
    assert "x^2 + 1" in text


def test_a_body_the_polynomial_engine_cannot_express_is_symbolic(
        kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md §Elementary calculus' bodies. This test runs BEFORE the one
    # below, and that ordering is the point: `e` is Euler's number only while
    # nothing has bound the name, and the next test binds it to SPEC.md's own
    # doubling map. Both halves of the collision are pinned.
    text = ok(kc, "let expo := t ↦ e^t in ℝ → ℝ")
    assert "t ↦ e^t" in text and "ℝ → ℝ" in text
    text = ok(kc, "let sine: ℝ → ℝ := t ↦ sin(t)")
    assert "t ↦ sin(t)" in text
    ok(kc, "let recip := t ↦ 1/t in ℝ → ℝ")
    # a symbolic body is a PRESENTATION: nothing here evaluates it at a point,
    # and the refusal says so rather than approximating
    text = err(kc, "sine(0)")
    assert "SYMBOLIC body" in text and "approximation" in text
    # …and a RATIONAL body is refused at a point for the same reason: `1/t` is
    # an expression this slice presents, not a function it evaluates
    text = err(kc, "recip(2)")
    assert "SYMBOLIC body" in text and "approximation" in text
    # the POLYNOMIAL reading is preferred wherever it applies, and these are
    # the sentinels: both are identities of function expressions, which only
    # that reading decides
    ok(kc, "assert h(-t) = h(t)")
    ok(kc, "assert h(3) = 10")
    # …and the vocabulary is a CLOSED list, named in the refusal. `arctan` is
    # also a body NEITHER reading reaches — the polynomial engine hits an
    # unbound name — so the refusal carries BOTH reasons rather than losing
    # the polynomial side behind the vocabulary list
    text = err(kc, "let bad := t ↦ arctan(t) in ℝ → ℝ")
    assert "arctan" in text and "sin" in text and "vocabulary" in text
    assert "polynomial reading was tried first" in text and "not bound" in text
    # (a body the polynomial engine reads FINE but that is not a polynomial —
    # a matrix literal — has no such reason to carry, and reports the
    # vocabulary alone)
    text = err(kc, "let bad2 := t ↦ [1, 2; 3, 4] in ℝ → ℝ")
    assert "vocabulary" in text and "polynomial reading was tried" not in text
    # …and a body whose POLYNOMIAL reading hits a capability GAP propagates
    # that gap: it is not an expressibility failure, so it must not be
    # laundered into "not in the vocabulary"
    ok(kc, "let zpoly := x ↦ x^2 + 1 in ℤ[x]")
    text = err(kc, "let bad3 := t ↦ zpoly.gcd(zpoly) in ℝ → ℝ")
    assert "NoImplementation" in text and "vocabulary" not in text


def test_a_symbolic_body_typesets(kernel: Kernel) -> None:
    _, kc = kernel
    # `\sin` and `e^{t}` are math mode's own spellings; the plain text stays
    # in the bundle as the fallback every consumer can read
    b = bundle(kc, "sine")
    assert b["text/latex"] == "$$t \\mapsto \\sin(t)$$"
    assert b["text/plain"] == "t ↦ sin(t)"
    b = bundle(kc, "expo")
    assert b["text/latex"] == "$$t \\mapsto e^{t}$$"


def test_typed_colon_ascription_spelling(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "let e: ℕ → ℕ := n ↦ 2n")
    assert "n ↦ 2n" in text and "ℕ → ℕ" in text


def test_a_binding_shadows_the_symbolic_constant_it_spells(
        kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md collides with itself: `e` is the doubling map in §Set
    # comprehensions and Euler's number in §Elementary calculus. A binding
    # wins over a constant — the rule `i` and `R` already follow — so with
    # `e` bound, SPEC.md's own `e^t` reads the BINDING and refuses.
    text = err(kc, "let boom := t ↦ e^t in ℝ → ℝ")
    assert "'e' is BOUND" in text
    # `exp(t)` is the spelling no binding can shadow, and it is the same
    # function the constant would have named
    text = ok(kc, "let expo2 := t ↦ exp(t) in ℝ → ℝ")
    assert "t ↦ exp(t)" in text


def test_composition_is_an_identity_of_function_expressions(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let f(t) = t^2 in RR->RR")   # SPEC.md spells the definition with `=`
    ok(kc, "let g(t) = t^3 in RR->RR")
    ok(kc, "assert (f ∘ g)(t) = t^6")
    ok(kc, "assert (f ∘ g)(2) = 64")


def test_non_composable_domains_fail_loudly(kernel: Kernel) -> None:
    _, kc = kernel
    # e : ℕ → ℕ from the typed-ascription test; f : ℝ → ℝ
    text = err(kc, "assert (f ∘ e)(t) = t")
    assert "do not compose" in text


def test_lambda_without_a_domain_is_refused(kernel: Kernel) -> None:
    _, kc = kernel
    text = err(kc, "let bad := t ↦ t^2")
    assert "ascription" in text


def test_body_neither_reading_can_express_is_refused(kernel: Kernel) -> None:
    _, kc = kernel
    # PIN CHANGED, deliberately, and the reason is that the gap it recorded
    # closed. U1 pinned "a body the polynomial engine cannot express is
    # refused at the binding, until the calculus sections land"; they have
    # landed, so a body it cannot express is now read SYMBOLICALLY instead.
    # What is left refused is a body NEITHER reading reaches — and the
    # refusal is the symbolic reader's, which lists the vocabulary. That is
    # a wider refusal than the old one, not a narrower: `t ↦ sin(t)` moved
    # from this side of the line to the other, and nothing moved back.
    text = err(kc, "let bad := t ↦ [1, 2; 3, 4] in ℝ → ℝ")
    assert "a matrix literal" in text and "vocabulary" in text
    text = err(kc, "let bad2 := t ↦ ℕ in ℝ → ℝ")
    assert "vocabulary" in text


def test_binder_is_scoped_to_calls_not_the_session(kernel: Kernel) -> None:
    _, kc = kernel
    # `h := t ↦ …` and `f`, `g` are bound above, yet a bare `t` outside a call
    # is NOT in scope: the honest-error channel is not widened by a definition
    text = err(kc, "t")
    assert "'t' is not bound" in text
    text = err(kc, "assert t = t")
    assert "'t' is not bound" in text
    text = err(kc, "assert zzz = 1")
    assert "'zzz' is not bound" in text
    # inside a call, and across an assertion containing one, it IS in scope —
    # the two SPEC.md identities keep working
    ok(kc, "assert h(-t) = h(t)")
    ok(kc, "assert (f ∘ g)(t) = t^6")


def test_a_binding_still_wins_over_a_callee_binder(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let s := 5 in ℤ")
    ok(kc, "let w(s) = s + 1 in ℕ → ℕ")
    ok(kc, "assert w(s) = 6")   # w(5), not the indeterminate


def test_argument_outside_the_source_domain_is_refused(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert e(3) = 6")   # e : ℕ → ℕ, bound above
    text = err(kc, "e(-1)")
    assert "-1 is not an element of ℕ" in text


def test_result_lands_in_the_target_domain(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let k(t) = t + 7 in ℤ/5 → ℤ/5")
    text = ok(kc, "k(4)")       # 4 + 7 in ℤ/5, not 11
    assert "1 ∈ ℤ/5" in text
    ok(kc, "assert k(4) = 1")


def test_symbolic_call_reduces_in_the_arrows_domain(kernel: Kernel) -> None:
    _, kc = kernel
    # the identity holds in ℤ/5, where the arrow says it lives — not in the
    # ℤ the body was written in
    text = ok(kc, "k(t)")
    assert "x + 2" in text
    ok(kc, "assert k(t) = t + 2")
    text = err(kc, "assert k(t) = t + 3")
    assert "false" in text.lower()


# -- 10 · registry-driven embeddings ----------------------------------------

def test_registered_quotient_embedding_int_to_mod(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "map n to ℤ/7")  # n = 360 ≡ 3 (mod 7); ℤ → ℤ/n is ONE rule
    assert "3" in text


def test_canonical_maps_audit_surface(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "#canonical_maps")
    assert "ℕ → ℤ" in text and "ℤ → ℤ/_" in text and "intToMod" in text


def test_unregistered_embedding_is_honest_error(kernel: Kernel) -> None:
    _, kc = kernel
    # q ∈ ℚ[x] (rebound to x² - 2 by the roots test, still ℚ[x]); ℚ → ℤ is
    # not a registered embedding
    text = err(kc, "map q to ℤ[x]")
    assert "no preferred canonical map" in text


# -- 11 · a binding always wins ---------------------------------------------
# Both readings a name can acquire — the prefix spelling of a method call, and
# the indeterminate of a polynomial ring — apply to UNBOUND names only. The
# names bound here (`det`, `z`) appear nowhere else, so these tests do not
# depend on running after anything.

def test_a_binding_wins_over_the_prefix_method_spelling(kernel: Kernel) -> None:
    _, kc = kernel
    # `det` is a declared method, so `det(2)` would otherwise be the prefix
    # spelling of `2.det()`. A binding of that name is an ordinary value, and
    # calling it is the ordinary not-callable error.
    ok(kc, "let det := 7 in ℤ")
    text = err(kc, "det(2)")
    assert "7 ∈ ℤ is not callable" in text


# -- 12 · finite sets and set algebra -------------------------------------
# SPEC.md §Finite sets. `A` is rebound here (it named the Mat₂(ℤ/5) gap
# fixture above, whose tests are all before this point); `B` appears nowhere
# else in this file.

def test_both_powerset_ascriptions_are_checked_membership(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let A := {1, 2, 3} in 𝒫(ℤ)")
    ok(kc, "let B := {3, 4, 5} in 2^ℤ")     # SPEC.md's other spelling
    # the ascription is a JUDGMENT, not an annotation: a set that does not
    # lie in the ascribed powerset is refused at the binding
    text = err(kc, "let bad3 := {1, 1/2} in 𝒫(ℤ)")
    assert "is not an element of" in text


def test_the_four_binary_operations(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert A ∪ B = {1, 2, 3, 4, 5}")
    ok(kc, "assert A ∩ B = {3}")
    ok(kc, "assert A \\ B = {1, 2}")
    ok(kc, "assert A △ B = {1, 2, 4, 5}")
    # each one rejects a wrong answer
    for wrong in ("A ∪ B = {1, 2, 3, 4}", "A ∩ B = {4}",
                  "A \\ B = {1, 2, 3}", "A △ B = {1, 2, 4}"):
        assert "false" in err(kc, f"assert {wrong}").lower()


def test_cardinality_product_and_powerset(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert |A| = 3")
    ok(kc, "assert |A × B| = 9")
    ok(kc, "assert |𝒫(A)| = 2^|A|")
    assert "false" in err(kc, "assert |A| = 4").lower()
    # the product and the powerset are DENOTED, not listed
    text = ok(kc, "A × B")
    assert "{1, 2, 3} × {3, 4, 5}" in text
    text = ok(kc, "𝒫(A)")
    assert "𝒫({1, 2, 3})" in text
    # 𝒫 of a countably infinite set is uncountable: the slice says it cannot
    # state that cardinality rather than inventing ℵ₀
    text = err(kc, "|2^ℕ|")
    assert "uncountable" in text


def test_membership_and_inclusion(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert 2 ∈ A")
    ok(kc, "assert 4 ∉ A")
    ok(kc, "assert A ⊆ A ∪ B")
    ok(kc, "assert A ∩ B ⊆ A")
    assert "false" in err(kc, "assert A ⊆ B").lower()
    # membership in a powerset IS inclusion — SPEC.md's ASCII `in` spelling
    ok(kc, "assert A in 𝒫(ℤ)")
    ok(kc, "assert A ∪ B ∉ 𝒫(A)")
    # a finite set against a countably infinite domain is decided elementwise
    ok(kc, "assert A ⊆ ℤ")
    # a domain inclusion is the canonical-map registry's claim — and it is now
    # ANSWERED from there (see the number-systems section at the end of this
    # file). The set layer still refuses to restate it, which the native
    # `subset` guard in CasDslTests/Core.lean pins.
    ok(kc, "assert ℕ ⊆ ℤ")


def test_infinite_receivers_are_the_honest_gap(kernel: Kernel) -> None:
    _, kc = kernel
    # union is meaningful for every set; only explicit finite ones are routed
    text = err(kc, "ℤ ∪ A")
    assert "NoImplementation" in text and "union" in text
    text = err(kc, "𝒫(A) ∪ A")
    assert "NoImplementation" in text


# -- 13 · set comprehensions and images ------------------------------------
# SPEC.md §Set comprehensions. `S`, `E` and the binder names used here appear
# nowhere else in this file.

def test_a_finite_comprehension_is_decided(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let S := {n ∈ ℤ | n² ≤ 20}")
    ok(kc, "assert S in 𝒫(ℤ)")
    ok(kc, "assert S = {-4, -3, -2, -1, 0, 1, 2, 3, 4}")
    ok(kc, "assert |S| = 9")
    # exact on both sides of the boundary
    ok(kc, "assert 4 ∈ S")
    ok(kc, "assert 5 ∉ S")
    assert "false" in err(kc, "assert |S| = 10").lower()
    # SPEC.md §Ellipses spells the binder with the ASCII `in` too
    ok(kc, "assert {n in ℤ | n² ≤ 20} = S")


def test_a_numeral_against_a_domain_refuses_rather_than_splitting(
        kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md §Ellipses writes `assert Y = 2ℕ`, and there is still NO scaling
    # of a set by a number. What changed with #26 is the FAILURE: implicit
    # multiplication now takes an atom rather than an identifier, so `2ℕ` is
    # the product `2 · ℕ` and refuses loudly. It used to split into two
    # statements and quietly assert `Y = 2` while displaying `ℕ` beside it —
    # a decided answer to a claim nobody made, which is strictly worse than
    # this error.
    text = err(kc, "assert {0, 2, ...} = 2ℕ")
    assert "element value" in text and "ℕ" in text


def test_an_infinite_comprehension_is_its_progression(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "let E := {2n | n ∈ ℕ}")
    assert "{0, 2, ...}" in text
    ok(kc, "assert E in 𝒫(ℕ)")
    ok(kc, "assert 8 ∈ E")
    ok(kc, "assert 9 ∉ E")
    ok(kc, "assert |E| = ℵ₀")
    # membership is SOLVED, not enumerated: nothing counts to 10¹²
    ok(kc, "assert 1000000000000 ∈ E")
    ok(kc, "assert 1000000000001 ∉ E")
    assert "false" in err(kc, "assert 9 ∈ E").lower()
    # inclusion against a progression is decided elementwise: A has odd
    # members, so it is not inside the evens
    assert "false" in err(kc, "assert A ⊆ E").lower()


def test_the_image_of_a_function_is_that_same_set(kernel: Kernel) -> None:
    _, kc = kernel
    # e : ℕ → ℕ := n ↦ 2n, bound in the functions section above
    ok(kc, "assert e(ℕ) = E")
    ok(kc, "assert e.image() = E")
    text = ok(kc, "#explain_route e.image()")
    assert "FunctionElems" in text and "func_image" in text
    # applying a function to a set that is not its source is refused
    text = err(kc, "e(ℤ)")
    assert "is not its source" in text


def test_a_bounded_image_comprehension_enumerates_exactly(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "{e(n) | n ∈ ℕ, 0 ≤ n < 6}")
    assert "{0, 2, 4, 6, 8, 10}" in text
    ok(kc, "assert {e(n) | n ∈ ℕ, 0 ≤ n < 6} = {0, 2, 4, 6, 8, 10}")
    assert "false" in err(
        kc, "assert {e(n) | n ∈ ℕ, 0 ≤ n < 6} = {0, 2, 4, 6, 8}").lower()


def test_an_undecidable_comprehension_is_refused_at_the_binding(
        kernel: Kernel) -> None:
    _, kc = kernel
    # a predicate the polynomial engine does not reach: a structured gap, not
    # a sampled guess and not a truncated enumeration
    text = err(kc, "let notdecided := {n in ℕ | n.is_prime()}")
    assert "polynomial comparison" in text
    # an infinite solution set is reported as infinite, never cut off
    text = err(kc, "let notdecided := {n ∈ ℤ | n² ≥ 20}")
    assert "infinite" in text
    # an image that is not a progression is a gap too
    text = err(kc, "let notdecided := {n² | n ∈ ℕ}")
    assert "arithmetic progression" in text


def test_a_guard_that_only_the_indeterminate_understands_is_refused(
        kernel: Kernel) -> None:
    _, kc = kernel
    # The bounds are read with the binder as an INDETERMINATE, where `n.deg()`
    # answers 1 — while for an integer it is a resolver error. The candidate
    # loop re-reads the guard in the element world, so any range that
    # enumerates something is validated by construction; these three enumerate
    # NOTHING (two collapse to an empty range, one to the infinite refusal) and
    # would otherwise ship a verdict no element-world reading supported.
    for g in ("{n ∈ ℤ | n.deg() ≤ 0}", "{n ∈ ℕ | n.deg() ≤ 0}",
              "{n ∈ ℤ | n.deg() ≤ 1}"):
        text = err(kc, "let zz := %s" % g)
        assert "polynomial comparison" in text, g
        assert "infinite" not in text, g


def test_an_unguarded_head_is_read_in_the_element_world_too(
        kernel: Kernel) -> None:
    _, kc = kernel
    # The unguarded path reads the head ONCE, so without an element-world
    # reading the indeterminate's answer would be the whole verdict:
    # `n.deg()` is 1 there, and `{n.deg() | n ∈ ℤ}` presented `{1}`.
    for h in ("{n.deg() | n ∈ ℤ}", "{n.deg() | n ∈ ℕ}"):
        text = err(kc, "let zh := %s" % h)
        assert "does not evaluate for an element" in text, h
        assert "infinite" not in text, h
    # …while heads that genuinely evaluate for an element still decide
    ok(kc, "assert {p.deg() | n ∈ ℕ} = {3}")      # constant, element world agrees
    ok(kc, "assert {7 | n ∈ ℕ} = {7}")
    ok(kc, "assert {2n | n ∈ ℕ} = E")             # the progression, unchanged


def test_a_constant_guard_is_decided_not_misdiagnosed(kernel: Kernel) -> None:
    _, kc = kernel
    # A guard that does not mention the binder holds for every candidate or
    # for none. `0*n` and `n - n` reach that through the ZERO polynomial, and
    # both answers must be the constant ones — infinite, or the empty set —
    # never "no extractable bound", which describes a different failure.
    for g in ("0*n ≤ 0", "n - n ≤ 0", "1 ≤ 2"):
        text = err(kc, "let z1 := {n ∈ ℤ | %s}" % g)
        assert "infinite" in text, g
        assert "extractable bound" not in text, g
    # …and where the two readings AGREE constant, the empty set is decided
    ok(kc, "assert {n ∈ ℤ | n - n < 0} = {}")
    ok(kc, "assert {n ∈ ℕ | 0*n > 0} = {}")
    # over ℕ the lower bound is 0, so a constant-true guard is unbounded ABOVE
    text = err(kc, "let z2 := {n ∈ ℕ | 0*n ≤ 0}")
    assert "from above" in text and "infinite" in text


def test_both_caps_fail_loudly_rather_than_truncating(kernel: Kernel) -> None:
    _, kc = kernel
    # a bound the guard really does impose, past what the slice will test
    text = err(kc, "let big := {n ∈ ℤ | n² ≤ 10000000000}")
    assert "tests at most" in text and "20000000001" in text
    # 2^n past `powersetExpCap` stops being worth materializing
    assert "1024" in ok(kc, "|𝒫(ℤ/10)|")
    text = err(kc, "|𝒫(ℤ/5000)|")
    assert "too large" in text


def test_is_prime_is_a_ufd_method(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md §Ellipses writes `n.is_prime()`; primality is declared where
    # primes exist — on UFD elements — and routed for ℤ
    ok(kc, "let m7 := 7 in ℤ")
    assert "true" in ok(kc, "m7.is_prime()")
    ok(kc, "let m8 := 8 in ℤ")
    assert "false" in ok(kc, "m8.is_prime()")
    text = ok(kc, "#explain_route m7.is_prime()")
    assert "sage" in text.lower() and "FactorizationElems" in text
    # …so irreducibility in ℤ[x] is available and not executable
    text = err(kc, "p.is_prime()")
    assert "NoImplementation" in text and "is_prime" in text


def test_the_comprehension_binder_is_scoped_to_the_braces(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let cn := 100 in ℤ")
    # the binder shadows the session binding inside the braces…
    ok(kc, "assert {cn ∈ ℤ | cn² ≤ 20} = S")
    # …leaves it untouched outside them…
    ok(kc, "assert cn = 100")
    # …and publishes nothing: the binder name is still unbound afterwards
    ok(kc, "let cmset := {cmb ∈ ℤ | cmb² ≤ 1}")
    text = err(kc, "cmb")
    assert "'cmb' is not bound" in text


# -- 12 · LaTeX-first display (#16) ---------------------------------------

def test_the_showcase_shapes_are_typeset(kernel: Kernel) -> None:
    _, kc = kernel
    # issue #16's three expected shapes, exactly. The payload is the math
    # wrapped in `$$…$$` — the display register, which is what makes a
    # notebook typeset it with no show() call; `text/plain` stays in the
    # bundle as the fallback.
    ok(kc, "let ln := 360 in ℤ")
    b = bundle(kc, "ln.factor()")
    assert b["text/latex"] == r"$$2^{3} \cdot 3^{2} \cdot 5$$"
    assert b["text/plain"] == "2^3 * 3^2 * 5"

    ok(kc, "let lM := [1, 2; 3, 4] in Mat₂(ℚ)")
    b = bundle(kc, "lM.inverse()")
    assert b["text/latex"] == (
        r"$$\begin{pmatrix} -2 & 1 \\ 3/2 & -1/2 \end{pmatrix}$$")
    assert b["text/plain"] == "[-2, 1; 3/2, -1/2]"

    ok(kc, "let lq(x) := x^3 - 2x + 1 in ℤ[x]")
    b = bundle(kc, "lq")
    assert b["text/latex"] == r"$$x^{3} - 2x + 1$$"
    assert b["text/plain"] == "x^3 - 2x + 1"

    # a ℚ[x] factorization with non-unit content: the unit is a scalar like
    # any other, so an integral rational is an integer and never `2/1`
    ok(kc, "let lr(x) := 2*x^2 - 2 in ℚ[x]")
    b = bundle(kc, "lr.factor()")
    assert b["text/latex"] == r"$$2 \cdot (x - 1) \cdot (x + 1)$$"
    assert b["text/plain"] == "2 * (x - 1) * (x + 1)"

    # …and a CONSTANT has no factors at all: the unit alone is the answer, in
    # both spellings. An empty core would publish `$$$$` and an empty plain
    ok(kc, "let lc(x) := 1 in ℚ[x]")
    b = bundle(kc, "lc.factor()")
    assert b["text/latex"] == "$$1$$"
    assert b["text/plain"] == "1"


def test_sets_domains_and_cardinals_are_typeset(kernel: Kernel) -> None:
    _, kc = kernel
    # every LaTeX payload is math-mode LaTeX: MathJax does not typeset the raw
    # ℤ/↦/ℵ₀ the plain rendering uses, so nothing non-ASCII may reach it
    for code, expected in (
            ("lq.roots()", r"$$\{1\}$$"),
            ("{0, 2, 4, ...}", r"$$\{0, 2, \ldots\}$$"),
            ("{1, 2, 3}", r"$$\{1, 2, 3\}$$"),
            ("𝒫({1, 2})", r"$$\mathcal{P}(\{1, 2\})$$"),
            ("ℤ", r"$$\mathbb{Z}$$"),
            ("ℤ/5", r"$$\mathbb{Z}/5\mathbb{Z}$$"),
            ("|{0, 2, 4, ...}|", r"$$\aleph_0$$"),
            ("|{1, 2, 3}|", "$$3$$")):
        b = bundle(kc, code)
        assert b["text/latex"] == expected, code
        assert b["text/latex"].isascii(), code
        # nothing may ship as bare delimiters around nothing
        assert b["text/latex"].strip("$").strip() != "", code
        assert "text/plain" in b, code


def test_a_value_with_no_latex_form_emits_plain_text_only(
        kernel: Kernel) -> None:
    _, kc = kernel
    # a truth value: `\text{true}` would be typeset prose, not mathematics
    ok(kc, "let lb := 7 in ℤ")
    b = bundle(kc, "lb.is_prime()")
    assert b["text/plain"] == "true"
    assert "text/latex" not in b
    assert "application/vnd.casdsl.value+json" in b
    # the module fixture: displaying it as ℤ/4ℤ would be the RING, and
    # equality here is category-bound
    ok(kc, "let lF := ℤ/4 in SmallModules(ℤ)")
    b = bundle(kc, "lF")
    assert b["text/plain"] == "ℤ/4 as ℤ-module"
    assert "text/latex" not in b
    # a non-ASCII BINDER: `θ` is not a LaTeX command, and raw Unicode in math
    # mode does not typeset, so the whole function falls back to plain text
    ok(kc, "let lθ := θ ↦ θ + 1 in ℝ → ℝ")
    b = bundle(kc, "lθ")
    assert b["text/plain"] == "θ ↦ θ + 1"
    assert "text/latex" not in b
    # an ASCII binder that is not LaTeX-safe either: `x_1_2` is a double
    # subscript, which pdflatex rejects outright
    ok(kc, "let lu := x_1_2 ↦ x_1_2 + 1 in ℝ → ℝ")
    b = bundle(kc, "lu")
    assert b["text/plain"] == "x_1_2 ↦ x_1_2 + 1"
    assert "text/latex" not in b
    # …while a plain ASCII binder still typesets, so the guard narrows nothing
    ok(kc, "let lt := t ↦ t² + 1 in ℝ → ℝ")
    b = bundle(kc, "lt")
    assert b["text/latex"] == r"$$t \mapsto t^{2} + 1$$"


def test_assertions_and_diagnostics_stay_textual(kernel: Kernel) -> None:
    _, kc = kernel
    # a check-mark is not mathematics: an assertion publishes no bundle at all
    _, outputs = run_cell(kc, "assert 2 + 3 = 5")
    assert bundles(outputs) == []
    assert "✓" in all_text(outputs)
    for diagnostic in ("#explain_route ln.factor()", "#capabilities",
                       "#capability_gaps", "#canonical_maps"):
        b = bundle(kc, diagnostic)
        assert "text/latex" not in b, diagnostic
        assert "text/plain" in b, diagnostic


def test_the_value_payload_carries_a_set_result(kernel: Kernel) -> None:
    _, kc = kernel
    # the ceiling set display first exposed: a set OBJECT has no element-shaped
    # `Denote.value?`, and the payload used to carry a bare null for it
    b = bundle(kc, "lq.roots()")
    payload = b["application/vnd.casdsl.value+json"]
    assert payload["value"]["t"] == "set"
    assert payload["value"]["elems"] == [{"t": "int", "v": "1"}]
    b = bundle(kc, "{0, 2, 4, ...}")
    assert b["application/vnd.casdsl.value+json"]["value"]["t"] == "progression"
    # a DENOTED set has no wire value and says so — that is the honest answer
    b = bundle(kc, "𝒫({1, 2})")
    assert b["application/vnd.casdsl.value+json"]["value"] is None


# -- 13 · exact number systems: the ⊆-chain -----------------------------------
# SPEC.md §Exact number systems. Inclusion between two DOMAINS is decided from
# the canonical-map registry, so every claim here is a claim about that
# registry — and `and` is a conjunction of assertions, not a term operator.

def test_the_number_system_chain(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ")   # SPEC.md, verbatim
    # each link on its own, and the ones nobody registered are false
    ok(kc, "assert ℚ ⊆ ℂ")
    assert "false" in err(kc, "assert ℝ ⊆ ℚ").lower()
    assert "false" in err(kc, "assert ℚ ⊆ ℤ").lower()
    # a registered canonical map that is NOT an inclusion: the quotient
    # ℤ → ℤ/5 exists — `map n to ℤ/7` above uses its sibling — and does not
    # make ℤ a subset of ℤ/5
    assert "false" in err(kc, "assert ℤ ⊆ ℤ/5").lower()
    # a chain is decided conjunct by conjunct, and says WHICH one failed
    text = err(kc, "assert ℤ ⊆ ℚ and ℝ ⊆ ℚ and ℝ ⊆ ℂ")
    assert "false" in text.lower() and "ℝ ⊆ ℚ" in text
    # …and a chain of true claims is one commit with one check-mark
    text = ok(kc, "assert 2 + 3 = 5 and 4 ∉ {1, 2, 3}")
    assert "✓ 2 + 3 = 5 and 4 ∉ {1, 2, 3}" in text


def test_an_integer_is_a_real_number(kernel: Kernel) -> None:
    _, kc = kernel
    # The visible consequence of registering the chain's transitive closure
    # (DESIGN.md §Coercions): a domain ascription to ℝ or ℂ now goes through a
    # registered canonical map, where it used to have none to apply.
    text = ok(kc, "let rr := 3 in ℝ")
    assert "3 ∈ ℝ" in text
    text = ok(kc, "map 3 to ℂ")
    assert "3" in text
    # …and a pair nobody registered is still the honest error
    text = err(kc, "let bad4 := 3 in ℝ → ℝ")
    assert "no preferred canonical map" in text or "not an element" in text


def test_a_domain_is_a_receiver_too(kernel: Kernel) -> None:
    _, kc = kernel
    # `ℝ.cardinality()` lexes as ONE identifier, so the domain reaches the
    # evaluator as a NAME. It used to fail with "'ℝ' is not bound"; the honest
    # answer is that ℝ is uncountable and this slice cannot state that cardinal
    text = err(kc, "ℝ.cardinality()")
    assert "cannot express the cardinality of ℝ" in text
    assert "not bound" not in text
    # the countable ones answer through the same path
    assert "ℵ₀" in ok(kc, "ℤ.cardinality()")
    # …and ℝ is a set that is not a COUNTABLE one, so indexing it does not
    # even resolve: `nth` is declared on CountableSets
    text = err(kc, "ℝ[3]")
    assert "not a method of any category" in text


# -- 14 · √2, i, and the complex plane ---------------------------------------
# SPEC.md §Exact number systems. Everything here is EXACT — `√2`, `2√2`,
# `2 + 2i` are algebraic numbers in the normal form a + b√d, and no cell in
# this section produces a decimal. `z` is rebound here (SPEC.md's own name for
# it); the test that bound it before is above.

def test_exact_algebraic_membership(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert √2 ∈ ℝ")            # SPEC.md, verbatim
    ok(kc, "assert 2 + 2i ∈ ℂ")        # SPEC.md, verbatim
    # the memberships that must fail, one per reason
    assert "false" in err(kc, "assert √2 ∈ ℚ").lower()
    assert "false" in err(kc, "assert 2 + 2i ∈ ℝ").lower()
    # the value is a normal form, not a decimal: `√8` IS `2√2`
    text = ok(kc, "√8")
    assert "2√2" in text and "2.82" not in text
    ok(kc, "assert √8 = 2√2")
    ok(kc, "assert √2 · √2 = 2")


def test_the_complex_methods(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let z := 2 + 2i in ℂ")     # SPEC.md, verbatim, and so are the five
    ok(kc, "assert z.re() = 2")
    ok(kc, "assert z.im() = 2")
    ok(kc, "assert z.bar() = 2 - 2i")
    ok(kc, "assert z · z.bar() = 8")
    ok(kc, "assert |z| = 2√2")
    # each one rejects a wrong answer
    for wrong in ("z.re() = 3", "z.im() = 0", "z.bar() = 2 + 2i",
                  "z · z.bar() = 4", "|z| = 2"):
        assert "false" in err(kc, f"assert {wrong}").lower(), wrong
    # the modulus is exact: |2 + 2i| is 2√2 and never 2.828…
    text = ok(kc, "|z|")
    assert "2√2" in text and "2.8" not in text
    # …and the four are native, not a backend's answer
    text = ok(kc, "#explain_route z.bar()")
    assert "native" in text and "ComplexElems" in text


def test_the_bars_are_one_spelling_of_two_methods(kernel: Kernel) -> None:
    _, kc = kernel
    # a SET is counted, an element of ℝ or ℂ is measured, and a receiver that
    # is neither gets the ordinary not-a-method error — the bars invent nothing
    assert "3" in ok(kc, "|{1, 2, 3}|")
    assert "2√2" in ok(kc, "|z|")
    text = err(kc, "|3|")
    assert "'abs' is not a method of any category" in text
    text = ok(kc, "#explain_route z.abs()")
    assert "alg_abs" in text


def test_the_exact_form_has_a_ceiling_and_says_so(kernel: Kernel) -> None:
    _, kc = kernel
    # two different quadratic fields leave the presentation: a loud gap, never
    # a dropped term and never a decimal
    text = err(kc, "√2 + √5")
    assert "gap, not an approximation" in text
    # …while one field is closed under the arithmetic
    ok(kc, "assert (1 + √2) · (1 - √2) = -1")
    # √ of something that is not a rational is refused rather than approximated
    text = err(kc, "√(1 + √2)")
    assert "does not approximate" in text


def test_exact_algebraic_values_are_typeset(kernel: Kernel) -> None:
    _, kc = kernel
    for code, expected in (
            ("√2", r"$$\sqrt{2}$$"),
            ("2√2", r"$$2\sqrt{2}$$"),
            ("2 + 2i", "$$2 + 2i$$"),
            ("ℂ", r"$$\mathbb{C}$$")):
        b = bundle(kc, code)
        assert b["text/latex"] == expected, code
        assert b["text/latex"].isascii(), code   # no `√`, no `ℂ` in a payload
        assert "text/plain" in b, code
    assert bundle(kc, "√2")["text/plain"] == "√2"


# -- 15 · ℂ[x]: where the cubic splits ---------------------------------------
# SPEC.md §Polynomials' last two blocks. `p` (x³ - 2x + 1 over ℤ) and `q`
# (x² - 2 over ℚ) are bound in §3 above; `pc` and `qc` are new here.

def test_a_polynomial_evaluated_at_an_exact_irrational(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md, verbatim: q = x² - 2 in ℚ[x] has √2 for a root, exactly —
    # √2 · √2 is 2 and not 1.9999999
    ok(kc, "assert q(√2) = 0")
    ok(kc, "assert q(-√2) = 0")
    assert "false" in err(kc, "assert q(√2) = 1").lower()
    assert "false" in err(kc, "assert q(2) = 0").lower()


def test_the_cubic_splits_over_the_complex_numbers(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let pc := map p to ℂ[x]")     # SPEC.md's `q := map p to ℂ[x]`
    text = ok(kc, "pc.factor()")
    # the CONTENT, not one string: Sage owns the factor order and the unit
    # convention (DESIGN.md decision 7), so what is pinned here is that three
    # linear factors came back and that the roots SPEC.md displays are roots.
    assert text.count("(x") >= 2 and "√5" in text
    ok(kc, "assert pc((-1 + √5) / 2) = 0")
    ok(kc, "assert pc((-1 - √5) / 2) = 0")
    ok(kc, "assert pc(1) = 0")
    assert "false" in err(kc, "assert pc((-1 + √5) / 3) = 0").lower()
    # a factorization whose factors do not lie in a + b√d is a loud refusal
    # from the adapter, not a decimal: x⁵ - 1 has roots of degree 4 over ℚ
    ok(kc, "let pf := x ↦ x^5 - 1 in ℂ[x]")
    text = err(kc, "pf.factor()")
    assert "not_expressible" in text


def test_roots_in_the_complex_numbers_and_the_difference_set(
        kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md writes `assert q.roots() ⊆ ℂ - ℚ` for q ∈ ℚ[x]. `roots` answers
    # in the polynomial's OWN coefficient ring — the pinned decision above —
    # so over ℚ that set is EMPTY and the inclusion holds VACUOUSLY. It runs,
    # and the honest version of the claim is the next three lines.
    ok(kc, "assert q.roots() = {}")
    ok(kc, "assert q.roots() ⊆ ℂ - ℚ")
    ok(kc, "let qc := map q to ℂ[x]")
    text = ok(kc, "qc.roots()")
    assert "√2" in text and "2.41" not in text and "1.41" not in text
    ok(kc, "assert qc.roots() = {√2, -√2}")
    ok(kc, "assert qc.roots() ⊆ ℂ - ℚ")     # …with two elements in it
    ok(kc, "assert √2 ∈ qc.roots()")
    assert "false" in err(kc, "assert qc.roots() = {√2}").lower()
    assert "false" in err(kc, "assert 2 ∈ qc.roots()").lower()
    # the difference set decides membership pointwise and refuses the rest
    ok(kc, "assert 2 + 2i ∈ ℂ - ℚ")
    assert "false" in err(kc, "assert 1 ∈ ℂ - ℚ").lower()
    text = err(kc, "|ℂ - ℚ|")
    assert "cannot state the cardinality" in text
    b = bundle(kc, "ℂ - ℚ")
    assert b["text/latex"] == r"$$\mathbb{C} \setminus \mathbb{Q}$$"
    assert b["text/plain"] == "ℂ - ℚ"


def test_a_surd_coefficient_crosses_the_wire(kernel: Kernel) -> None:
    _, kc = kernel
    # The Lean alg ENCODER runs only for a ℂ[x] polynomial that actually
    # carries a surd, and only against real Sage. `x - √2` is the sharp case:
    # a sign flip anywhere in that codec sends `x + √2` and comes back with
    # the other root.
    ok(kc, "let ps := x ↦ x - √2 in ℂ[x]")
    ok(kc, "assert ps.roots() = {√2}")
    assert "false" in err(kc, "assert ps.roots() = {-√2}").lower()
    text = ok(kc, "ps.factor()")
    assert "√2" in text and "1.41" not in text
    # …and once more with a NEGATIVE radicand, which a symmetric flip of both
    # halves of the codec cannot survive: Sage answers d = -1 either way
    ok(kc, "let pim := x ↦ x - i in ℂ[x]")
    ok(kc, "assert pim.roots() = {i}")
    assert "false" in err(kc, "assert pim.roots() = {-i}").lower()


# -- 16 · numerical approximation: map x to ℝ/O(ε) ---------------------------
# SPEC.md §Exact number systems' last block. `ℝ/O(ε)` is SUGAR for a requested
# absolute tolerance and NOT a quotient (|a − b| < ε is not transitive), so the
# result carries the exact value, the decimal presenting it, and the ε asked
# for. This section runs before `i` is shadowed below.

def test_the_spec_approximation_line(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md, verbatim — the line and the display it writes under it
    b = bundle(kc, "map √2 to ℝ/O(1/10^{10})")
    assert b["text/plain"] == "1.4142135623 + O(1/10^{10})"
    assert b["text/latex"] == "$$1.4142135623 + O(1/10^{10})$$"
    assert b["text/latex"].isascii()
    # the DIGITS are the claim, not decoration: a coarser tolerance shows
    # fewer of them, and the exact value is never a decimal until asked
    assert "1.41 + O(1/10^{2})" in ok(kc, "map √2 to ℝ/O(1/10^{2})")
    # …and the exact value itself is untouched by having been asked: no cell
    # that did not ask for a decimal produces one
    assert bundle(kc, "√2")["text/plain"] == "√2"


def test_the_approximation_keeps_the_exact_value_it_is_of(kernel: Kernel) -> None:
    _, kc = kernel
    payload = bundle(kc, "map √2 to ℝ/O(1/10^{4})")[
        "application/vnd.casdsl.value+json"]["value"]
    assert payload["t"] == "approx", payload
    # the source is the exact algebraic number, unchanged — asking for a
    # decimal presentation does not replace the value with it
    assert payload["exact"] == {"t": "alg",
                               "a": {"t": "rat", "num": "0", "den": "1"},
                               "b": {"t": "rat", "num": "1", "den": "1"},
                               "d": "2"}, payload
    assert payload["decimal"] == "1.4142", payload
    # …and both tolerances travel with it: the one requested and the one the
    # backend certified
    assert payload["eps"] == {"t": "rat", "num": "1", "den": "10000"}, payload
    assert payload["achieved"] == {"t": "rat", "num": "1", "den": "10000"}, payload


def test_the_registry_decides_what_may_be_presented_in_the_reals(
        kernel: Kernel) -> None:
    _, kc = kernel
    # `map … to ℝ/O(ε)` moves the value into ℝ along the REGISTERED canonical
    # map first, so everything the ⊆-chain covers can be asked for…
    assert "0.333 + O(1/10^{3})" in ok(kc, "map 1/3 to ℝ/O(1/10^{3})")
    assert "3.00 + O(1/10^{2})" in ok(kc, "map 3 to ℝ/O(1/10^{2})")
    assert "0.70710678 + O" in ok(kc, "map 1/√2 to ℝ/O(1/10^{8})")
    # …and ℂ is refused by the REGISTRY, which registers no map into ℝ — not
    # by a special case, and never by dropping the imaginary part
    text = err(kc, "map 2 + 2i to ℝ/O(1/10^{4})")
    assert "no preferred canonical map" in text and "into ℝ" in text
    assert "1.41" not in text and "2.82" not in text


def test_a_tolerance_is_a_positive_rational(kernel: Kernel) -> None:
    _, kc = kernel
    # ε ≤ 0 is refused AT THE SURFACE as not-a-tolerance: no finite decimal is
    # within 0 of an irrational, and that is a different statement from "no
    # backend could meet it" (which is the capability failure below)
    for bad in ("map √2 to ℝ/O(0)", "map √2 to ℝ/O(-1/10)"):
        text = err(kc, bad)
        assert "is not a tolerance" in text, bad
        assert "capability" not in text.lower(), bad


def test_an_unmeetable_tolerance_is_a_capability_failure(kernel: Kernel) -> None:
    _, kc = kernel
    # every configured backend refusing to meet ε is a CAPABILITY failure, and
    # the tolerance that was requested is visible in it (issue #7's third
    # acceptance criterion)
    text = err(kc, "map √2 to ℝ/O(1/10^{2000})")
    assert "capability" in text.lower()
    assert "O(1/10^{2000})" in text
    assert "tolerance_not_met" in text
    # …and it says nothing about the VALUE being defective
    assert "not a tolerance" not in text


def test_the_approximation_target_is_not_a_domain(kernel: Kernel) -> None:
    _, kc = kernel
    # `ℝ/O(ε)` is the target of `map … to`, and nothing else — there is no
    # quotient here to be an element of, or for ℝ to be included in, so the
    # claim cannot even be stated (let alone answered `true`)
    for code in ("ℝ/O(1/10)", "assert ℝ ⊆ ℝ/O(1/10)", "assert √2 ∈ ℝ/O(1/10)",
                 "let bad5 := ℝ/O(1/10)"):
        text = err(kc, code)
        assert "not a domain" in text and "not transitive" in text, code


def test_the_map_spelling_answers_in_its_own_terms(kernel: Kernel) -> None:
    _, kc = kernel
    # `map … to ℝ/O(ε)` is ONE construct to the user; the routed `approximate`
    # method is how it is implemented, not a step anyone wrote. No failure of
    # the map spelling may name it. (`#capability_gaps` and an explicit
    # `x.approximate(ε)` call are the audit surfaces where the method DOES
    # appear — see the ℂ gap above.)
    for code in ("map √2 to ℝ/O(0)", "map 2 + 2i to ℝ/O(1/10)",
                 "map √2 to ℝ/O(1/10^{2000})", "map ℤ to ℝ/O(1/10)",
                 "map √2 to ℝ/O(ℤ)", "(map √2 to ℝ/O(1/10)) + 1"):
        assert "approximate" not in err(kc, code), code


def test_the_tolerance_is_read_from_the_surface_spelling(kernel: Kernel) -> None:
    _, kc = kernel
    # ε is an exact rational, whatever the spelling computes to — a reciprocal
    # power of TWO is displayed as the rational it is, since only a power of
    # ten has the `1/10^{k}` spelling SPEC.md writes
    assert ("1.4142135623730950 + O(1/9007199254740992)"
            in ok(kc, "map √2 to ℝ/O(1/2^{53})"))
    assert "1.4 + O(1/3)" in ok(kc, "map √2 to ℝ/O(1/3)")


def test_an_approximation_is_a_result_not_a_binding(kernel: Kernel) -> None:
    _, kc = kernel
    # DISCLOSED, and shared with every other domainless result (a
    # factorization, an ideal, a cardinal): a `let` binds an OBJECT, and an
    # approximation presents no domain — it is not an element of ℝ/O(ε),
    # because there is nothing to be an element of. It displays and it fails
    # loudly; it does not bind to something it is not.
    assert "is not an object" in err(kc, "let ap := map √2 to ℝ/O(1/10^{4})")
    assert "is not an object" in err(kc, "let apf := n.factor()")   # n = 360
    # …and two approximations are not compared: |a − b| < ε is not transitive,
    # so the honest outcome is `unknown` rather than a decided equality
    assert "unknown" in err(kc, "assert (map √2 to ℝ/O(1/10^{4})) = 1")


def test_an_approximation_has_no_arithmetic(kernel: Kernel) -> None:
    _, kc = kernel
    # a requested tolerance is not an error term, and this slice does not
    # invent an error calculus to propagate one
    # …in ONE wording, whichever operator reaches it: a binary operation, the
    # unary negation that has its own arm, and a power (whose fold multiplies
    # up from 1, so the refusal must name the user's operator and operand
    # rather than a multiplication by a `1` nobody wrote)
    for code, op in (("(map √2 to ℝ/O(1/10^{4})) + 1", "addition"),
                     ("-(map √2 to ℝ/O(1/10^{4}))", "negation"),
                     ("(map √2 to ℝ/O(1/10^{4}))^2", "exponentiation")):
        text = err(kc, code)
        assert f"{op} is not defined on an approximation" in text, code
        assert "compute exactly, then ask for a decimal" in text, code


def test_the_complex_approximation_is_a_structured_gap(kernel: Kernel) -> None:
    _, kc = kernel
    # asking for a decimal is meaningful for every exact number — the method
    # is declared on ComplexElems — and only the REALS are routed, so ℂ is the
    # honest capability gap, exactly like det over ℤ/5
    ok(kc, "let apz := 2 + 2i in ℂ")
    text = err(kc, "apz.approximate(1/1000)")
    assert "NoImplementation" in text and "approximate" in text
    assert "2.82" not in text          # never a projection to |z| or to Re z
    # …while the real one routes, and the diagnostic names the backend
    ok(kc, "let apr := √2 in ℝ")
    text = ok(kc, "#explain_route apr.approximate(1/1000)")
    assert "sage" in text and "approx_real" in text and "ComplexElems" in text


def test_both_spellings_answer_for_the_tolerance_alike(kernel: Kernel) -> None:
    _, kc = kernel
    # criterion 3 is not spelling-scoped: `x.approximate(ε)` is the same
    # request as `map x to ℝ/O(ε)`, so it refuses a non-positive ε at the
    # surface and reports an unmeetable one as the capability failure naming
    # the tolerance — in the O(1/10^{k}) spelling, not 2000 literal zeros.
    ok(kc, "let apr2 := √2 in ℝ")
    for code in ("map √2 to ℝ/O(0)", "apr2.approximate(0)"):
        text = err(kc, code)
        assert "is not a tolerance" in text, code
        assert "capability" not in text.lower(), code
    for code in ("map √2 to ℝ/O(1/10^{2000})", "apr2.approximate(1/10^{2000})"):
        text = err(kc, code)
        assert "capability" in text.lower(), code
        assert "O(1/10^{2000})" in text, code
        assert "0000000000" not in text, code


def test_only_the_tolerance_failures_are_capability_failures(
        kernel: Kernel) -> None:
    _, kc = kernel
    # the wrapper speaks for a missing route and a backend that could not meet
    # ε. A RESOLVE failure is about the receiver, so it must come through
    # untouched — "no backend produced a decimal" over a body naming the
    # profile would be a lie in the wrapper's own words.
    ok(kc, "let apthree := 3 in ℤ")   # `3.approximate(…)` lexes as a decimal
    text = err(kc, "apthree.approximate(1/10)")
    assert "not a method of any category" in text
    assert "capability" not in text.lower()


def test_a_non_rational_tolerance_is_refused_in_surface_words(
        kernel: Kernel) -> None:
    _, kc = kernel
    # both spellings validate ε at the same junction, so neither reaches the
    # backend to be refused in the backend's vocabulary
    ok(kc, "let apr3 := √2 in ℝ")
    # …and an EMPTY call is an arity failure, not a tolerance one
    text = err(kc, "apr3.approximate()")
    assert "takes 1 argument(s), got 0" in text
    assert "tolerance" not in text
    for code in ("apr3.approximate(√2)", "apr3.approximate(ℤ)",
                 "apr3.approximate({1, 2})", "map √2 to ℝ/O(√2)"):
        text = err(kc, code)
        assert "exact positive rational" in text, code
        assert "sage op" not in text, code


def test_a_base_without_arithmetic_names_its_own_operator(
        kernel: Kernel) -> None:
    _, kc = kernel
    # `Common.same` is a shared SHAPE, not an operation: a fold from 1 would
    # otherwise report a multiplication by a `1` nobody wrote — and answer
    # that `1` at exponent 0
    ok(kc, "let apset := {1, 2, 3}")
    for base in ("apset.contains(2)", "|apset|"):
        text = err(kc, f"assert {base}^2 = 1")
        assert "exponentiation is not defined on" in text, base
        assert "multiplication" not in text, base
        assert "exponentiation is not defined on" in err(kc, f"assert {base}^0 = 1"), base
    # …while a base that really has arithmetic is untouched
    ok(kc, "assert 2^10 = 1024")
    ok(kc, "assert (1/2)^0 = 1")
    ok(kc, "assert (√2)^2 = 2")


def test_the_braced_exponent_is_an_exponent(kernel: Kernel) -> None:
    _, kc = kernel
    # `x^{k}` is the spelling this system's own LaTeX renderer produces and
    # the one SPEC.md writes its tolerance in, so it reads as the exponent
    ok(kc, "assert 10^{3} = 1000")
    ok(kc, "assert 2^{3} = 8")
    # …and a brace with more than one element is still SPEC.md's powerset `2^A`
    ok(kc, "assert |2^{1, 2, 3}| = 8")


def test_set_equality_stays_linear_on_sorted_sides(kernel: Kernel) -> None:
    _, kc = kernel
    # Two sorted sides of 9999 elements (a bounded progression expands to an
    # explicit list). Under a quadratic comparison this cell takes ~30s; the
    # zip settles it in one pass, so a regression shows up as a stall rather
    # than as a wrong answer.
    ok(kc, "assert {1, 2, ..., 9999} = {1, 2, ..., 9999}")


def test_i_is_a_constant_a_binding_shadows(kernel: Kernel) -> None:
    _, kc = kernel
    # `i` names the imaginary unit only while it is UNBOUND, exactly like the
    # `R` spelling of ℝ. Nothing below this test may read `i` as that constant.
    ok(kc, "let i := 5 in ℤ")
    ok(kc, "assert 2 + 2i = 12")
    ok(kc, "assert i = 5")


def test_a_binding_wins_over_the_indeterminate_reading(kernel: Kernel) -> None:
    _, kc = kernel
    # unbound, `z` would be the indeterminate of ℤ[z] exactly as `x` is above.
    # Bound, the brackets are an INDEX — the registered ℤ enumeration
    # 0, 1, −1, 2, −2, 3 — so no bound name is ever read as an indeterminate.
    ok(kc, "let z := 5 in ℤ")
    text = ok(kc, "ℤ[z]")
    assert "'3'" in text
    # …and the membership assertion asks about that integer, not about a ring
    text = err(kc, "assert z ∈ ℤ[z]")
    assert "'contains' is not a method" in text


# -- 17 · vectors and the linear action ---------------------------------------
# SPEC.md §Vectors and matrices' second and fourth blocks. `M` is the Mat₂(ℚ)
# bound in §4 above; `v` and `b` are SPEC.md's own names and appear nowhere
# else in this file. The inverse is Sage-routed, so these are the lines that
# cannot be decided at build time.

def test_matrix_vector_application_in_every_spelling(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let v := (1, 2) in ℚ²")
    ok(kc, "let b := (5, 11) in ℚ²")
    # SPEC.md writes the action three ways — explicitly, by juxtaposition, and
    # as a call — and all three are ONE operation
    ok(kc, "assert M*v = b")
    ok(kc, "assert M⁻¹ b = v")
    ok(kc, "assert M⁻¹(M v) = v")
    ok(kc, "assert M(M⁻¹ b) = b")
    # `M⁻¹` is the spelling of the `inverse` METHOD, not a second operation
    text = ok(kc, "M⁻¹")
    assert "-2, 1" in text and "3/2, -1/2" in text


def test_a_vector_is_typeset_as_the_tuple_it_is(kernel: Kernel) -> None:
    _, kc = kernel
    bd = bundle(kc, "v")
    # the conventions table's choice: the TUPLE, which is SPEC.md's own
    # spelling and the one the surface reads back — a column pmatrix would
    # typeset something the input syntax does not say
    assert bd["text/latex"] == "$$(1, 2)$$"
    assert bd["text/plain"] == "(1, 2)"
    assert bd["text/latex"].isascii()
    assert bundle(kc, "ℚ²")["text/latex"] == r"$$\mathbb{Q}^{2}$$"


def test_the_action_is_shape_checked_and_decides_the_wrong_vector(
        kernel: Kernel) -> None:
    _, kc = kernel
    # a matrix applies to vectors of its own size and to no other — the whole
    # reason a vector is not presented as a one-column matrix
    for code in ("assert M*(1, 0, 1) = b", "assert M((1, 0, 1)) = b"):
        text = err(kc, code)
        assert "does not apply to a vector of length 3" in text, code
    # …while a WRONG vector of the right shape is decided false, not refused
    text = err(kc, "assert M*v = (5, 12)")
    assert "false" in text.lower()
    assert "does not apply" not in text


# -- 18 · subspaces and spans -------------------------------------------------
# SPEC.md §Subspaces and spans, and the two §Vectors lines that read a matrix's
# echelon form. `u₁`, `u₂`, `W` are SPEC.md's own names and appear nowhere else.
# A subspace is presented by a REDUCED basis, which is what makes dim,
# membership and equality decidable from the presentation alone.

def test_rank_and_kernel_of_a_matrix(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "assert M.rank() = 2")
    ok(kc, "assert M.rank() ≠ 3")
    # SPEC.md's own `M.ker() = {0}`: an invertible matrix kills nothing, and
    # the trivial subspace IS the one-element set whose element is the zero of
    # the ambient space — which is what `0` spells there
    ok(kc, "assert M.ker() = {0}")
    text = ok(kc, "M.ker()")
    assert "span_ℚ{}" in text and "ℚ²" in text


def test_the_span_answers_dim_membership_and_equality(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let u₁ := (1, 0, 1) in ℚ³")
    ok(kc, "let u₂ := (0, 1, 1) in ℚ³")
    # SPEC.md's own line, `\leq` spelling included
    ok(kc, r"let W := span_QQ{u₁, u₂} \leq ℚ³ in QQ-Mod")
    ok(kc, "assert W.dim() = 2")
    ok(kc, "assert (1, 1, 2) ∈ W")
    ok(kc, "assert (1, 1, 0) ∉ W")
    # the ∉ line DECIDES false rather than refusing…
    text = err(kc, "assert (1, 1, 0) ∈ W")
    assert "false" in text.lower()
    # …and the display carries the reduced basis and the ambient
    bd = bundle(kc, "W")
    assert bd["text/plain"] == "span_ℚ{(1, 0, 1), (0, 1, 1)} ≤ ℚ³"
    assert bd["text/latex"] == (
        r"$$\mathrm{span}_{\mathbb{Q}}\{(1, 0, 1), (0, 1, 1)\} "
        r"\leq \mathbb{Q}^{3}$$")
    assert bd["text/latex"].isascii()


def test_the_subobject_ascription_is_checked(kernel: Kernel) -> None:
    _, kc = kernel
    # `\leq` means SUBOBJECT here (SPEC.md's own note), and the ambient is
    # checked rather than taken on trust
    text = err(kc, "let Wbad := span_QQ{u₁, u₂} ≤ ℚ² in QQ-Mod")
    assert "is not a subobject of ℚ²" in text
    # …the QQ-Mod ascription is a real membership judgment: a set that is not
    # a subspace is not in it
    text = err(kc, "let Wbad := {1, 2, 3} in QQ-Mod")
    assert "QQ-Mod" in text and "«" not in text
    # …and only SPEC.md's own span spelling is a construction
    text = err(kc, "span_ZZ{u₁}")
    assert "span_QQ" in text


def test_the_subspace_is_a_set_and_a_qq_module(kernel: Kernel) -> None:
    _, kc = kernel
    # both memberships are real and INDEPENDENT: the set methods reach it
    # through the ordinary hierarchy, `dim` through QQ-Mod
    ok(kc, "assert span_QQ{u₁} ⊆ W")
    ok(kc, "assert W = span_QQ{(1, 1, 2), (0, 1, 1)}")
    ok(kc, "assert W ≠ span_QQ{(1, 0, 0), (0, 1, 1)}")
    ok(kc, "assert |W| = ℵ₀")
    text = ok(kc, "#explain_route W.dim()")
    assert "QQ-Mod" in text and "native" in text and "span_dim" in text
    assert "«" not in text


# -- 19 · the companion matrix, charpoly and trace ----------------------------
# SPEC.md §A composed computation's second block. `r` and `C` are SPEC.md's own
# names and appear nowhere else. Mat₃(ℚ) is the first matrix past 2×2 to reach
# the routed ℚ ops, so `det` is exercised at that size here too.

def test_companion_matrix_charpoly_and_trace(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let r(x) := x³ - 2x + 1 in ℚ[x]")
    ok(kc, "let C := r.companion_matrix()")
    # SPEC.md's three assertions, verbatim
    ok(kc, "assert C.charpoly() = r")
    ok(kc, "assert C.det() = -1")
    ok(kc, "assert C.trace() = 0")
    # …and the wrong answers each of them must reject (a bare `x` is unbound
    # outside a polynomial binding, so the wrong polynomial is bound to a name)
    ok(kc, "let rwrong(x) := x³ - 2x in ℚ[x]")
    ok(kc, "assert C.charpoly() ≠ rwrong")
    ok(kc, "assert C.det() ≠ 1")
    ok(kc, "assert C.trace() ≠ 1")
    # the companion matrix has the polynomial's own size, and lands in Mat₃(ℚ)
    # — the first matrix past 2×2 to reach the routed ℚ ops
    assert bundle(kc, "C")["text/plain"].count(";") == 2


def test_the_trace_reaches_where_det_gaps(kernel: Kernel) -> None:
    _, kc = kernel
    # the trace is a structural read of the diagonal, so it is native and
    # defined over every entry domain — while `det` over ℤ/5 stays the
    # deliberate gap. Two judgments, one object.
    ok(kc, "let Cm5 := [1, 2; 3, 4] in Mat₂(ℤ/5)")
    ok(kc, "assert Cm5.trace() = 0")
    text = err(kc, "Cm5.det()")
    assert "NoImplementation" in text
    text = err(kc, "Cm5.charpoly()")
    assert "NoImplementation" in text


# -- 20 · the root set, and Σ / Π over it -------------------------------------
# SPEC.md §A composed computation's first block, verbatim. `r` is the ℚ[x]
# cubic bound in §19; `roots` appears nowhere else in this file.

def test_the_root_set_over_c_and_its_aggregations(kernel: Kernel) -> None:
    _, kc = kernel
    ok(kc, "let roots := {a ∈ ℂ | r(a) = 0} in 𝒫(ℂ)")
    ok(kc, "assert |roots| = 3")
    ok(kc, "assert 1 ∈ roots")
    ok(kc, "assert ∑_{a ∈ roots} a = 0")
    ok(kc, "assert ∏_{a ∈ roots} a = -1")
    # the roots are EXACT surds, not decimals — asserted as the rendering it
    # is rather than by hunting for an absent "." in a slice of the output
    assert bundle(kc, "roots")["text/plain"] == "{-1/2 - (1/2)√5, -1/2 + (1/2)√5, 1}"


def test_the_index_domain_decides_where_the_roots_are_sought(
        kernel: Kernel) -> None:
    _, kc = kernel
    # `{a ∈ D | p(a) = 0}` seeks the solutions IN D — over ℚ the cubic has one
    # root and over ℂ it has three. That is the mathematics, not a default
    ok(kc, "assert {a ∈ ℚ | r(a) = 0} = {1}")
    ok(kc, "assert |{a ∈ ℂ | r(a) = 0}| = 3")
    # an equation with a non-zero right side is the same operation
    ok(kc, "assert 0 ∈ {a ∈ ℚ | r(a) = 1}")
    # …and the guarded comprehension is untouched: `=` is still not a
    # term-level comparison, so a guard is still an ORDER comparison
    ok(kc, "assert {n ∈ ℤ | n² ≤ 4} = {-2, -1, 0, 1, 2}")


def test_the_multi_binder_lambda_is_a_named_gap(kernel: Kernel) -> None:
    _, kc = kernel
    # SPEC.md §Subspaces and spans' last block needs a lambda in three
    # variables, which the univariate polynomial engine cannot express. It is
    # refused as a GAP that names itself and says what it blocks — never as a
    # syntax error, and never approximated.
    text = err(kc, "let φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c")
    assert "disclosed GAP" in text
    assert "ker φ" in text
    # …and the single-binder lambda it did not break
    ok(kc, "let φ1 := t ↦ t + 1 in ℚ[x]")


def test_the_and_chain_survives_identifier_conjuncts(kernel: Kernel) -> None:
    _, kc = kernel
    # `and` is an identifier token, so the juxtaposition production would eat
    # it as an argument. Every conjunct here ENDS in a name — the shape the
    # committed `and` chains (all over domain tokens) never exercised.
    ok(kc, "assert v = v and b = b")
    ok(kc, "assert M v = b and v = v")
    # …and a chain still NAMES the conjunct that failed rather than reporting
    # a bare "false", with identifier conjuncts too
    text = err(kc, "assert v = v and v = b")
    assert "v = b" in text and "of v = v and v = b" in text


def test_the_juxtaposition_residual_has_a_workaround(kernel: Kernel) -> None:
    _, kc = kernel
    # An identifier token following an identifier token is an application
    # wherever the two sit, so a statement ending in a name joins a following
    # one that begins with a name…
    ok(kc, "let jx := 5 in ℤ")
    text = err(kc, "jx\njx")
    assert "not callable" in text
    # …and parenthesizing the following statement is the workaround, because
    # `(` is not an identifier token
    ok(kc, "jx\n(jx)")
