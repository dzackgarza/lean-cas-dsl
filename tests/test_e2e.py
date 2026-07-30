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
    # SPEC.md §Differentials' ℚ[x] polynomial. (SPEC spells the leading term
    # `3x²`; implicit multiplication binds tighter than the superscript in
    # this grammar, so the product is written out — `f(2) = 15` is SPEC's own
    # check that this is the intended polynomial.)
    ok(kc, "let f := x ↦ 3*x² + x + 1 in ℚ[x]")
    ok(kc, "assert f(2) = 15")
    ok(kc, "assert f.deg() = 2")


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


def test_typed_colon_ascription_spelling(kernel: Kernel) -> None:
    _, kc = kernel
    text = ok(kc, "let e: ℕ → ℕ := n ↦ 2n")
    assert "n ↦ 2n" in text and "ℕ → ℕ" in text


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


def test_body_the_polynomial_engine_cannot_express_is_refused(kernel: Kernel) -> None:
    _, kc = kernel
    # a value, but not one `asPolyCoeffs` reads
    text = err(kc, "let bad := t ↦ [1, 2; 3, 4] in ℝ → ℝ")
    assert "[1, 2; 3, 4] is not a polynomial body" in text
    # not an element value at all
    text = err(kc, "let bad2 := t ↦ ℕ in ℝ → ℝ")
    assert "ℕ is not a function body" in text


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
    # a domain inclusion is the canonical-map registry's claim, and the set
    # layer refuses to restate it rather than answering it twice
    text = err(kc, "assert ℕ ⊆ ℤ")
    assert "canonical-map registry" in text


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
