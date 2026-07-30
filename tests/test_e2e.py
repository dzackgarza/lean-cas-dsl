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


# -- 9 · registry-driven embeddings -----------------------------------------

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
    # q ∈ ℚ[x] from the polynomial test; ℚ → ℤ is not a registered embedding
    text = err(kc, "map q to ℤ[x]")
    assert "no preferred canonical map" in text
