# lean-cas-dsl — categorically organized CAS in Lean, an nbdsl DSL plugin.
#
# One Lake package (library CasDsl + prelude CasDsl.Notebook) over the
# nbdsl-worker core, plus the Python half of the Sage adapter
# (backends/sage_adapter.py, runs under `sage -python`). Lake owns
# compilation; language-level QC delegates to the global gates.

set dotenv-load := true

# Show available recipes
default:
    @just --list

# Fetch Mathlib's prebuilt compilation cache
cache:
    @lake exe cache get

# Build the CasDsl library (and the worker it depends on)
build:
    @lake build CasDsl CasDslTests nbdsl_worker

# One-time dev setup: venv, kernel adapter, casdsl kernelspec
setup:
    @uv venv .venv
    @uv pip install -p .venv/bin/python nbclient \
        'nbdsl-kernel[test] @ git+https://github.com/dzackgarza/lean-jupyter-kernel@92c0caefb9587f4fee0a0e67e79afd91c8cb4f49#subdirectory=nbdsl_kernel'
    @.venv/bin/python -m nbdsl_kernel.install --project "$PWD" \
        --prelude-module CasDsl.Notebook --name casdsl --display-name "CasDsl (Lean 4)"

# Run the repository QC gate (roundtrip talks to real Sage; E2E drives the
# installed casdsl kernelspec — `just setup` first)
test: build
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-no-sorry
    @python3 -m py_compile backends/sage_adapter.py tests/roundtrip.py
    @python3 tests/roundtrip.py
    @.venv/bin/pytest tests/test_e2e.py -q

[private]
test-commit: test

# Run the CI quality gate
test-ci: test

[private]
test-push: test-ci
