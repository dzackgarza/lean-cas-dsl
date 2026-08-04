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
        'nbdsl-kernel[test] @ git+https://github.com/dzackgarza/lean-jupyter-kernel@main#subdirectory=nbdsl_kernel'
    @.venv/bin/python -m nbdsl_kernel.install --project "$PWD" \
        --prelude-module CasDsl.Notebook --name casdsl --display-name "CasDsl (Lean 4)"

# Sync the lake dependency on nbdsl-worker to the latest kernel repo commit
# and reinstall the Python kernel adapter, so the installed kernel matches
# the worker the lake build just compiled. Run before test-push so a stale
# .lake/packages/nbdsl-worker or venv never serves old kernel code to the
# notebook re-exec. Also kill any running nbdsl kernel processes so
# JupyterLab restarts them from the fresh install on the next cell run.
sync-kernel:
    @lake update nbdsl-worker
    @lake build nbdsl_worker
    @uv pip install -p .venv/bin/python --reinstall-package nbdsl-kernel \
        'nbdsl-kernel[test] @ git+https://github.com/dzackgarza/lean-jupyter-kernel@main#subdirectory=nbdsl_kernel'
    @.venv/bin/python -m nbdsl_kernel.install --project "$PWD" \
        --prelude-module CasDsl.Notebook --name casdsl --display-name "CasDsl (Lean 4)"
    @-pkill -f "python.*nbdsl_kernel.*connection_file" 2>/dev/null || true
    @-pkill -f "nbdsl_worker --req-fd" 2>/dev/null || true

# The full suite (Sage roundtrip + E2E) runs under `test-ci`; this is the
# commit gate and must stay fast.
# Run the QC preflight: compile Lean and the Python adapter, then the Lean law.
test: build
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-no-sorry
    @python3 -m py_compile backends/sage_adapter.py tests/roundtrip.py

[private]
_test-full:
    @python3 tests/roundtrip.py
    @.venv/bin/pytest tests/test_e2e.py -q

# Talks to real Sage and drives the installed casdsl kernelspec
# (`just setup` first); the full suite behind it is `_test-full`.
# Run the full QC gate: the preflight, the Sage roundtrip, and the E2E suite.
test-ci: test _test-full

[private]
test-commit: test

# Re-execute the demo notebook against the live casdsl kernel so committed
# outputs are genuine kernel output (a23ee30 standard), never hand-written.
[private]
_notebook-reexec:
    @.venv/bin/python scripts/reexec_demo.py

[private]
test-push: sync-kernel test-ci _notebook-reexec
