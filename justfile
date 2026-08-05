# lean-cas-dsl — categorically organized CAS in Lean, an nbdsl DSL plugin.
#
# One Lake package (library CasDsl + prelude CasDsl.Notebook) over the
# nbdsl-worker core, plus the Python half of the Sage adapter
# (backends/sage_adapter.py, runs under `sage -python`). Lake owns
# compilation; language-level QC delegates to the global gates.
#
# Not adopted: lean-axiom-audit — it requires a target-private
# _lean-axiom-audit budget recipe, and this package has no audited axiom
# budget yet (same posture as lean-jupyter-kernel; revisit alongside its
# proof-status work).

set dotenv-load := true

# Show available recipes
default:
    @just --list

# Build the CasDsl library (and the worker it depends on)
build:
    @lake build CasDsl CasDslTests nbdsl_worker

# One-time dev setup: Mathlib cache, venv, kernel adapter, casdsl kernelspec
setup:
    @lake exe cache get
    @uv venv .venv
    @uv pip install -p .venv/bin/python nbclient \
        'nbdsl-kernel[test] @ git+https://github.com/dzackgarza/lean-jupyter-kernel@main#subdirectory=nbdsl_kernel'
    @.venv/bin/python -m nbdsl_kernel.install --project "$PWD" \
        --prelude-module CasDsl.Notebook --name casdsl --display-name "CasDsl (Lean 4)"

# Moves the lake dependency on nbdsl-worker to the latest kernel repo commit
# and reinstalls the Python kernel adapter to match, so a stale
# .lake/packages/nbdsl-worker or venv never serves old kernel code to the
# notebook re-exec (test-push runs this first for that reason). Restarting
# the open casdsl notebooks makes JupyterLab pick up the fresh install; a
# notebook that fails to restart fails the recipe. The JupyterLab federated
# extension converges too, copied from the same Lake checkout rev into
# ~/.local/share/jupyter/labextensions (a browser reload picks it up).
# Sync the installed casdsl kernel + lab extension to the latest nbdsl-worker
sync-kernel:
    @lake update nbdsl-worker
    @lake build nbdsl_worker
    @uv pip install -p .venv/bin/python --reinstall-package nbdsl-kernel \
        'nbdsl-kernel[test] @ git+https://github.com/dzackgarza/lean-jupyter-kernel@main#subdirectory=nbdsl_kernel'
    @.venv/bin/python -m nbdsl_kernel.install --project "$PWD" \
        --prelude-module CasDsl.Notebook --name casdsl --display-name "CasDsl (Lean 4)"
    @for nb in $(/home/dzack/gitclones/jupyter-assistant-api/japi list-notebooks --format json 2>/dev/null | jq -r '.result' | rg 'cas-dsl/.*\.ipynb' | cut -f1); do \
      /home/dzack/gitclones/jupyter-assistant-api/japi restart-notebook "$nb" '{"kernel_name": "casdsl"}'; \
    done
    @mkdir -p ~/.local/share/jupyter/labextensions
    @rsync -a --delete \
        .lake/packages/nbdsl-worker/jupyterlab_nbdsl/jupyterlab_nbdsl/labextension/ \
        ~/.local/share/jupyter/labextensions/jupyterlab_nbdsl/
    @cp .lake/packages/nbdsl-worker/jupyterlab_nbdsl/install.json \
        ~/.local/share/jupyter/labextensions/jupyterlab_nbdsl/install.json

# The full suite (Sage roundtrip + E2E) runs under `test-ci`; this is the
# commit gate and must stay fast.
# The worker's oleans are toolchain-bound, so this repo and the kernel repo
# must pin the same Lean (release.toml there is the source of truth). The
# diff below fails the gate loudly on drift, naming both pins.
# Run the QC preflight: compile Lean and the Python adapter, then the Lean laws.
test: build
    @diff -u .lake/packages/nbdsl-worker/worker/lean-toolchain lean-toolchain
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-no-sorry
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-semgrep
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

# Re-execute the committed notebooks (demo + boundaries) against the live
# casdsl kernel: outputs stay genuine kernel output (a23ee30 standard) and
# the runnable-trail rule holds — a live error cell fails this gate, since
# the document model would block every cell below it.
[private]
_notebook-reexec:
    @.venv/bin/python scripts/reexec_notebooks.py

[private]
test-push: sync-kernel test-ci _notebook-reexec
