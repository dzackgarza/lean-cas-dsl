# lean-cas-dsl — categorically organized CAS in Lean, an nbdsl DSL plugin.
#
# One Lake package (library CasDsl + prelude CasDsl.Notebook) over the
# nbdsl-worker core. The leaves (`lean-cas-dsl-leaves`) are not a Lake
# dependency: a leaf is a manifest `leaves.json` of registrations and the
# programs it names, found through `CAS_LEAVES` (or `.lake/packages/cas_leaves`),
# written against the leaf contract (`lean-cas-dsl-leaf-contracts`). Lake owns
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

# Build the core and the notebook package, and run their probes: the acceptance probes and the
# suite (CasAcceptance), the notebook boundary and the demo notebook's cells (CasDslTests).
# Permanent acceptance assertions are append-only (scripts/check_acceptance_permanent.py), and
# authors are separated by layer across the chain (scripts/check_authorship.py).
build:
    @python3 scripts/check_authorship.py --self-test
    @python3 scripts/check_authorship.py
    @python3 scripts/check_no_leaves.py --self-test
    @python3 scripts/check_no_leaves.py
    @python3 scripts/check_reuse_records.py
    @python3 scripts/check_acceptance_permanent.py
    @lake build CasCatalogue CasGates CasAcceptance CasTools CasDsl CasDslTests cas-registry-export cas-axiom-audit cas-harness

# Run the acceptance suite over a leaves manifest (default: the installed leaves', through
# `CAS_LEAVES` or `.lake/packages/cas_leaves`); writes every result to .tmp/harness.json. Gaps are
# the report, not failures.
harness *manifest="":
    @lake build cas-harness
    @mkdir -p .tmp
    @lake exe cas-harness --report .tmp/harness.json {{ if manifest == "" { "" } else { "--manifest " + manifest } }}

# One-time dev setup: Mathlib cache, venv, kernel adapter, casdsl kernelspec. The leaves' engines
# (Sage, GAP, …) are the leaves' own (`lean-cas-dsl-leaves`), installed with them.
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

# Lean compilation runs in CI only (.github/workflows/gates.yml): the commit
# and push tiers are static scans.
# Build everything, then run the audits and the Lean laws.
test: build
    @lake exe cas-axiom-audit
    @lake exe cas-registry-export > /dev/null
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-no-sorry
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-semgrep
    @python3 -m py_compile CasAcceptance/Strata/probe_registration.py

# Drives the installed casdsl kernelspec (`just setup` first) through the demo notebook.
[private]
_test-full:
    @.venv/bin/python scripts/reexec_notebooks.py

# Run the full QC gate: the preflight, then the demo notebook through the live kernel.
test-ci: test _test-full

# Scan staged Lean source; the permanent assertions stay append-only.
[private]
test-commit:
    @just -f ~/ai-review-ci/justfiles/lean.just -d . test-commit
    @python3 scripts/check_acceptance_permanent.py

# Re-execute the committed notebook against the live casdsl kernel:
# outputs stay genuine kernel output (a23ee30 standard). The demo is a
# runnable trail — a live error cell fails this gate, since the document
# model would block every cell below it. The re-executed notebook — execution
# timestamps included, they are the provenance of the genuine outputs —
# are committed here; the push in flight proceeds, and the commit rides
# the next one.
[private]
_notebook-reexec:
    #!/usr/bin/env bash
    set -euo pipefail
    .venv/bin/python scripts/reexec_notebooks.py
    if ! git diff --quiet -- notebooks/demo.ipynb; then
        git add notebooks/demo.ipynb
        git commit -m "chore: notebook session metadata"
    fi

# Static Lean scans before push; no compilation.
[private]
test-push:
    @just -f ~/ai-review-ci/justfiles/lean.just -d . test-push
    @python3 scripts/check_acceptance_permanent.py
    @python3 -m py_compile CasAcceptance/Strata/probe_registration.py
