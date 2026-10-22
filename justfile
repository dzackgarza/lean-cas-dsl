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

# Refresh own-organisation checkouts to latest main and resolve changed Lake requires.
track-main:
    @python3 scripts/ci_chain.py
    @python3 scripts/resolve_lake_if_needed.py

# Build one Lean target and automatically profile it if slow; mode=profile profiles a source.
focus target mode="build": track-main
    #!/usr/bin/env bash
    set -euo pipefail
    target={{quote(target)}}
    mode={{quote(mode)}}
    diagnosed=0
    if [[ "$mode" == "diagnosed" ]]; then
      if [[ -z "${B0_PRIOR_PROFILE_LOG:-}" ]]; then
        echo "Diagnosed build requires B0_PRIOR_PROFILE_LOG from a completed profile." >&2
        exit 2
      fi
      if [[ ! -s "$B0_PRIOR_PROFILE_LOG" ]]; then
        echo "Prior profile must be a nonempty readable log: $B0_PRIOR_PROFILE_LOG" >&2
        exit 2
      fi
      if ! rg -q 'cumulative profiling times:' "$B0_PRIOR_PROFILE_LOG"; then
        echo "Diagnosed build requires B0_PRIOR_PROFILE_LOG from a completed profile." >&2
        exit 2
      fi
      diagnosed=1
      mode=build
      echo "Using prior target profile: $B0_PRIOR_PROFILE_LOG"
    fi
    budget=${B0_FOCUS_BUDGET_SECONDS:-120}
    if [[ ! "$budget" =~ ^[1-9][0-9]*$ ]]; then
      echo "B0_FOCUS_BUDGET_SECONDS must be a positive integer" >&2
      exit 2
    fi
    if (( budget > 120 && diagnosed == 0 )) && [[ "$mode" == "build" ]]; then
      echo "A build budget above 120s requires a completed target profile; use profile first, then diagnosed mode." >&2
      exit 2
    fi
    if [[ "$target" == *.lean ]]; then
      source=$target
      module=${target%.lean}
      module=${module//\//.}
    else
      module=$target
      source=${target//.//}.lean
    fi
    if (( diagnosed == 1 )); then
      prior_target=$(cat "${B0_PRIOR_PROFILE_LOG}.target")
      if [[ "$prior_target" != "$module" ]]; then
        echo "Prior profile must be tagged for $module." >&2
        exit 2
      fi
    fi
    log=$(mktemp /tmp/lean-cas-focus.XXXXXX.log)
    started=$(date +%s)
    set +e
    case "$mode" in
      profile) timeout --signal=TERM --kill-after=5s "${budget}s" \
          /usr/bin/time -f 'elapsed_seconds=%e peak_rss_kib=%M' \
          lake env lean --profile "$source" 2>&1 | tee "$log" >/dev/null ;;
      build) timeout --signal=TERM --kill-after=5s "${budget}s" \
          /usr/bin/time -f 'elapsed_seconds=%e peak_rss_kib=%M' \
          lake build "$module" 2>&1 | tee "$log" >/dev/null ;;
      *) echo "mode must be profile or build" >&2; exit 2 ;;
    esac
    result=${PIPESTATUS[0]}
    set -e
    if [[ "$mode" == "profile" && "$result" == 0 ]]; then
      printf '%s\n' "$module" > "${log}.target"
    fi
    echo "Focused log: $log"
    if (( result == 0 )); then
      if [[ "$mode" == "profile" ]]; then tail -n 27 "$log"
      else rg 'Built |Build completed|elapsed_seconds=' "$log" | tail -n 8
      fi
    else
      tail -n 30 "$log"
    fi
    elapsed=$(($(date +%s) - started))
    if (( result == 124 )); then
      echo "Focused $mode exceeded ${budget}s. Diagnose the target before increasing B0_FOCUS_BUDGET_SECONDS." >&2
    fi
    if (( elapsed >= 60 )); then
      case "$mode:$diagnosed:$result" in
        build:0:0|build:0:124)
        if [[ -f "$source" ]]; then
          profile_log=$(mktemp /tmp/lean-cas-profile.XXXXXX.log)
          set +e
          timeout --signal=TERM --kill-after=5s "${budget}s" \
            /usr/bin/time -f 'elapsed_seconds=%e peak_rss_kib=%M' \
            lake env lean --profile "$source" 2>&1 | tee "$profile_log" >/dev/null
          profile_result=${PIPESTATUS[0]}
          set -e
          if (( profile_result == 0 )); then
            printf '%s\n' "$module" > "${profile_log}.target"
          fi
          echo "Profile log: $profile_log"
          tail -n 27 "$profile_log"
          if (( profile_result == 124 )); then
            echo "Profile exceeded ${budget}s; reduce the reproducer or inspect the import boundary." >&2
          fi
          if (( result == 0 )); then result=$profile_result; fi
        fi
        ;;
      esac
      echo "Slow target ($elapsed s): inspect the profile and import costs before another source iteration." >&2
    fi
    exit "$result"

# Run a bounded import-only Lean reproducer from /tmp before another slow source edit.
probe source: track-main
    #!/usr/bin/env bash
    set -euo pipefail
    source={{quote(source)}}
    if [[ "$source" != /tmp/*.lean ]]; then
      echo "Probe source must be an existing /tmp/*.lean file." >&2
      exit 2
    fi
    if [[ ! -f "$source" ]]; then
      echo "Probe source must be an existing /tmp/*.lean file." >&2
      exit 2
    fi
    budget=${B0_PROBE_BUDGET_SECONDS:-60}
    if [[ ! "$budget" =~ ^[1-9][0-9]*$ ]]; then
      echo "B0_PROBE_BUDGET_SECONDS must be a positive integer" >&2
      exit 2
    fi
    log=$(mktemp /tmp/lean-cas-probe.XXXXXX.log)
    echo "Probe log: $log"
    set +e
    timeout --signal=TERM --kill-after=5s "${budget}s" \
      /usr/bin/time -f 'elapsed_seconds=%e peak_rss_kib=%M' \
      lake env lean "$source" 2>&1 | tee "$log"
    result=${PIPESTATUS[0]}
    set -e
    if (( result == 124 )); then
      echo "Probe exceeded ${budget}s; shrink the reproducer before another source edit." >&2
    fi
    exit "$result"

# Measure an unchanged admitted assertion through the requested production stage.
bench-question assertion="matrices.kernel" source="benchmarks/question_identity.lean": track-main
    #!/usr/bin/env bash
    set -euo pipefail
    budget=${B0_BENCH_BUDGET_SECONDS:-180}
    if [[ ! "$budget" =~ ^[1-9][0-9]*$ ]]; then
      echo "B0_BENCH_BUDGET_SECONDS must be a positive integer" >&2
      exit 2
    fi
    log=$(mktemp /tmp/lean-cas-question.XXXXXX.log)
    echo "Benchmark log: $log"
    for package in . lean_categories cas_leaf_contracts cas_leaves nbdsl-worker; do
      if [[ "$package" == . ]]; then
        checkout=.
      else
        checkout=".lake/packages/$package"
      fi
      echo "revision[$package]=$(git -C "$checkout" rev-parse HEAD)" | tee -a "$log"
    done
    if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
      echo "source_worktree=dirty" | tee -a "$log"
    else
      echo "source_worktree=clean" | tee -a "$log"
    fi
    set +e
    CAS_BENCH_ONCE=1 CAS_BENCH_ASSERTION={{quote(assertion)}} \
      timeout --signal=TERM --kill-after=5s "${budget}s" \
      /usr/bin/time -f 'elapsed_seconds=%e peak_rss_kib=%M' \
      lake env lean {{quote(source)}} 2>&1 | tee -a "$log"
    result=${PIPESTATUS[0]}
    set -e
    if (( result == 124 )); then
      echo "Benchmark exceeded ${budget}s; inspect per-binding timings in $log." >&2
    fi
    exit "$result"

# Fast semantic-reading diagnostic; the full question benchmark still checks identity.
bench-reading assertion="matrices.kernel":
    @just bench-question {{quote(assertion)}} benchmarks/semantic_reading.lean

[private]
_integration-intent:
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ "${GITHUB_ACTIONS:-}" == "true" ]]; then exit 0; fi
    if [[ "${B0_INTEGRATION:-}" != "1" ]]; then
      echo "Full build is for integration candidates. Use 'just focus SOURCE' first; set B0_INTEGRATION=1 for the final gate." >&2
      exit 2
    fi
    if [[ -n "$(git status --porcelain)" ]]; then
      echo "Full build requires a clean committed candidate. Use 'just focus SOURCE' while editing." >&2
      exit 2
    fi

# Build and statically check a clean integration candidate (CI or B0_INTEGRATION=1).
build: _integration-intent track-main
    @python3 -m unittest discover -s scripts -p 'test_*.py'
    @python3 scripts/check_no_leaves.py --self-test
    @python3 scripts/check_no_leaves.py
    @python3 scripts/check_reuse_records.py
    @python3 scripts/check_acceptance_permanent.py
    @lake build CasCatalogue CasGates CasAcceptance CasTools CasDsl CasDslTests cas-registry-export cas-axiom-audit cas-harness

# Run the acceptance suite over a leaves manifest (default: the installed leaves', through
# `CAS_LEAVES` or `.lake/packages/cas_leaves`); writes every result to .tmp/harness.json. Gaps are
# the report, not failures.
harness *manifest="": track-main
    @lake build cas-harness
    @mkdir -p .tmp
    @CAS_SAGE_PYTHON="${CAS_SAGE_PYTHON:-$PWD/.venv/bin/python}" CAS_GAP_PYTHON="${CAS_GAP_PYTHON:-$PWD/.venv/bin/python}" lake exe cas-harness --report .tmp/harness.json {{ if manifest == "" { "" } else { "--manifest " + manifest } }}

# Run the suite here and compare it with the base run `base` (a report of `cas-harness`),
# assertion by assertion (`scripts/check_acceptance_regression.py`): an assertion of the base that is
# missing here, one that the base did not fail and fails here, and a new one that fails here,
# each fail the comparison. The harness exits nonzero whenever an assertion fails, so its exit
# does not decide; its report does, and a run that did not complete writes none (the stale
# report is removed first).
acceptance base: track-main
    @lake build cas-harness
    @mkdir -p .tmp
    @rm -f .tmp/harness.json
    -@CAS_SAGE_PYTHON="${CAS_SAGE_PYTHON:-$PWD/.venv/bin/python}" CAS_GAP_PYTHON="${CAS_GAP_PYTHON:-$PWD/.venv/bin/python}" lake exe cas-harness --report .tmp/harness.json
    @python3 scripts/check_acceptance_regression.py {{ base }} .tmp/harness.json
    @python3 scripts/check_question_permanence.py --base CasAcceptance/Permanent/questions.json .tmp/harness.json

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
# notebook re-exec (explicit sync-kernel setup, never a local push gate). Restarting
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

# Local commit checks validate staged syntax only. The permanent assertions
# remain append-only and are audited by the CI-only Gates workflow.
[private]
test-commit:
    @just -f ~/ai-review-ci/justfiles/lean.just -d . test-commit

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

# Local push inspects outgoing committed syntax, without CI-only audits.
[private]
test-push:
    @just -f ~/ai-review-ci/justfiles/lean.just -d . test-push
