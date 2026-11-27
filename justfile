
set dotenv-load := true

default:
    @just --list

track-main:
    @python3 scripts/ci_chain.py
    @python3 scripts/resolve_lake_if_needed.py

cache +modules:
    @lake exe cache get {{modules}}

[positional-arguments]
loop targets *acceptance:
    @scripts/feedback.sh loop "$@"

[positional-arguments]
slow reason +targets:
    @scripts/feedback.sh slow "$@"

milestone reason:
    @scripts/feedback.sh milestone {{quote(reason)}}

stop:
    @scripts/feedback.sh stop

[private]
[positional-arguments]
test-feedback *tests:
    #!/usr/bin/env bash
    set -euo pipefail
    source scripts/container.sh
    incontainer python3 -S tests/feedback/test_feedback.py "$@" -v

profile target:
    #!/usr/bin/env bash
    set -euo pipefail
    source={{quote(target)}}
    if [[ "$source" != *.lean ]]; then source="${source//.//}.lean"; fi
    log=$(mktemp "${TMPDIR:-/tmp}/lean-cas-profile.XXXXXX.log")
    echo "Profile log: $log"
    lake lean "$source" -- --profile 2>&1 | tee "$log"

probe source:
    @python3 -S scripts/feedback_records.py probe {{quote(source)}}

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

build-production:
    @lake build +CasRuntime.Session:olean

setup-sdk contracts=".lake/packages/cas_leaf_contracts":
    #!/usr/bin/env bash
    set -euo pipefail
    contracts=${CAS_LEAF_CONTRACT_PATH:-{{quote(contracts)}}}
    uv sync --frozen --project "$contracts"

audit-production:
    @lake env lake build +CasGates.Production:olean +CasGates.KernelPurityProbes:olean

protocol-v2 contracts:
    @uv run --project "{{contracts}}" python scripts/test_protocol_v2.py "{{contracts}}"

build: _integration-intent
    @python3 -m unittest discover -s scripts -p 'test_*.py'
    @python3 scripts/check_no_leaves.py --self-test
    @python3 scripts/check_no_leaves.py
    @python3 scripts/check_reuse_records.py
    @python3 scripts/check_acceptance_permanent.py
    @just build-production
    @just setup-sdk
    @lake build +CasCompilerTests:olean
    @lake build +CasRuntimeTests:olean
    @just audit-production
    @lake env lake build CasCatalogue CasGates CasAcceptance CasTools CasDsl CasDslTests cas-registry-export cas-axiom-audit cas-harness

harness *manifest="": track-main
    @lake build cas-harness
    @mkdir -p .tmp
    @CAS_SAGE_PYTHON="${CAS_SAGE_PYTHON:-$PWD/.venv/bin/python}" CAS_GAP_PYTHON="${CAS_GAP_PYTHON:-$PWD/.venv/bin/python}" lake exe cas-harness --report .tmp/harness.json {{ if manifest == "" { "" } else { "--manifest " + manifest } }}

acceptance base: track-main
    @lake build cas-harness
    @mkdir -p .tmp
    @rm -f .tmp/harness.json
    -@CAS_SAGE_PYTHON="${CAS_SAGE_PYTHON:-$PWD/.venv/bin/python}" CAS_GAP_PYTHON="${CAS_GAP_PYTHON:-$PWD/.venv/bin/python}" lake exe cas-harness --report .tmp/harness.json
    @python3 scripts/check_acceptance_regression.py {{ base }} .tmp/harness.json
    @python3 scripts/check_question_permanence.py --base CasAcceptance/Permanent/questions.json .tmp/harness.json

setup:
    @lake exe cache get
    @uv venv .venv
    @uv pip install -p .venv/bin/python nbclient \
        'nbdsl-kernel[test] @ git+https://github.com/dzackgarza/lean-jupyter-kernel@main#subdirectory=nbdsl_kernel'
    @.venv/bin/python -m nbdsl_kernel.install --project "$PWD" \
        --prelude-module CasDsl.Notebook --session-mode language --name casdsl --display-name "CasDsl (Lean 4)"

sync-kernel:
    @lake update nbdsl-worker
    @lake build nbdsl_worker
    @uv pip install -p .venv/bin/python --reinstall-package nbdsl-kernel \
        'nbdsl-kernel[test] @ git+https://github.com/dzackgarza/lean-jupyter-kernel@main#subdirectory=nbdsl_kernel'
    @.venv/bin/python -m nbdsl_kernel.install --project "$PWD" \
        --prelude-module CasDsl.Notebook --session-mode language --name casdsl --display-name "CasDsl (Lean 4)"
    @for nb in $(/home/dzack/gitclones/jupyter-assistant-api/japi list-notebooks --format json 2>/dev/null | jq -r '.result' | rg 'cas-dsl/.*\.ipynb' | cut -f1); do \
      /home/dzack/gitclones/jupyter-assistant-api/japi restart-notebook "$nb" '{"kernel_name": "casdsl"}'; \
    done
    @mkdir -p ~/.local/share/jupyter/labextensions
    @rsync -a --delete \
        .lake/packages/nbdsl-worker/jupyterlab_nbdsl/jupyterlab_nbdsl/labextension/ \
        ~/.local/share/jupyter/labextensions/jupyterlab_nbdsl/
    @cp .lake/packages/nbdsl-worker/jupyterlab_nbdsl/install.json \
        ~/.local/share/jupyter/labextensions/jupyterlab_nbdsl/install.json

test: build
    @lake exe cas-axiom-audit
    @lake exe cas-registry-export > /dev/null
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-no-sorry
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-semgrep
    @python3 -m py_compile CasAcceptance/Strata/probe_registration.py

[private]
_test-full:
    @.venv/bin/python scripts/reexec_notebooks.py

test-ci: test _test-full

[private]
test-commit:
    @just -f ~/ai-review-ci/justfiles/lean.just -d . test-commit

[private]
_notebook-reexec:
    #!/usr/bin/env bash
    set -euo pipefail
    .venv/bin/python scripts/reexec_notebooks.py
    if ! git diff --quiet -- notebooks/demo.ipynb; then
        git add notebooks/demo.ipynb
        git commit -m "chore: notebook session metadata"
    fi

[private]
test-push:
    @just -f ~/ai-review-ci/justfiles/lean.just -d . test-push
