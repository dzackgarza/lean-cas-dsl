#!/usr/bin/env bash
set -euo pipefail
invocation=(scripts/feedback.sh "$@")
now() { python3 -S -c 'import time; print(time.monotonic_ns())'; }
started=$(now)
cd "$(dirname "$0")/.."
limit=300
records=timing/runs.jsonl
die() { printf 'feedback: %s\n' "$*" >&2; exit 2; }
usage() {
  printf '%s\n' \
    'Current-source feedback (C21/C24). Called by just loop, slow, milestone and stop.' \
    'loop "MODULE ..." [STEM | --extension STEM ...] executes complete original inputs.' \
    'loop --extension STEM builds the suite imports and observes that unchanged completion file.' \
    'An explicit +Module:facet is build-only and requires a selected acceptance consumer.' \
    'slow "REASON" MODULE... [-- acceptance arguments...] runs the same checks as an explicit long run.' \
    'milestone "REASON" builds all original targets and freshly executes their tests and suite.'
}

running() {
  incontainer bash -c '
    for process in /proc/[0-9]*; do
      [[ "$(readlink "$process/cwd" 2>/dev/null)" == "$0" ]] || continue
      name=$(cat "$process/comm" 2>/dev/null)
      if [[ "$name" == lake || "$name" == lean ]]; then echo "${process#/proc/} $name"; fi
    done' "$root"
}

command=${1:-}
[[ $# -gt 0 ]] && shift
reason=
targets=()
stems=()
sources=()
build_targets=()
case "$command" in
  stop)
    source scripts/container.sh
    active=$(running)
    [[ -n "$active" ]] || { echo "no lake or lean process works in this checkout"; exit 0; }
    echo "$active"
    incontainer kill $(echo "$active" | cut -d' ' -f1)
    exit 0
    ;;
  loop|slow|milestone) ;;
  *) usage; exit 2 ;;
esac

milestone_tree_status=
if [[ "$command" == milestone ]]; then
  milestone_tree_status=$(git status --porcelain)
fi
if [[ "$command" == slow || "$command" == milestone ]]; then reason=${1:-}; fi

mkdir -p timing/logs
run_dir=$(mktemp -d "timing/logs/$(date -u +%Y%m%dT%H%M%SZ)-$command.XXXXXX")
log=$run_dir/output.log
context=$run_dir/context.json
touch "$log" "$records"
exec {original_stdout}>&1 {original_stderr}>&2
exec > >(trap '' INT TERM; tee --output-error=warn -a "$log" >&"$original_stdout") 2>&1
log_writer=$!

CAS_FEEDBACK_PARENT_RUN=${CAS_FEEDBACK_RUN:-}
CAS_FEEDBACK_RUN=${run_dir##*/}
CAS_FEEDBACK_CONTEXT=$context
CAS_APPLICATION_LOG_DIR=$run_dir/application
export CAS_FEEDBACK_PARENT_RUN CAS_FEEDBACK_RUN CAS_FEEDBACK_CONTEXT CAS_APPLICATION_LOG_DIR
mkdir -p "$CAS_APPLICATION_LOG_DIR"
native() {
  incontainer env CAS_FEEDBACK_RUN="$CAS_FEEDBACK_RUN" \
    CAS_FEEDBACK_CONTEXT="$CAS_FEEDBACK_CONTEXT" \
    CAS_FEEDBACK_PARENT_RUN="$CAS_FEEDBACK_PARENT_RUN" \
    CAS_FEEDBACK_IMAGE_DIGEST="${CAS_FEEDBACK_IMAGE_DIGEST:-}" \
    CAS_APPLICATION_LOG_DIR="$CAS_APPLICATION_LOG_DIR" \
    CAS_FEEDBACK_STEP="${CAS_FEEDBACK_STEP:-}" \
    CAS_FEEDBACK_SOURCE="${CAS_FEEDBACK_SOURCE:-}" "$@"
}
preparation_ns=0 build_ns=0 execution_ns=0 acceptance_ns=0
build_status= execution_status= acceptance_status=
preparation_finished=false
context_pending=true
attempted=false
attempted_sources=()
active_pid=
interruption_signal=
run_active() {
  local status=0
  setsid env --default-signal=INT,TERM bash -c '"$@"' bash "$@" &
  active_pid=$!
  wait "$active_pid" || status=$?
  active_pid=
  return "$status"
}
interrupt() {
  interruption_signal=$1
  trap '' INT TERM
  if [[ -n "$active_pid" ]]; then
    kill -s "$1" -- "-$active_pid" 2>/dev/null || true
    wait "$active_pid" || true
    active_pid=
  fi
  exit "$2"
}
finish() {
  local status=$? drain_status=0
  trap - EXIT
  trap '' INT TERM
  set +e
  if [[ "$context_pending" == true ]]; then
    python3 -S scripts/feedback_records.py begin "$context" "$command" "$reason" "$log" \
      "${#targets[@]}" "${#stems[@]}" "${#sources[@]}" \
      "${targets[@]}" "${stems[@]}" "${sources[@]}" "${invocation[@]}"
    local refresh_status=$?
    [[ "$status" -ne 0 ]] || status=$refresh_status
  fi
  if [[ "$preparation_finished" != true ]]; then preparation_ns=$(( $(now) - started )); fi
  python3 -S scripts/feedback_records.py finish "$records" "$context" "$status" "$limit" \
    "$(( $(now) - started ))" "$preparation_ns" "$build_ns" "$execution_ns" "$acceptance_ns" \
    "$build_status" "$execution_status" "$acceptance_status" "$attempted" \
    "$interruption_signal" "${attempted_sources[@]}"
  status=$?
  exec 1>&"$original_stdout" 2>&"$original_stderr"
  wait "$log_writer" || drain_status=$?
  exec {original_stdout}>&- {original_stderr}>&-
  if [[ -f "$run_dir/result.json" ]]; then
    python3 -S scripts/feedback_records.py finalize "$records" "$context" "$drain_status"
    status=$?
  fi
  exit "$status"
}
trap finish EXIT
trap 'interrupt INT 130' INT
trap 'interrupt TERM 143' TERM
python3 -S scripts/feedback_records.py begin "$context" "$command" "$reason" "$log" \
  "${#targets[@]}" "${#stems[@]}" "${#sources[@]}" \
  "${targets[@]}" "${stems[@]}" "${sources[@]}" "${invocation[@]}"

case "$command" in
  loop)
    [[ $# -ge 1 ]] || die 'usage: just loop "<test modules>" [STEM | --extension STEM ...]'
    [[ "$1" != *$'\n'* ]] || die 'put selected test modules on one line'
    if [[ "$1" == --extension ]]; then
      targets=(+CasCatalogue.TestSuite:leanArts)
      stems=("$@")
    else
      read -r -a targets <<<"$1"
      shift
      stems=("$@")
    fi
    ;;
  slow)
    [[ $# -ge 2 ]] || die 'usage: just slow "<reason>" <module ...> [-- acceptance arguments ...]'
    reason=$1
    shift
    while [[ $# -gt 0 ]]; do
      if [[ "$1" == -- ]]; then
        shift
        [[ $# -gt 0 ]] || die 'name the acceptance selection after --'
        stems=("$@")
        break
      fi
      targets+=("$1")
      shift
    done
    ;;
  milestone)
    [[ $# -eq 1 ]] || die 'usage: just milestone "<reason>"'
    reason=$1
    [[ -z "$milestone_tree_status" ]] || die 'a milestone requires a clean committed tree'
    targets=(CasCompilerTests CasRuntimeTests CasDsl CasDslTests)
    build_targets=("${targets[@]}")
    stems=(--all)
    ;;
  *) usage; exit 2 ;;
esac
[[ "$command" == loop || ${#reason} -ge 20 ]] || die 'state the reason in at least 20 characters'
[[ ${#targets[@]} -gt 0 ]] || die 'select at least one test module; an empty selection cannot run'

if [[ "$command" != milestone ]]; then
  for target in "${targets[@]}"; do
    if [[ "$target" == *:* ]]; then
      [[ ${#stems[@]} -gt 0 && "$target" == +* ]] ||
        die 'an explicit +Module:facet is build-only and needs a selected acceptance consumer'
      build_targets+=("$target")
      continue
    fi
    module=${target#+}
    if [[ "$module" == *.lean ]]; then module=${module#./}; module=${module%.lean}; module=${module//\//.}; fi
    [[ "$module" =~ ^[A-Za-z_][A-Za-z0-9_]*([.][A-Za-z_][A-Za-z0-9_]*)*$ ]] ||
      die "not a local Lean module: $target"
    case "$module" in
      CasCompiler|CasRuntime|CasCompilerTests|CasRuntimeTests|CasDsl|CasDslTests|CasCatalogue|CasGates|CasAcceptance|CasTools)
        die "$module is an aggregate; name the actual test module for a focused run" ;;
    esac
    file=${module//.//}.lean
    sources+=("$file")
    build_targets+=("+$module:deps")
  done
fi

python3 -S scripts/feedback_records.py begin "$context" "$command" "$reason" "$log" \
  "${#targets[@]}" "${#stems[@]}" "${#sources[@]}" \
  "${targets[@]}" "${stems[@]}" "${sources[@]}" "${invocation[@]}"
source scripts/container.sh
export root
export -f native incontainer
run_active native python3 -S scripts/feedback_records.py identity "$context"
active=$(running)
[[ -z "$active" ]] || die "a run is in progress in this checkout (just stop stops it): $active"
if [[ ${#stems[@]} -gt 0 && -f .tmp/accept-run.json ]]; then
  mv .tmp/accept-run.json "$run_dir/prior-accept-run.json"
fi
if [[ ${#stems[@]} -gt 0 && -f .tmp/accept-current.json ]]; then
  mv .tmp/accept-current.json "$run_dir/prior-accept-current.json"
fi
if [[ ${#stems[@]} -gt 0 ]]; then
  python3 -S scripts/acceptance_inputs.py "$run_dir/selected-inputs.json" "${stems[@]}"
fi

if [[ "$command" == milestone ]]; then
  run_active native lake env lean --deps-json CasCompilerTests.lean CasRuntimeTests.lean CasDslTests.lean \
    > "$run_dir/imports.json"
  python3 -S - "$run_dir/imports.json" > "$run_dir/sources" <<'PY'
import json, sys
from pathlib import Path
roots = ("CasCompilerTests", "CasRuntimeTests", "CasDslTests")
results = json.loads(Path(sys.argv[1]).read_text())["imports"]
if len(results) != len(roots):
    raise SystemExit("the native import query did not return every test aggregate")
sources = []
for root, result in zip(roots, results, strict=True):
    if result["errors"] or "result" not in result:
        raise SystemExit(f"cannot discover tests of {root}: {result['errors']}")
    imports = result["result"]["imports"]
    selected = [entry["module"] for entry in imports if entry["module"] != "Init"]
    if not selected:
        raise SystemExit(f"test aggregate {root} selected no modules")
    for module in selected:
        path = Path(module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise SystemExit(f"test aggregate {root} imports missing local source {path}")
        if str(path) not in sources:
            sources.append(str(path))
print("\n".join(sources))
PY
  mapfile -t sources < "$run_dir/sources"
fi

run_active native python3 -S scripts/feedback_records.py context "$context" "$command" "$reason" "$log" \
  "${#targets[@]}" "${#stems[@]}" "${#sources[@]}" \
  "${targets[@]}" "${stems[@]}" "${sources[@]}" "${invocation[@]}"
context_pending=false
preparation_ns=$(( $(now) - started ))
preparation_finished=true

for file in "${sources[@]}"; do
  [[ -f "$file" ]] || {
    printf 'feedback: no local source for selected consumer: %s\n' "$file" >&2
    exit 2
  }
done

if [[ "$command" == loop ]]; then
  python3 -S - "$records" "$context" "$limit" <<'PY'
import json, sys
from pathlib import Path
records, context, limit = sys.argv[1:]
current = json.loads(Path(context).read_text())
previous = None
for line in Path(records).read_text().splitlines():
    entry = json.loads(line)
    if entry.get("kind") in ("loop", "slow") and entry.get("attempted") and entry.get("workload") == current["workload"]:
        previous = entry
if previous and previous["seconds"] > int(limit):
    raise SystemExit(f"this exact workload last took {previous['seconds']:.3f} s; repair its cost or use an explicit long run")
PY
fi

step() {
  local phase=$1 source=$2 before elapsed result
  shift 2
  printf '[%s] ' "$phase"
  printf '%q ' "$@"
  printf '\n'
  attempted=true
  before=$(now)
  python3 -S scripts/feedback_records.py step-start "$context" "$phase" "$source" "$before" \
    "$(( preparation_ns + build_ns ))" "$@" || return $?
  result=0
  CAS_FEEDBACK_STEP="$phase:$before" CAS_FEEDBACK_SOURCE="$source" run_active "$@" || result=$?
  elapsed=$(( $(now) - before ))
  python3 -S scripts/feedback_records.py step-finish "$context" "$before" "$elapsed" "$result" \
    || return $?
  case "$phase" in
    build) build_ns=$(( build_ns + elapsed )); build_status=$result ;;
    execution) execution_ns=$(( execution_ns + elapsed ));
      [[ -n "$execution_status" && "$execution_status" -ne 0 ]] || execution_status=$result ;;
    acceptance) acceptance_ns=$(( acceptance_ns + elapsed )); acceptance_status=$result ;;
  esac
  return "$result"
}

status=0
step build "" native lake --log-level=error build "${build_targets[@]}" || status=$?
if [[ "$status" -eq 0 || "$command" == milestone ]]; then
  for file in "${sources[@]}"; do
    attempted_sources+=("$file")
    if step execution "$file" native lake --log-level=error lean "$file" -- -DstderrAsMessages=false; then :; else
      result=$?
      [[ "$status" -ne 0 ]] || status=$result
      [[ "$command" == milestone ]] || break
    fi
  done
fi
if [[ ${#stems[@]} -gt 0 && ( "$status" -eq 0 || "$command" == milestone ) ]]; then
  if CAS_FEEDBACK_PARENT_CONTEXT="$context" step acceptance "" scripts/accept_files.sh "${stems[@]}"; then :; else
    result=$?
    [[ "$status" -ne 0 ]] || status=$result
  fi
fi
exit "$status"
