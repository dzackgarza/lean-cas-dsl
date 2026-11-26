#!/usr/bin/env bash
# Run complete selected acceptance files through the public suite command.
# Named files use the current build outputs; do not build concurrently.
# Usage: accept_files.sh [--manifest FILE] [STEM | --extension STEM] ...
#        accept_files.sh --all
#        accept_files.sh --baseline
# The default is the explicit no-provider diagnostic. A named manifest selects real providers.
# Only this invocation's results become .tmp/accept-run.json; earlier runs remain in their logs.
set -euo pipefail
invocation=(scripts/accept_files.sh "$@")
cd "$(dirname "$0")/.."
source scripts/container.sh

if [[ "${1:-}" == "--baseline" ]]; then
  [[ $# -eq 1 ]] || exit 2
  python3 - <<'PY'
import hashlib, json, shutil
from pathlib import Path
report = Path(".tmp/accept-run.json")
entry = json.loads(Path("timing/acceptance.jsonl").read_text().splitlines()[-1])
if not entry["complete"] or entry["report_sha256"] != hashlib.sha256(report.read_bytes()).hexdigest():
    raise SystemExit("the current report is not a complete recorded execution")
shutil.copyfile(report, ".tmp/accept-prev.json")
print("The complete current observation is now the regression baseline; its failures remain failures.")
PY
  exit 0
fi

started=$(python3 -c 'import time; print(time.monotonic_ns())')
mkdir -p .tmp timing/logs
run=$(mktemp -d "timing/logs/accept-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX")

context=$run/context.json
log=$run/output.log
touch "$log"
exec > >(tee -a "$log") 2>&1
CAS_FEEDBACK_PARENT_RUN=${CAS_FEEDBACK_RUN:-}
CAS_FEEDBACK_RUN=${run##*/}
CAS_FEEDBACK_CONTEXT=$context
CAS_APPLICATION_LOG_DIR=$run/application
export CAS_FEEDBACK_PARENT_RUN CAS_FEEDBACK_RUN CAS_FEEDBACK_CONTEXT CAS_APPLICATION_LOG_DIR
mkdir -p "$CAS_APPLICATION_LOG_DIR"
native() {
  incontainer env CAS_FEEDBACK_RUN="$CAS_FEEDBACK_RUN" \
    CAS_FEEDBACK_CONTEXT="$CAS_FEEDBACK_CONTEXT" \
    CAS_FEEDBACK_PARENT_RUN="$CAS_FEEDBACK_PARENT_RUN" \
    CAS_APPLICATION_LOG_DIR="$CAS_APPLICATION_LOG_DIR" "$@"
}
selection_args=("$@")
stems=("$@")
manifest="$run/empty-leaves.json"
workers=0
workers_status=0
build_status=1
build_started=$started
build_finished=$started
revision=$(git rev-parse HEAD)
python3 scripts/feedback_records.py begin "$context" accept "" "$log" \
  0 "${#stems[@]}" 0 "${stems[@]}" "${invocation[@]}"
finish() {
  local outer_status=$?
  trap - EXIT
  set +e
  python3 - "$run" "$started" "$build_started" "$build_finished" "$build_status" \
    "$workers" "$workers_status" "$revision" "$manifest" "$outer_status" "${stems[@]}" <<'PY'
import collections, datetime, hashlib, json, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, "scripts")
from check_acceptance_regression import outcomes, report_outcome
from feedback_records import append_record, atomic_json, collect_computations, identity, read_json

run = Path(sys.argv[1])
started, build_started, build_finished, status, workers = map(int, sys.argv[2:7])
workers_status = int(sys.argv[7])
revision, manifest = sys.argv[8:10]
outer_status = int(sys.argv[10])
stems = sys.argv[11:]
selection_path = run / "selection.json"
selection = json.loads(selection_path.read_text()) if selection_path.is_file() else {
    "files": [], "complete": False}
selected_files = selection["files"]
selected = {item["source"] for item in selected_files}
complete = status == 0 and selection["complete"]
status = status or workers_status or outer_status
context = read_json(run / "context.json")
results = []
worker_results = []
for worker in range(workers):
    path = run / f"worker{worker}.status.json"
    if path.is_file():
        observation = json.loads(path.read_text())
        worker_results.append(observation)
        if observation["status"]:
            status = observation["status"]
    else:
        complete = False
        status = status or 1
        worker_results.append({"status": None, "seconds": None})
for item in selected_files:
    source, key = item["source"], item["key"]
    try:
        report = run / f"{key}.json"
        observed = outcomes(report)
        rows = json.loads(report.read_text())
        if any("stratum" not in row for row in rows):
            raise ValueError("the current report lost its outcome stratum column")
        expected = set(json.loads((run / f"{key}.inventory.json").read_text())["assertions"])
        actual = {identity for file, identity in observed if not identity.startswith("(statement)")}
        if any(file != source for file, _ in observed) or actual != expected:
            raise ValueError(f"incomplete or foreign selected results: expected {sorted(expected)}, "
                             f"received {sorted(actual)}")
        inputs = json.loads((run / "inputs.json").read_text())
        if hashlib.sha256(Path(source).read_bytes()).hexdigest() != inputs[source]:
            raise ValueError("selected input changed during execution")
        results.extend({**row, "inputKind": item["kind"], "admitted": item["admitted"],
                        "computing": item["computing"]} for row in rows)
        if any(report_outcome(row).fails for row in rows):
            status = status or 1
    except (SystemExit, FileNotFoundError, json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
        complete = False
        status = status or 1
        detail = f"current selected execution has no complete valid report: {error}"
        print(f"{source}: {detail}", file=sys.stderr)
        results.append({"file": source, "id": "(statement) current report", "kind": "internal",
                        "stratum": None, "inputKind": item["kind"], "admitted": False,
                        "computing": item["kind"] == "extension",
                        "detail": detail, "fails": True, "question": "", "proposition": "",
                        "dispatches": [], "milliseconds": 0, "setupMilliseconds": 0})

shared_setup = (build_finished - started) / 1e9
computations = collect_computations(run / "context.json", shared_setup)
timed_files = {entry["file"] for entry in computations["files"]}
timing_complete = computations["complete"] and selected == timed_files
if not timing_complete:
    complete = False
    status = status or 1
    print("Current statement timing is incomplete; see " + str(run / "computation-summary.json"),
          file=sys.stderr)
current = run / "report.json"
current.write_text(json.dumps(results, ensure_ascii=False, indent=1) + "\n")
Path(".tmp/accept-run.json").write_bytes(current.read_bytes())
baseline = Path(".tmp/accept-prev.json")
if baseline.is_file():
    scoped = run / "baseline.json"
    scoped.write_text(json.dumps([row for row in json.loads(baseline.read_text())
                                 if row["file"] in selected]))
    comparison = subprocess.run(
        [sys.executable, "scripts/check_acceptance_regression.py", str(scoped), str(current)],
        check=False)
    status = status or comparison.returncode
seconds = (time.monotonic_ns() - started) / 1e9
entry = {
    **identity(context),
    "context_status": context["context_status"], "command": context["command"],
    "environment": context["environment"], "source": context.get("source"),
    "dependencies": context.get("dependencies", []), "resolution": context.get("resolution"),
    "computations": computations, "timing_complete": timing_complete,
    "preparation_seconds": (build_started - started) / 1e9,
    "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "revision": revision, "run": str(run), "files": [item["stem"] for item in selected_files],
    "selection": context.get("acceptance", stems),
    "selected_inputs": selected_files, "manifest": manifest,
    "manifest_sha256": ((run / "manifest.sha256").read_text().split()[0]
                        if (run / "manifest.sha256").is_file() else None),
    "inputs": json.loads((run / "inputs.json").read_text()) if (run / "inputs.json").is_file() else {},
    "build_seconds": (build_finished - build_started) / 1e9,
    "workers": worker_results, "workers_status": workers_status,
    "seconds": seconds, "status": status, "complete": complete,
    "report": str(current), "report_sha256": hashlib.sha256(current.read_bytes()).hexdigest(),
    "outcomes": dict(collections.Counter(row["kind"] for row in results)),
    "strata": dict(collections.Counter(row["stratum"] for row in results
                                       if row.get("stratum") is not None)),
}
atomic_json(run / "result.json", entry)
append_record(Path("timing/acceptance.jsonl"), entry)
append_record(run / "events.jsonl", {**identity(context), "event": "run.finished",
                                   "status": status, "seconds": seconds, "complete": complete})
print(f"Current selected outcomes: {entry['outcomes']}; complete={complete}; "
      f"status={status}; total={seconds:.3f}s; report={current}")
raise SystemExit(status)
PY
  local status=$?
  exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

[[ ! -f .tmp/accept-run.json ]] || cp .tmp/accept-run.json "$run/previous.json"
printf '[]\n' > .tmp/accept-run.json
printf 'Acceptance run: %s\n' "$run"
printf '{"backends":[],"registrations":[]}\n' > "$manifest"
prepare_status=0
python3 - "$run" "${selection_args[@]}" <<'PY' || prepare_status=$?
import hashlib, json, sys
from pathlib import Path
sys.path.insert(0, "scripts")
from acceptance_inputs import checked_input, parse_selection

run = Path(sys.argv[1])
manifest, selected = parse_selection(sys.argv[2:])
if not selected:
    raise SystemExit("select complete acceptance or extension files; use --all for the admitted suite")
manifest = manifest or str(run / "empty-leaves.json")
workers = min(2, len(selected))
arguments = ["--manifest", manifest]
for item in selected:
    if item["kind"] == "extension":
        arguments.append("--extension")
    arguments.append(item["stem"])
selection = {"manifest": manifest, "workers": workers, "files": selected,
             "arguments": arguments, "complete": False}
plan = run / "selection.json"
plan.write_text(json.dumps(selection, ensure_ascii=False, indent=2) + "\n")
inputs = {}
for worker in range(workers):
    (run / f"worker{worker}.lean").write_text(
        "import LeanCategories.Catalogue\nimport CasCatalogue.TestSuite\n\n")
for index, item in enumerate(selected):
    item = checked_input(item)
    selected[index] = item
    source, key = item["source"], item["key"]
    inventory = run / f"{key}.inventory.json"
    inventory.write_text(json.dumps({"assertions": item["assertions"],
                                    "admitted": item["admitted"],
                                    "source_sha256": item["sha256"],
                                    "authority": item["authority"]}))
    inputs[source] = item["sha256"]
    (run / "inputs.json").write_text(json.dumps(inputs, indent=2))
    plan.write_text(json.dumps(selection, ensure_ascii=False, indent=2) + "\n")
    with (run / f"worker{index % workers}.lean").open("a") as output:
        computing = " computing" if item["computing"] else ""
        output.write(
            f"#cas_tests {json.dumps(source)} manifest {json.dumps(manifest)} "
            f"reporting {json.dumps(str(run / (key + '.json')))} "
            f"inventory {json.dumps(str(inventory))}{computing}\n")
selection["complete"] = True
plan.write_text(json.dumps(selection, ensure_ascii=False, indent=2) + "\n")
PY

selected_args=("${selection_args[@]}")
if [[ -f "$run/selection.json" ]]; then
  mapfile -t prepared < <(python3 - "$run/selection.json" <<'PY'
import json, sys
from pathlib import Path
selection = json.loads(Path(sys.argv[1]).read_text())
print(selection["manifest"])
print(selection["workers"])
for item in selection["files"]:
    print(item["stem"])
PY
)
  manifest=${prepared[0]}
  workers=${prepared[1]}
  stems=("${prepared[@]:2}")
  mapfile -t selected_args < <(python3 - "$run/selection.json" <<'PY'
import json, sys
from pathlib import Path
print("\n".join(json.loads(Path(sys.argv[1]).read_text())["arguments"]))
PY
)
fi

if [[ $prepare_status -eq 0 ]]; then
  native python3 scripts/feedback_records.py context "$context" accept "" "$log" \
    0 "${#selected_args[@]}" 0 "${selected_args[@]}" "${invocation[@]}" \
    || prepare_status=$?
fi

build_started=$(python3 -c 'import time; print(time.monotonic_ns())')
build_status=$prepare_status
lean_path=""
if [[ $prepare_status -eq 0 ]]; then
  native sha256sum "$manifest" > "$run/manifest.sha256" || build_status=$?
  if [[ $build_status -eq 0 ]]; then
    native lake --log-level=error build LeanCategories.Catalogue CasCatalogue.TestSuite 2>&1 |
      tee "$run/build.log" || build_status=$?
  fi
  if [[ $build_status -eq 0 ]]; then
    lean_path=$(native lake env printenv LEAN_PATH) || build_status=$?
  fi
fi
build_finished=$(python3 -c 'import time; print(time.monotonic_ns())')

run_worker() {
  local worker=$1 start status
  start=$(python3 -c 'import time; print(time.monotonic_ns())')
  python3 scripts/feedback_records.py step-start "$context" "acceptance-worker$worker" "" "$start" \
    "$(( build_finished - started ))" lean "$run/worker$worker.lean" || return $?
  set +e
  set -o pipefail
  native env CAS_FEEDBACK_WORKER="$worker" LEAN_PATH="$lean_path" lean -DstderrAsMessages=false "$run/worker$worker.lean" 2>&1 |
    tee "$run/worker$worker.log"
  status=$?
  python3 scripts/feedback_records.py step-finish "$context" "$start" \
    "$(( $(python3 -c 'import time; print(time.monotonic_ns())') - start ))" "$status" || status=$?
  python3 - "$run/worker$worker.status.json" "$start" "$status" <<'PY'
import json, sys, time
from pathlib import Path
Path(sys.argv[1]).write_text(json.dumps({
    "status": int(sys.argv[3]), "seconds": (time.monotonic_ns() - int(sys.argv[2])) / 1e9}))
PY
  return "$status"
}
export root lean_path run context started build_finished
export -f run_worker incontainer native
workers_status=0
if [[ $build_status -eq 0 ]]; then
  # Every worker is reaped even if another fails; each publishes its real status.
  seq 0 $((workers - 1)) | xargs -P "$workers" -I{} bash -c 'run_worker {}' || workers_status=$?
fi

[[ "$build_status" -eq 0 ]] || exit "$build_status"
exit "$workers_status"
