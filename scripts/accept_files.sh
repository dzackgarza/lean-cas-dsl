#!/usr/bin/env bash
set -euo pipefail
invocation=(scripts/accept_files.sh "$@")
cd "$(dirname "$0")/.."

if [[ "${1:-}" == "--baseline" ]]; then
  source scripts/container.sh
  [[ $# -eq 1 ]] || exit 2
  python3 - <<'PY'
import hashlib, json, shutil
from pathlib import Path
report = Path(".tmp/accept-run.json")
current = json.loads(Path(".tmp/accept-current.json").read_text())
result = Path(current["result"])
entry = json.loads(result.read_text())
try:
    finished = json.loads(result.with_name("events.jsonl").read_text().splitlines()[-1])
except (FileNotFoundError, IndexError, json.JSONDecodeError):
    finished = {}
if (not entry["complete"] or finished.get("event") != "run.finished"
        or finished.get("run") != result.parent.name
        or any(finished.get(key) != entry[key] for key in ("context", "status", "complete", "log"))
        or entry["report_sha256"] != hashlib.sha256(report.read_bytes()).hexdigest()):
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
exec {log_stdout}>&1 {log_stderr}>&2
exec > >(trap '' INT TERM; tee --output-error=warn -a "$log" >&"$log_stdout") 2>&1
log_pid=$!
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
    CAS_APPLICATION_LOG_DIR="$CAS_APPLICATION_LOG_DIR" \
    CAS_FEEDBACK_IMAGE_DIGEST="${CAS_FEEDBACK_IMAGE_DIGEST:-}" \
    CAS_FEEDBACK_STEP="${CAS_FEEDBACK_STEP:-}" \
    CAS_FEEDBACK_SOURCE="${CAS_FEEDBACK_SOURCE:-}" "$@"
}
selection_args=("$@")
stems=("$@")
manifest="$run/empty-leaves.json"
workers=0
workers_status=0
build_status=1
build_started=$started
build_finished=$started
active_phase=preparation
active_pid=
interruption_signal=
revision=$(git rev-parse HEAD)
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
    kill -s "$interruption_signal" -- "-$active_pid" 2>/dev/null || true
    wait "$active_pid" 2>/dev/null || true
    active_pid=
  fi
  exit "$2"
}
finish() {
  local outer_status=$? unfinished_phase=$active_phase finished
  trap - EXIT
  trap '' INT TERM
  set +e
  finished=$(python3 -c 'import time; print(time.monotonic_ns())')
  if [[ ! -f "$context" ]]; then
    python3 scripts/feedback_records.py begin "$context" accept "" "$log" \
      0 "${#stems[@]}" 0 "${stems[@]}" "${invocation[@]}"
  fi
  if [[ "$active_phase" == preparation ]]; then
    build_started=$finished
    build_finished=$finished
  elif [[ "$active_phase" == build ]]; then
    build_finished=$finished
  fi
  python3 - "$run" "$started" "$build_started" "$build_finished" "$build_status" \
    "$workers" "$workers_status" "$revision" "$manifest" "$outer_status" "$unfinished_phase" \
    "$interruption_signal" "$finished" "${stems[@]}" <<'PY'
import collections, datetime, hashlib, json, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, "scripts")
from acceptance_inputs import parse_selection
from check_acceptance_regression import outcomes, report_outcome
from feedback_records import atomic_json, collect_computations, identity, read_json

run = Path(sys.argv[1])
started, build_started, build_finished, status, workers = map(int, sys.argv[2:7])
workers_status = int(sys.argv[7])
revision, manifest = sys.argv[8:10]
outer_status = int(sys.argv[10])
unfinished_phase = sys.argv[11] or None
interruption_signal = sys.argv[12] or None
finished = int(sys.argv[13])
stems = sys.argv[14:]
context = read_json(run / "context.json")
metadata_errors = []
selection_path = run / "selection.json"
try:
    if selection_path.is_file():
        selection = read_json(selection_path)
    else:
        _, files = parse_selection(context["acceptance"])
        selection = {"files": files, "complete": False}
    if not isinstance(selection, dict) or type(selection["complete"]) is not bool:
        raise ValueError("invalid selected-input completion")
    if not isinstance(selection["files"], list) or any(
            not isinstance(item, dict) or any(not isinstance(item.get(key), str) or not item[key]
                for key in ("source", "key", "stem", "kind"))
            or item["kind"] not in {"admitted", "extension"} for item in selection["files"]):
        raise ValueError("invalid selected-input identities")
except (OSError, json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
    metadata_errors.append(f"{selection_path}: {error}")
    try:
        _, files = parse_selection(context["acceptance"])
    except (KeyError, TypeError, ValueError, SystemExit) as error:
        metadata_errors.append(f"original selection: {error}")
        files = []
    selection = {"files": files, "complete": False}
selected_files = selection["files"]
selected = {item["source"] for item in selected_files}
complete = status == 0 and selection["complete"] and unfinished_phase is None
status = (outer_status or status or 1) if unfinished_phase else (status or workers_status or outer_status)
try:
    inputs = read_json(run / "inputs.json") if (run / "inputs.json").is_file() else {}
    if not isinstance(inputs, dict) or any(not isinstance(value, str) for value in inputs.values()):
        raise ValueError("invalid selected-input hashes")
except (OSError, json.JSONDecodeError, TypeError, ValueError) as error:
    metadata_errors.append(f"{run / 'inputs.json'}: {error}")
    inputs = {source: context.get("inputs", {}).get(source) for source in selected}
results = []
file_statuses = {source: "fail" for source in selected}
input_metadata_complete = not metadata_errors
worker_results = []
for worker in range(workers):
    path = run / f"worker{worker}.status.json"
    try:
        observation = read_json(path)
        if not isinstance(observation, dict) or type(observation["status"]) is not int:
            raise ValueError("invalid worker status")
        if (observation["status"] < 0 or type(observation["seconds"]) not in (int, float)
                or not 0 <= observation["seconds"] < float("inf")):
            raise ValueError("invalid worker duration or status")
        worker_results.append(observation)
        if observation["status"]:
            status = observation["status"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
        complete = False
        status = status or 1
        metadata_errors.append(f"{path}: {error}")
        worker_results.append({"status": None, "seconds": None, "error": str(error)})
worker_metadata_count = len(metadata_errors)
for item in selected_files:
    source, key = item["source"], item["key"]
    try:
        report = run / f"{key}.json"
        observed = outcomes(report)
        rows = json.loads(report.read_text())
        if any("stratum" not in row for row in rows):
            raise ValueError("the current report lost its outcome stratum column")
        inventory = read_json(run / f"{key}.inventory.json")
        expected = set(inventory["assertions"])
        actual = {identity for file, identity in observed if not identity.startswith("(statement)")}
        if any(file != source for file, _ in observed) or actual != expected:
            raise ValueError(f"incomplete or foreign selected results: expected {sorted(expected)}, "
                             f"received {sorted(actual)}")
        if hashlib.sha256(Path(source).read_bytes()).hexdigest() != inputs[source]:
            raise ValueError("selected input changed during execution")
        admitted = item.get("admitted", inventory["admitted"])
        computing = item.get("computing", item["kind"] == "extension")
        if type(admitted) is not bool or type(computing) is not bool:
            raise ValueError("invalid selected-input admission or computation mode")
        results.extend({**row, "inputKind": item["kind"], "admitted": admitted,
                        "computing": computing} for row in rows)
        file_statuses[source] = "fail" if any(report_outcome(row).fails for row in rows) else "pass"
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
    try:
        scoped = run / "baseline.json"
        scoped.write_text(json.dumps([row for row in json.loads(baseline.read_text())
                                     if row["file"] in selected]))
        comparison = subprocess.run(
            [sys.executable, "scripts/check_acceptance_regression.py", str(scoped), str(current)],
            check=False)
        status = status or comparison.returncode
        if comparison.returncode:
            baseline_rows = json.loads(scoped.read_text())
            for item in selected_files:
                source, key = item["source"], item["key"]
                if file_statuses[source] != "pass":
                    continue
                file_baseline = run / f"baseline--{key}.json"
                file_baseline.write_text(json.dumps([row for row in baseline_rows if row["file"] == source]))
                file_comparison = subprocess.run(
                    [sys.executable, "scripts/check_acceptance_regression.py", str(file_baseline),
                     str(run / f"{key}.json")], stdout=subprocess.DEVNULL, check=False)
                if file_comparison.returncode:
                    file_statuses[source] = "fail"
    except (OSError, json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
        metadata_errors.append(f"{baseline}: {error}")
manifest_sha256 = None
if (run / "manifest.sha256").is_file():
    try:
        manifest_sha256 = (run / "manifest.sha256").read_text().split()[0]
        if len(manifest_sha256) != 64 or any(char not in "0123456789abcdef" for char in manifest_sha256):
            raise ValueError("invalid manifest hash")
    except (OSError, IndexError, ValueError) as error:
        metadata_errors.append(f"{run / 'manifest.sha256'}: {error}")
        manifest_sha256 = None
if metadata_errors:
    complete = False
    status = status or 1
    for error in metadata_errors:
        print(f"Current acceptance metadata is incomplete: {error}", file=sys.stderr)
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
    "manifest_sha256": manifest_sha256,
    "inputs": inputs, "metadata_errors": metadata_errors, "unfinished_phase": unfinished_phase,
    "interruption_signal": interruption_signal, "terminated_monotonic_ns": finished,
    "file_statuses": file_statuses,
    "terminal_metadata_complete": (input_metadata_complete and
        len(metadata_errors) == worker_metadata_count and selection["complete"] and
        context["context_status"] == "complete"),
    "build_seconds": (build_finished - build_started) / 1e9,
    "workers": worker_results, "workers_status": workers_status,
    "seconds": seconds, "status": status, "complete": complete,
    "report": str(current), "report_sha256": hashlib.sha256(current.read_bytes()).hexdigest(),
    "outcomes": dict(collections.Counter(row["kind"] for row in results)),
    "strata": dict(collections.Counter(row["stratum"] for row in results
                                       if row.get("stratum") is not None)),
}
atomic_json(run / "result.json", entry)
print(f"Current selected outcomes: {entry['outcomes']}; complete={complete}; "
      f"status={status}; total={seconds:.3f}s; report={current}")
raise SystemExit(status)
PY
  local status=$?
  exec 1>&"$log_stdout" 2>&"$log_stderr"
  exec {log_stdout}>&- {log_stderr}>&-
  local log_status=0
  wait "$log_pid" || log_status=$?
  [[ "$status" -ne 0 ]] || status=$log_status
  python3 - "$run" "$log" "$log_status" "$status" <<'PY'
import sys
from pathlib import Path
sys.path.insert(0, "scripts")
from feedback_records import append_record, atomic_json, compress_log, identity, read_json, terminal_row, utc_at

run = Path(sys.argv[1])
log_path, log_sha256 = compress_log(Path(sys.argv[2]))
context = read_json(run / "context.json")
entry = read_json(run / "result.json")
context["log"] = log_path
atomic_json(run / "context.json", context)
entry["log"], entry["log_sha256"] = log_path, log_sha256
if int(sys.argv[3]):
    entry["status"] = int(sys.argv[4])
    entry["complete"] = False
    entry["terminal_metadata_complete"] = False
    entry["metadata_errors"].append("the acceptance log writer failed before finalization")
atomic_json(run / "result.json", entry)
for item in entry["selected_inputs"]:
    source = item["source"]
    observations = [row for row in entry["computations"]["files"] if row["file"] == source]
    observation = observations[0] if len(observations) == 1 else None
    begin = observation.get("begin") if observation else None
    terminal = (observation.get("completion") or observation.get("failure")) if observation else None
    if begin is not None:
        started_ns = begin["monotonicMilliseconds"] * 1_000_000
        utc_start = observation.get("utc_start") or utc_at(context, started_ns)
        seconds = observation.get("seconds")
        if seconds is None or not 0 <= seconds < float("inf"):
            seconds = max(0, (entry["terminated_monotonic_ns"] - started_ns) / 1e9)
    else:
        utc_start, seconds = context["utc"], 0
    completed = bool(observation and observation["complete"] and terminal is not None)
    if completed:
        status = (entry["file_statuses"][source] if entry["terminal_metadata_complete"] else "fail")
    else:
        status = "interrupted" if entry["interruption_signal"] else "fail"
    append_record(Path("timing/acceptance.jsonl"), terminal_row(context,
        target=source, input_sha256=entry["inputs"].get(source, context["inputs"].get(source)),
        utc_start=utc_start, seconds=seconds, status=status,
        log_path=log_path, log_sha256=log_sha256))
append_record(run / "events.jsonl", {**identity(context), "event": "run.finished",
    "status": entry["status"], "seconds": entry["seconds"], "complete": entry["complete"],
    "unfinished_phase": entry["unfinished_phase"], "interruption_signal": entry["interruption_signal"]})
PY
  local record_status=$?
  [[ "$status" -ne 0 ]] || status=$record_status
  exit "$status"
}
trap finish EXIT
trap 'interrupt INT 130' INT
trap 'interrupt TERM 143' TERM
python3 scripts/feedback_records.py begin "$context" accept "" "$log" \
  0 "${#stems[@]}" 0 "${stems[@]}" "${invocation[@]}"

[[ ! -f .tmp/accept-run.json ]] || cp .tmp/accept-run.json "$run/previous.json"
printf '[]\n' > .tmp/accept-run.json
printf 'Acceptance run: %s\n' "$run"
printf '{"backends":[],"registrations":[]}\n' > "$manifest"
source scripts/container.sh
export root
export -f incontainer native
prepare_status=0
run_active native python3 scripts/feedback_records.py identity "$context" || prepare_status=$?
python3 - "$run" "${selection_args[@]}" <<'PY' || prepare_status=$?
import hashlib, json, sys
from pathlib import Path
sys.path.insert(0, "scripts")
from acceptance_inputs import checked_input, parse_selection
from feedback_records import atomic_json

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
atomic_json(plan, selection)
inputs = {}
for worker in range(workers):
    (run / f"worker{worker}.lean").write_text(
        "module\n\nimport LeanCategories.Catalogue\nimport CasCatalogue.TestSuite\n\n")
for index, item in enumerate(selected):
    item = checked_input(item)
    selected[index] = item
    source, key = item["source"], item["key"]
    inventory = run / f"{key}.inventory.json"
    atomic_json(inventory, {"assertions": item["assertions"],
                            "admitted": item["admitted"],
                            "source_sha256": item["sha256"],
                            "authority": item["authority"]})
    inputs[source] = item["sha256"]
    atomic_json(run / "inputs.json", inputs)
    atomic_json(plan, selection)
    with (run / f"worker{index % workers}.lean").open("a") as output:
        computing = " computing" if item["computing"] else ""
        output.write(
            f"#cas_tests {json.dumps(source)} manifest {json.dumps(manifest)} "
            f"reporting {json.dumps(str(run / (key + '.json')))} "
            f"inventory {json.dumps(str(inventory))}{computing}\n")
selection["complete"] = True
atomic_json(plan, selection)
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
  run_active native python3 scripts/feedback_records.py context "$context" accept "" "$log" \
    0 "${#selected_args[@]}" 0 "${selected_args[@]}" "${invocation[@]}" \
    || prepare_status=$?
fi

build_started=$(python3 -c 'import time; print(time.monotonic_ns())')
build_finished=$build_started
active_phase=
build_status=$prepare_status
if [[ $prepare_status -eq 0 ]]; then
  active_phase=build
  run_active native sha256sum "$manifest" > "$run/manifest.sha256" || build_status=$?
  if [[ $build_status -eq 0 ]]; then
    run_build() {
      set -o pipefail
      native lake --log-level=error build LeanCategories.Catalogue CasCatalogue.TestSuite 2>&1 |
        tee "$run/build.log"
    }
    export run
    export -f run_build
    run_active run_build || build_status=$?
  fi
  build_finished=$(python3 -c 'import time; print(time.monotonic_ns())')
  active_phase=
fi

run_worker() {
  local worker=$1 start status
  start=$(python3 -c 'import time; print(time.monotonic_ns())')
  python3 scripts/feedback_records.py step-start "$context" "acceptance-worker$worker" "" "$start" \
    "$(( build_finished - started ))" lake --log-level=error lean "$run/worker$worker.lean" \
    -- -DstderrAsMessages=false || return $?
  set +e
  set -o pipefail
  native env CAS_FEEDBACK_WORKER="$worker" CAS_FEEDBACK_STEP="acceptance-worker$worker:$start" \
    CAS_FEEDBACK_SOURCE="$run/worker$worker.lean" \
    lake --log-level=error lean "$run/worker$worker.lean" -- -DstderrAsMessages=false 2>&1 |
    tee "$run/worker$worker.log"
  status=$?
  python3 scripts/feedback_records.py step-finish "$context" "$start" \
    "$(( $(python3 -c 'import time; print(time.monotonic_ns())') - start ))" "$status" || status=$?
  python3 - "$run/worker$worker.status.json" "$start" "$status" <<'PY'
import sys, time
from pathlib import Path
sys.path.insert(0, "scripts")
from feedback_records import atomic_json
atomic_json(Path(sys.argv[1]), {
    "status": int(sys.argv[3]), "seconds": (time.monotonic_ns() - int(sys.argv[2])) / 1e9})
PY
  return "$status"
}
export root run context started build_finished workers
export -f run_worker incontainer native
workers_status=0
if [[ $build_status -eq 0 ]]; then
  run_workers() {
    set -o pipefail
    seq 0 $((workers - 1)) | xargs -P "$workers" -I{} bash -c 'run_worker {}'
  }
  export -f run_workers
  run_active run_workers || workers_status=$?
fi

[[ "$build_status" -eq 0 ]] || exit "$build_status"
exit "$workers_status"
