#!/usr/bin/env bash
# Run complete selected acceptance files through the public suite command.
# Named files use the current build outputs; do not build concurrently.
# Usage: accept_files.sh [--manifest FILE] STEM ...
#        accept_files.sh --all
#        accept_files.sh --baseline
# The default is the explicit no-provider diagnostic. A named manifest selects real providers.
# Only this invocation's results become .tmp/accept-run.json; earlier runs remain in their logs.
set -euo pipefail
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
mkdir -p .tmp/logs timing
run=$(mktemp -d ".tmp/logs/accept-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX")
[[ ! -f .tmp/accept-run.json ]] || cp .tmp/accept-run.json "$run/previous.json"
printf '[]\n' > .tmp/accept-run.json
printf 'Acceptance run: %s\n' "$run"
revision=$(git rev-parse HEAD)
manifest="$run/empty-leaves.json"
printf '{"backends":[],"registrations":[]}\n' > "$manifest"
if [[ "${1:-}" == "--manifest" ]]; then
  [[ $# -ge 3 ]] || { echo "usage: accept_files.sh --manifest FILE STEM ..." >&2; exit 2; }
  manifest=$2
  shift 2
fi
if [[ "${1:-}" == "--all" ]]; then
  [[ $# -eq 1 ]] || exit 2
  stems=()
  for file in tests/acceptance/*.cas; do stems+=("$(basename "$file" .cas)"); done
else
  stems=("$@")
fi
[[ ${#stems[@]} -gt 0 ]] || {
  echo "name complete acceptance files; use just milestone for every file" >&2
  exit 2
}
workers=2
[[ ${#stems[@]} -ge $workers ]] || workers=${#stems[@]}
prepare_status=0
python3 - "$run" "$manifest" "$workers" "${stems[@]}" <<'PY' || prepare_status=$?
import hashlib, json, sys
from pathlib import Path
sys.path.insert(0, "scripts")
from check_acceptance_permanent import MANIFEST, suite_assertions
run, manifest, workers = Path(sys.argv[1]), sys.argv[2], int(sys.argv[3])
stems = sys.argv[4:]
if len(set(stems)) != len(stems):
    raise SystemExit("select each acceptance file once")
admitted = json.loads(MANIFEST.read_text())["assertions"]
inputs = {}
for worker in range(workers):
    (run / f"worker{worker}.lean").write_text(
        "import LeanCategories.Catalogue\nimport CasCatalogue.TestSuite\n\n")
for index, stem in enumerate(stems):
    source = Path("tests/acceptance") / f"{stem}.cas"
    if source.parent != Path("tests/acceptance") or not source.is_file():
        raise SystemExit(f"no acceptance file {stem}")
    current = suite_assertions([source])
    ids = set(current)
    if not ids:
        raise SystemExit(f"no named assertions in {source}")
    for identity in ids:
        if identity not in admitted or current[identity] != admitted[identity]:
            raise SystemExit(f"selected assertion is not the unchanged admitted input: {identity}")
    inventory = run / f"{stem}.inventory.json"
    inventory.write_text(json.dumps({"assertions": {key: admitted[key] for key in sorted(ids)}}))
    inputs[str(source)] = hashlib.sha256(source.read_bytes()).hexdigest()
    with (run / f"worker{index % workers}.lean").open("a") as output:
        output.write(
            f"#cas_tests {json.dumps(str(source))} manifest {json.dumps(manifest)} "
            f"reporting {json.dumps(str(run / (stem + '.json')))} "
            f"inventory {json.dumps(str(inventory))}\n")
(run / "inputs.json").write_text(json.dumps(inputs, indent=2))
PY

build_started=$(python3 -c 'import time; print(time.monotonic_ns())')
build_status=$prepare_status
lean_path=""
if [[ $prepare_status -eq 0 ]]; then
  incontainer sha256sum "$manifest" > "$run/manifest.sha256" || build_status=$?
  if [[ $build_status -eq 0 ]]; then
    incontainer lake --log-level=error build LeanCategories.Catalogue CasCatalogue.TestSuite 2>&1 |
      tee "$run/build.log" || build_status=$?
  fi
  if [[ $build_status -eq 0 ]]; then
    lean_path=$(incontainer lake env printenv LEAN_PATH) || build_status=$?
  fi
fi
build_finished=$(python3 -c 'import time; print(time.monotonic_ns())')

run_worker() {
  local worker=$1 start status
  start=$(python3 -c 'import time; print(time.monotonic_ns())')
  set +e
  set -o pipefail
  incontainer env LEAN_PATH="$lean_path" lean -DstderrAsMessages=false "$run/worker$worker.lean" 2>&1 |
    tee "$run/worker$worker.log"
  status=$?
  python3 - "$run/worker$worker.status.json" "$start" "$status" <<'PY'
import json, sys, time
from pathlib import Path
Path(sys.argv[1]).write_text(json.dumps({
    "status": int(sys.argv[3]), "seconds": (time.monotonic_ns() - int(sys.argv[2])) / 1e9}))
PY
  return "$status"
}
export root lean_path run
export -f run_worker incontainer
workers_status=0
if [[ $build_status -eq 0 ]]; then
  # Every worker is reaped even if another fails; each publishes its real status.
  seq 0 $((workers - 1)) | xargs -P "$workers" -I{} bash -c 'run_worker {}' || workers_status=$?
fi

python3 - "$run" "$started" "$build_started" "$build_finished" "$build_status" \
  "$workers" "$workers_status" "$revision" "$manifest" "${stems[@]}" <<'PY'
import collections, datetime, hashlib, json, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, "scripts")
from check_acceptance_regression import FAILING, outcomes

run = Path(sys.argv[1])
started, build_started, build_finished, status, workers = map(int, sys.argv[2:7])
workers_status = int(sys.argv[7])
revision, manifest = sys.argv[8:10]
stems = sys.argv[10:]
selected = {f"tests/acceptance/{stem}.cas" for stem in stems}
complete = status == 0
status = status or workers_status
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
for stem in stems:
    source = f"tests/acceptance/{stem}.cas"
    try:
        report = run / f"{stem}.json"
        observed = outcomes(report)
        rows = json.loads(report.read_text())
        if any(row["kind"] not in {"holds", "gap", "unavailable"} | FAILING for row in rows):
            raise ValueError("unknown outcome in selected report")
        expected = set(json.loads((run / f"{stem}.inventory.json").read_text())["assertions"])
        actual = {identity for file, identity in observed if not identity.startswith("(statement)")}
        if any(file != source for file, _ in observed) or actual != expected:
            raise ValueError(f"incomplete or foreign selected results: expected {sorted(expected)}, "
                             f"received {sorted(actual)}")
        inputs = json.loads((run / "inputs.json").read_text())
        if hashlib.sha256(Path(source).read_bytes()).hexdigest() != inputs[source]:
            raise ValueError("selected input changed during execution")
        results.extend(rows)
        if any(row["fails"] or row["kind"] in FAILING for row in rows):
            status = status or 1
    except (SystemExit, FileNotFoundError, json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
        complete = False
        status = status or 1
        detail = f"current selected execution has no complete valid report: {error}"
        print(f"{source}: {detail}", file=sys.stderr)
        results.append({"file": source, "id": "(statement) current report", "kind": "internal",
                        "detail": detail, "fails": True, "question": "", "proposition": "",
                        "dispatches": [], "milliseconds": 0, "setupMilliseconds": 0})

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
    "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "revision": revision, "run": str(run), "files": stems, "manifest": manifest,
    "manifest_sha256": ((run / "manifest.sha256").read_text().split()[0]
                        if (run / "manifest.sha256").is_file() else None),
    "inputs": json.loads((run / "inputs.json").read_text()) if (run / "inputs.json").is_file() else {},
    "build_seconds": (build_finished - build_started) / 1e9,
    "workers": worker_results, "workers_status": workers_status,
    "seconds": seconds, "status": status, "complete": complete,
    "report": str(current), "report_sha256": hashlib.sha256(current.read_bytes()).hexdigest(),
    "outcomes": dict(collections.Counter(row["kind"] for row in results)),
}
with Path("timing/acceptance.jsonl").open("a") as output:
    output.write(json.dumps(entry, ensure_ascii=False) + "\n")
print(f"Current selected outcomes: {entry['outcomes']}; complete={complete}; "
      f"status={status}; total={seconds:.3f}s; report={current}")
raise SystemExit(status)
PY
