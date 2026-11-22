#!/usr/bin/env bash
# Current-source feedback (C21/C24). Called by just loop, slow, milestone and stop.
# loop "MODULE ..." [acceptance stems...] rebuilds imports, then executes each source afresh.
# An explicit +Module:facet is build-only and requires a selected acceptance consumer.
# slow "REASON" MODULE... [-- acceptance arguments...] runs the same checks as an explicit long run.
# milestone "REASON" builds all original targets and freshly executes their tests and suite.
# Logs are unique per invocation; timing/runs.jsonl records its source, tuple and phase times.
set -euo pipefail
invocation=(scripts/feedback.sh "$@")
now() { python3 -c 'import time; print(time.monotonic_ns())'; }
started=$(now)
cd "$(dirname "$0")/.."
source scripts/container.sh
limit=300
records=timing/runs.jsonl
die() { echo "feedback: $*" >&2; exit 2; }

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
    active=$(running)
    [[ -n "$active" ]] || { echo "no lake or lean process works in this checkout"; exit 0; }
    echo "$active"
    incontainer kill $(echo "$active" | cut -d' ' -f1)
    exit 0
    ;;
  loop)
    [[ $# -ge 1 ]] || die 'usage: just loop "<test modules>" [acceptance stem ...]'
    [[ "$1" != *$'\n'* ]] || die 'put selected test modules on one line'
    read -r -a targets <<<"$1"
    shift
    stems=("$@")
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
    [[ -z "$(git status --porcelain)" ]] || die 'a milestone requires a clean committed tree'
    targets=(CasCompilerTests CasRuntimeTests CasDsl CasDslTests)
    build_targets=("${targets[@]}")
    stems=(--all)
    ;;
  *) sed -n '2,7p' "$0" | sed 's/^# //'; exit 2 ;;
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

active=$(running)
[[ -z "$active" ]] || die "a run is in progress in this checkout (just stop stops it): $active"
mkdir -p .tmp/logs timing
run_dir=$(mktemp -d ".tmp/logs/$(date -u +%Y%m%dT%H%M%SZ)-$command.XXXXXX")
log=$run_dir/output.log
context=$run_dir/context.json
touch "$log" "$records"
if [[ ${#stems[@]} -gt 0 && -f .tmp/accept-run.json ]]; then
  mv .tmp/accept-run.json "$run_dir/prior-accept-run.json"
fi

if [[ "$command" == milestone ]]; then
  # Lean's native header parser is also used by Lake; it does not elaborate imported tests.
  # https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Elab/ParseImportsFast.lean
  incontainer lake env lean --deps-json CasCompilerTests.lean CasRuntimeTests.lean CasDslTests.lean \
    > "$run_dir/imports.json" 2> >(tee -a "$log" >&2)
  python3 - "$run_dir/imports.json" > "$run_dir/sources" <<'PY'
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

# Resolve the actual package paths in the build environment, including container symlinks.
incontainer python3 - "$context" "$command" "$reason" "$log" \
  "${#targets[@]}" "${#stems[@]}" "${#sources[@]}" \
  "${targets[@]}" "${stems[@]}" "${sources[@]}" "${invocation[@]}" <<'PY'
import datetime, hashlib, json, os, platform, subprocess, sys
from pathlib import Path
out, kind, reason, log = sys.argv[1:5]
target_count, stem_count, source_count = map(int, sys.argv[5:8])
cursor = 8
targets = sys.argv[cursor:cursor + target_count]
cursor += target_count
stems = sys.argv[cursor:cursor + stem_count]
cursor += stem_count
sources = sys.argv[cursor:cursor + source_count]
cursor += source_count
digest = lambda data: hashlib.sha256(data).hexdigest()
def git_state(path: Path) -> dict[str, object]:
    def git(*args: str) -> bytes:
        return subprocess.check_output(["git", "-C", str(path), *args])
    revision = git("rev-parse", "HEAD").decode().strip()
    selection = ["--", ".", ":(exclude)timing"]
    diff = git("diff", "--binary", "HEAD", *selection)
    untracked = git("ls-files", "--others", "--exclude-standard", "-z", *selection).decode().split("\0")
    extra = {name: digest((path / name).read_bytes()) for name in untracked if name and (path / name).is_file()}
    return {"path": str(path.resolve()), "revision": revision, "diff_sha256": digest(diff),
            "changed": git("diff", "--name-only", "HEAD", *selection).decode().splitlines(),
            "untracked": extra, "dirty": bool(diff or extra)}
checkout = Path.cwd()
manifest_path = checkout / "lake-manifest.json"
manifest = json.loads(manifest_path.read_text())
dependencies = []
for package in manifest["packages"]:
    name = package["name"].strip("«»")
    path = (checkout / manifest.get("packagesDir", ".lake/packages") / name).resolve()
    if package["type"] == "path":
        path = (checkout / package["dir"]).resolve()
    dependencies.append({"name": name, "pin": package.get("rev"), **git_state(path)})
inputs = sources.copy()
acceptance = stems.copy()
if acceptance[:1] == ["--manifest"] and len(acceptance) >= 2:
    inputs.append(acceptance[1])
    acceptance = acceptance[2:]
inputs += [str(path) for path in sorted(Path("tests/acceptance").glob("*.cas"))] if acceptance == ["--all"] else [f"tests/acceptance/{stem}.cas" for stem in acceptance]
inputs += ["lean-toolchain", "lake-manifest.json", "lakefile.lean"]
# Match CasRuntime.installedManifest, including the absent-default observation.
installed = Path(os.environ.get("CAS_LEAVES", ".lake/packages/cas_leaves"))
if installed.suffix != ".json":
    installed /= "leaves.json"
inputs.append(str(installed))
if "CAS_REALIZATION_PROFILE" in os.environ:
    inputs.append(os.environ["CAS_REALIZATION_PROFILE"])
input_hashes = {name: digest(Path(name).read_bytes()) if Path(name).is_file() else None for name in inputs}
source = git_state(checkout)
environment = {"host": platform.node(), "system": platform.platform(), "machine": platform.machine(),
    "python": platform.python_version(),
    "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
    "lake": subprocess.check_output(["lake", "--version"], text=True).strip(),
    "selectors": {key: os.environ[key] for key in ("ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SYSROOT",
        "CAS_LEAVES", "CAS_REALIZATION_PROFILE", "CAS_LEAF_CONTRACT_PATH", "CAS_SAGE_PYTHON",
        "CAS_GAP_PYTHON") if key in os.environ}}
workload = {"targets": targets, "acceptance": stems, "inputs": input_hashes,
            "source": source, "dependencies": dependencies, "environment": environment}
entry = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "kind": kind,
    "run": Path(out).parent.name, "revision": source["revision"], "dirty": source["dirty"],
    "reason": reason, "command": sys.argv[cursor:], "sources": sources, "log": log,
    "workload": digest(json.dumps(workload, sort_keys=True).encode()), **workload}
Path(out).write_text(json.dumps(entry))
PY

build_ns=0 execution_ns=0 acceptance_ns=0
build_status= execution_status= acceptance_status=
attempted=false
attempted_sources=()
finish() {
  local status=$?
  trap - EXIT
  set +e
  python3 - "$records" "$context" "$status" "$limit" "$(( $(now) - started ))" \
    "$build_ns" "$execution_ns" "$acceptance_ns" "$build_status" "$execution_status" \
    "$acceptance_status" "$attempted" "${attempted_sources[@]}" <<'PY'
import datetime, json, sys
from pathlib import Path
records, context, status, limit, total, build, execution, acceptance, bs, es, acs, attempted = sys.argv[1:13]
sources = sys.argv[13:]
entry = json.loads(Path(context).read_text())
seconds = int(total) / 1e9
over = entry["kind"] == "loop" and seconds > int(limit)
execution_result = int(status)
status = execution_result or (1 if over else 0)
entry.update({"seconds": seconds, "status": status, "execution_status": execution_result,
    "over_limit": over, "within_loop_bound": seconds <= int(limit), "attempted": attempted == "true",
    "attempted_sources": sources, "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "phases": {name: {"seconds": int(elapsed) / 1e9, "status": int(result) if result else None}
        for name, elapsed, result in (("build", build, bs), ("execution", execution, es), ("acceptance", acceptance, acs))}})
summary = f"{entry['kind']}: execution status {execution_result}; status {status} in {seconds:.3f} s; log {entry['log']}"
if over:
    summary += f"\nOVER THE LIMIT: the {limit}-second development loop needs repair. The run was allowed to finish."
with open(entry["log"], "a") as handle:
    handle.write(summary + "\n")
with open(records, "a") as handle:
    handle.write(json.dumps(entry, ensure_ascii=False) + "\n")
print(summary)
raise SystemExit(status)
PY
  status=$?
  exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# A missing local consumer retires earlier acceptance results and records this failure.
for file in "${sources[@]}"; do
  [[ -f "$file" ]] || {
    printf 'feedback: no local source for selected consumer: %s\n' "$file" | tee -a "$log" >&2
    exit 2
  }
done

# A newer explicit slow run of this exact selection and tuple supersedes older loop evidence.
if [[ "$command" == loop ]]; then
  python3 - "$records" "$context" "$limit" <<'PY'
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

# One phase uses one command; preserve both command failure and a failed durable-log write.
step() {
  local phase=$1 before elapsed result
  shift
  printf '[%s] ' "$phase" | tee -a "$log"
  printf '%q ' "$@" | tee -a "$log"
  printf '\n' | tee -a "$log"
  attempted=true
  before=$(now)
  set +e
  "$@" 2>&1 | tee -a "$log"
  local codes=("${PIPESTATUS[@]}")
  set -e
  elapsed=$(( $(now) - before ))
  result=${codes[0]}
  [[ "$result" -ne 0 ]] || result=${codes[1]}
  case "$phase" in
    build) build_ns=$(( build_ns + elapsed )); build_status=$result ;;
    execution) execution_ns=$(( execution_ns + elapsed ));
      [[ -n "$execution_status" && "$execution_status" -ne 0 ]] || execution_status=$result ;;
    acceptance) acceptance_ns=$(( acceptance_ns + elapsed )); acceptance_status=$result ;;
  esac
  return "$result"
}

status=0
# Lake retains complete failed-job logs and build progress at this threshold. The fresh
# consumer's own stdout/stderr remains unfiltered; successful import warnings stay in Lake.
step build incontainer lake --log-level=error build "${build_targets[@]}" || status=$?
if [[ "$status" -eq 0 || "$command" == milestone ]]; then
  for file in "${sources[@]}"; do
    attempted_sources+=("$file")
    if step execution incontainer lake --log-level=error lean "$file" -- -DstderrAsMessages=false; then :; else
      result=$?
      [[ "$status" -ne 0 ]] || status=$result
      [[ "$command" == milestone ]] || break
    fi
  done
fi
if [[ ${#stems[@]} -gt 0 && ( "$status" -eq 0 || "$command" == milestone ) ]]; then
  if step acceptance scripts/accept_files.sh "${stems[@]}"; then :; else
    result=$?
    [[ "$status" -ne 0 ]] || status=$result
  fi
fi
exit "$status"
