#!/usr/bin/env bash
# Feedback loops of lean-cas-dsl (constitution C24, CONTRIBUTING "Feedback loops").
#
#   feedback.sh loop "<targets>" [stem ...]   the short loop: build the named Lake targets, then
#                                             run the named acceptance files. Limit: 300 s.
#   feedback.sh slow "<reason>" <target ...>  a target that the records show over the limit.
#   feedback.sh milestone "<reason>"          every test module, the notebook targets and every
#                                             acceptance file. Needs a clean tree.
#   feedback.sh stop                          stop every lake and lean process of this checkout.
#
# Each run appends one record to timing/runs.jsonl and writes its full output to .tmp/logs/.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/container.sh

limit=300
records=timing/runs.jsonl
mkdir -p .tmp/logs timing
touch "$records"

die() { echo "feedback: $*" >&2; exit 2; }

# The lake and lean processes whose working directory is this checkout, as "pid name" lines.
running() {
  incontainer bash -c '
    for process in /proc/[0-9]*; do
      [[ "$(readlink "$process/cwd" 2>/dev/null)" == "$0" ]] || continue
      name=$(cat "$process/comm" 2>/dev/null)
      if [[ "$name" == lake || "$name" == lean ]]; then echo "${process#/proc/} $name"; fi
    done' "$root"
}

require_idle() {
  local active
  active=$(running)
  [[ -z "$active" ]] || die "a run is in progress in this checkout (\`just stop\` stops it):
$active"
}

# record KIND STATUS SECONDS REASON TARGETS STEMS
record() {
  python3 - "$records" "$limit" "$@" <<'EOF'
import datetime, json, subprocess, sys
path, limit, kind, status, seconds, reason, targets, stems = sys.argv[1:9]
git = lambda *a: subprocess.run(("git",) + a, capture_output=True, text=True, check=True).stdout
entry = {
    "utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "kind": kind,
    "revision": git("rev-parse", "--short", "HEAD").strip(),
    "dirty": bool(git("status", "--porcelain", "--untracked-files=no").strip()),
    "targets": targets.split(),
    "acceptance": stems.split(),
    "seconds": int(seconds),
    "status": int(status),
    "over_limit": kind == "loop" and int(seconds) > int(limit),
}
if reason:
    entry["reason"] = reason
with open(path, "a") as handle:
    handle.write(json.dumps(entry, ensure_ascii=False) + "\n")
EOF
}

# last FIELD KIND [TARGETS]: a field of the latest record of that kind (and those targets).
last() {
  python3 - "$records" "$@" <<'EOF'
import json, sys
path, field, kind = sys.argv[1:4]
targets = sys.argv[4].split() if len(sys.argv) > 4 else None
found = None
for line in open(path):
    entry = json.loads(line)
    if entry["kind"] != kind:
        continue
    if targets is not None and entry["targets"] != targets:
        continue
    found = entry
print("" if found is None else found[field])
EOF
}

# build LOG TARGET...: build with live progress lines; the full output goes to the log.
build() {
  local log=$1 status
  shift
  set +e
  incontainer lake build "$@" 2>&1 | tee "$log" |
    grep --line-buffered -E '^(✖|✔|ℹ|⚠) \[|^error|^info: |^Build completed|^Some required|^- ' |
    grep --line-buffered -v ' Replayed '
  status=${PIPESTATUS[0]}
  set -e
  return "$status"
}

reason_of() {
  local reason=$1
  [[ ${#reason} -ge 20 ]] || die "state the reason for this run in at least 20 characters; it is recorded"
  printf '%s' "$reason"
}

command=${1:-}
[[ $# -gt 0 ]] && shift

case "$command" in
  stop)
    active=$(running)
    [[ -n "$active" ]] || { echo "no lake or lean process works in this checkout"; exit 0; }
    echo "$active"
    incontainer kill $(echo "$active" | cut -d' ' -f1)
    ;;

  loop)
    [[ $# -ge 1 ]] || die "usage: just loop \"<Lake targets>\" [acceptance file stem ...]"
    read -r -a targets <<<"$1"
    shift
    stems=("$@")
    for target in "${targets[@]}"; do
      seconds=$(last seconds loop "$target")
      [[ -n "$seconds" ]] || seconds=$(last seconds slow "$target")
      if [[ -n "$seconds" && "$seconds" -gt "$limit" ]]; then
        die "$target took $seconds s in its last recorded run; the short loop has a limit of $limit s.
Give it a row in timing/README.md and repair its cost, or run it with a stated reason:
  just slow \"<reason>\" $target"
      fi
    done
    require_idle
    log=.tmp/logs/$(date -u +%Y%m%dT%H%M%SZ)-loop.log
    start=$(date +%s)
    status=0
    build "$log" "${targets[@]}" || status=$?
    if [[ "$status" -eq 0 && ${#stems[@]} -gt 0 ]]; then
      scripts/accept_files.sh "${stems[@]}" 2>&1 | tee -a "$log" || status=$?
    fi
    seconds=$(( $(date +%s) - start ))
    record loop "$status" "$seconds" "" "${targets[*]}" "${stems[*]}"
    echo "loop: status $status in $seconds s (limit $limit s); log $log"
    if [[ "$seconds" -gt "$limit" ]]; then
      echo "OVER THE LIMIT. A short loop over $limit s is a defect (constitution C24)."
      echo "Add the cost to the table in timing/README.md and repair it, or split the target."
    fi
    exit "$status"
    ;;

  slow)
    [[ $# -ge 2 ]] || die "usage: just slow \"<reason>\" <Lake target ...>"
    reason=$(reason_of "$1")
    shift
    require_idle
    log=.tmp/logs/$(date -u +%Y%m%dT%H%M%SZ)-slow.log
    start=$(date +%s)
    status=0
    build "$log" "$@" || status=$?
    seconds=$(( $(date +%s) - start ))
    record slow "$status" "$seconds" "$reason" "$*" ""
    echo "slow: status $status in $seconds s; log $log"
    exit "$status"
    ;;

  milestone)
    [[ $# -eq 1 ]] || die "usage: just milestone \"<reason>\""
    reason=$(reason_of "$1")
    [[ -z "$(git status --porcelain)" ]] ||
      die "a milestone checks commits: commit the work (and timing/runs.jsonl) first"
    head=$(git rev-parse --short HEAD)
    [[ "$(last revision milestone)" != "$head" ]] ||
      die "the last milestone already ran at $head"
    require_idle
    previous=$(last seconds milestone)
    [[ -z "$previous" ]] || echo "the last milestone took $(( previous / 60 )) min"
    log=.tmp/logs/$(date -u +%Y%m%dT%H%M%SZ)-milestone.log
    start=$(date +%s)
    status=0
    build "$log" CasCompilerTests CasRuntimeTests CasDsl CasDslTests || status=$?
    scripts/accept_files.sh --all 2>&1 | tee -a "$log" || status=$?
    seconds=$(( $(date +%s) - start ))
    record milestone "$status" "$seconds" "$reason" \
      "CasCompilerTests CasRuntimeTests CasDsl CasDslTests" "--all"
    echo "milestone: status $status in $(( seconds / 60 )) min; log $log"
    echo "commit timing/runs.jsonl"
    exit "$status"
    ;;

  *)
    sed -n '2,12p' "$0" | sed 's/^# \{0,1\}//'
    exit 2
    ;;
esac
