#!/usr/bin/env bash
# Run acceptance files and compare every outcome with .tmp/accept-prev.json.
# Named files read the live build outputs (they are in the page cache; a copy imports about 90 s
# slower). Do not build while they run: `just loop` runs one thing at a time.
# `--all` reads a snapshot of the build outputs, so builds may proceed during the long run.
# With no leaves installed, a gap with NoImplementation is the correct outcome.
# Usage: scripts/accept_files.sh <stem> [stem ...]   the files that the change touches
#        scripts/accept_files.sh --baseline          make the last merged run the comparison base
# Every file is the long run: `just milestone "<reason>"` (it passes --all).
# The seconds of each worker and its files go to timing/acceptance.jsonl.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/container.sh
dexec() { incontainer "$@"; }

if [[ "${1:-}" == "--baseline" ]]; then
  cp .tmp/accept-run.json .tmp/accept-prev.json
  exit 0
fi

snapshot=false
if [[ "${1:-}" == "--all" ]]; then
  snapshot=true
  stems=()
  for f in tests/acceptance/*.cas; do stems+=("$(basename "$f" .cas)"); done
else
  stems=("$@")
fi
if [[ ${#stems[@]} -eq 0 ]]; then
  echo "name the acceptance files that the change touches (stems of tests/acceptance/*.cas)." >&2
  echo "Every file is the long run: just milestone \"<reason>\"" >&2
  exit 2
fi

dexec lake build LeanCategories.Catalogue CasCatalogue.TestSuite >/dev/null
path=$(dexec lake env printenv LEAN_PATH)
if $snapshot; then
  mkdir -p .tmp/snap && rsync -a --delete .lake/build/lib/lean/ .tmp/snap/lean/
  path=${path//"$root/.lake/build/lib/lean"/"$root/.tmp/snap/lean"}
fi

mkdir -p .tmp/acc
[[ -f .tmp/empty-leaves.json ]] || printf '{"backends": [], "registrations": []}\n' > .tmp/empty-leaves.json
# One Lean process imports the whole catalogue once (minutes). The files are therefore shared
# between at most two workers, and each worker reads its files one after the other.
workers=2
if [[ ${#stems[@]} -lt $workers ]]; then workers=${#stems[@]}; fi
for worker in $(seq 0 $(( workers - 1 ))); do
  printf 'import LeanCategories.Catalogue\nimport CasCatalogue.TestSuite\n\n' > ".tmp/acc/worker$worker.lean"
done
for index in "${!stems[@]}"; do
  stem=${stems[$index]}
  [[ -f "tests/acceptance/$stem.cas" ]] || { echo "no acceptance file $stem" >&2; exit 1; }
  mkdir -p ".tmp/acc/$stem"
  ln -sfn "../../../tests/acceptance/$stem.cas" ".tmp/acc/$stem/$stem.cas"
  if [[ -f ".tmp/acc/$stem.json" ]]; then mv -f ".tmp/acc/$stem.json" ".tmp/acc/$stem.previous.json"; fi
  printf '#cas_tests ".tmp/acc/%s" manifest ".tmp/empty-leaves.json" reporting ".tmp/acc/%s.json"\n' \
    "$stem" "$stem" >> ".tmp/acc/worker$(( index % workers )).lean"
done

export root path
run_worker() {
  local worker=$1 start
  start=$(date +%s)
  incontainer env LEAN_PATH="$path" lean ".tmp/acc/worker$worker.lean" > ".tmp/acc/worker$worker.log" 2>&1 || true
  echo $(( $(date +%s) - start )) > ".tmp/acc/worker$worker.seconds"
}
export -f run_worker incontainer
seq 0 $(( workers - 1 )) | xargs -P "$workers" -I{} bash -c 'run_worker {}'
mkdir -p timing
for worker in $(seq 0 $(( workers - 1 ))); do
  files=$(grep -o '"\.tmp/acc/[a-z_]*"' ".tmp/acc/worker$worker.lean" | tr -d '"' | sed 's#.tmp/acc/##' | paste -sd' ')
  printf '{"utc": "%s", "revision": "%s", "files": "%s", "seconds": %s}\n' \
    "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$(git rev-parse --short HEAD)" "$files" \
    "$(cat ".tmp/acc/worker$worker.seconds")" >> timing/acceptance.jsonl
done

python3 - "${stems[@]}" <<'EOF'
import json, os, sys, collections
order = {'holds': 0, 'gap': 1, 'unavailable': 1, 'ambiguous': 2, 'invalid': 2, 'malformed': 2,
         'wrong': 2, 'internal': 3}
key = lambda x: (os.path.basename(x['file']), x['id'])
prev = {key(x): x for x in json.load(open('.tmp/accept-prev.json'))}
run = {}
if os.path.exists('.tmp/accept-run.json'):
    run = {key(x): x for x in json.load(open('.tmp/accept-run.json'))}
else:
    run = dict(prev)
missing = []
for stem in sys.argv[1:]:
    report = f'.tmp/acc/{stem}.json'
    if not os.path.exists(report):
        missing.append(stem)
        continue
    run = {k: v for k, v in run.items() if k[0] != f'{stem}.cas'}
    for x in json.load(open(report)):
        x['file'] = f'tests/acceptance/{stem}.cas'
        run[key(x)] = x
json.dump(list(run.values()), open('.tmp/accept-run.json', 'w'), indent=1)
print(collections.Counter(x['kind'] for x in run.values()))
for stem in missing:
    print(f'NO REPORT {stem}: see .tmp/acc/worker*.log')
for k, x in run.items():
    p = prev.get(k)
    if p is None:
        print('NEW', k[1][:50], x['kind'])
    elif order[x['kind']] > order[p['kind']]:
        print('WORSE', k[1][:50], p['kind'], '->', x['kind'], x['detail'][:140])
    elif order[x['kind']] < order[p['kind']]:
        print('better', k[1][:50], p['kind'], '->', x['kind'], x['detail'][:100])
for k in prev:
    if k not in run:
        print('LOST', k[1][:50])
EOF
