#!/usr/bin/env bash
# Run acceptance files against a snapshot of the build outputs, two Lean processes at a time,
# and compare every outcome with .tmp/accept-prev.json. Builds may proceed while it runs.
# With no leaves installed, a gap with NoImplementation is the correct outcome.
# Usage: scripts/accept_files.sh [stem ...]   (default: every tests/acceptance/*.cas)
#        scripts/accept_files.sh --baseline   (make the last merged run the comparison base)
set -euo pipefail
cd "$(dirname "$0")/.."
root=/repos/v1-integration-20261106/lean-cas-dsl
export DOCKER_HOST="unix:///run/user/$(id -u)/docker.sock"
dexec() { "$HOME/bin/docker" exec -i -w "$root" sage-research "$@"; }

if [[ "${1:-}" == "--baseline" ]]; then
  cp .tmp/accept-run.json .tmp/accept-prev.json
  exit 0
fi

stems=("$@")
if [[ ${#stems[@]} -eq 0 ]]; then
  for f in tests/acceptance/*.cas; do stems+=("$(basename "$f" .cas)"); done
fi

dexec lake build LeanCategories.Catalogue CasCatalogue.TestSuite >/dev/null
mkdir -p .tmp/snap && rsync -a --delete .lake/build/lib/lean/ .tmp/snap/lean/
path=$(dexec lake env printenv LEAN_PATH)
path=${path//"$root/.lake/build/lib/lean"/"$root/.tmp/snap/lean"}

mkdir -p .tmp/acc
[[ -f .tmp/empty-leaves.json ]] || printf '{"backends": [], "registrations": []}\n' > .tmp/empty-leaves.json
for stem in "${stems[@]}"; do
  [[ -f "tests/acceptance/$stem.cas" ]] || { echo "no acceptance file $stem" >&2; exit 1; }
  mkdir -p ".tmp/acc/$stem"
  ln -sfn "../../../tests/acceptance/$stem.cas" ".tmp/acc/$stem/$stem.cas"
  rm -f ".tmp/acc/$stem.json"
  printf 'import LeanCategories.Catalogue\nimport CasCatalogue.TestSuite\n\n#cas_tests ".tmp/acc/%s" manifest ".tmp/empty-leaves.json" reporting ".tmp/acc/%s.json"\n' \
    "$stem" "$stem" > ".tmp/acc/$stem.lean"
done

printf '%s\n' "${stems[@]}" | xargs -P 2 -I{} sh -c \
  '"$HOME/bin/docker" exec -i -w '"$root"' -e LEAN_PATH='"$path"' sage-research lean .tmp/acc/{}.lean > .tmp/acc/{}.log 2>&1 || true'

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
    print(f'NO REPORT {stem}: see .tmp/acc/{stem}.log')
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
