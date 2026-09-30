#!/usr/bin/env bash
# Pin the whole development chain to the committed HEADs: lean-categories into the contract and the
# leaves, the contract into the leaves, all three into this workspace (scripts/pin_dev.py), committing
# and pushing each dependency's pin change. Every checkout must be committed first.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
commit() {
  local dir; dir="$(readlink -f "$here/.lake/packages/$1")"
  if [ -n "$(git -C "$dir" status --porcelain)" ]; then
    git -C "$dir" add lakefile.lean lake-manifest.json
    git -C "$dir" commit -q -m "Pin the development chain

Agent-Role: orchestrator
Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01SKJ21csPEAnJmemqQztSVD"
    git -C "$dir" push -q origin HEAD 2>&1 | grep -v "negotiation\|acknowledg" || true
  fi
}
# lean-categories into the contract and the leaves; then the contract's new head into the leaves;
# then all three here.
python3 "$here/scripts/pin_dev.py" > /dev/null; commit cas_leaf_contracts; commit cas_leaves
python3 "$here/scripts/pin_dev.py" > /dev/null; commit cas_leaves
python3 "$here/scripts/pin_dev.py"
