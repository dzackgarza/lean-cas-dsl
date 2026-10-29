#!/usr/bin/env bash
# Invoke the maintained RX-LIFT diagnostic against the existing compiled source.
# CAS_LAKE may name the existing environment's Lake wrapper. Engine and contract
# variables are inherited; no build, dependency update or environment setup runs.
set -euo pipefail

usage() {
  printf 'Usage: %s REPORT_JSON [first|THROUGH_QUESTION_ID]\n' "$0"
  printf 'Set CAS_LEAVES to the diagnostic manifest and optionally CAS_LAKE to a Lake executable/wrapper.\n'
  printf 'The default runs all ten original first-stage questions; a selection runs its complete prefix.\n'
  printf 'Preparation/execution timing is in REPORT_JSON; report-write timing is logged as JSON on stderr.\n'
}
if [[ $# -eq 1 && ( "$1" == --help || "$1" == -h ) ]]; then
  usage
  exit 0
fi
if [[ $# -lt 1 || $# -gt 2 ]]; then
  usage >&2
  exit 2
fi
: "${CAS_LEAVES:?set CAS_LEAVES to the actual independent diagnostic manifest}"
_cas_rx_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
_cas_rx_lake="${CAS_LAKE:-lake}"
case "${_cas_rx_lake}" in
  /*) ;;
  */*) _cas_rx_lake="${PWD}/${_cas_rx_lake}" ;;
esac
case "${CAS_LEAVES}" in
  /*) ;;
  *) export CAS_LEAVES="${PWD}/${CAS_LEAVES}" ;;
esac
if [[ ! -f "${CAS_LEAVES}" ]]; then
  printf 'Diagnostic manifest does not exist: %s\n' "${CAS_LEAVES}" >&2
  exit 2
fi
case "$1" in
  /*) export CAS_READER_REPORT="$1" ;;
  *) export CAS_READER_REPORT="${PWD}/$1" ;;
esac
if [[ -e "${CAS_READER_REPORT}" ]]; then
  printf 'Refuse to overwrite an earlier runtime report: %s\n' "${CAS_READER_REPORT}" >&2
  exit 2
fi
if [[ $# -eq 2 ]]; then
  export CAS_READER_THROUGH="$2"
else
  unset CAS_READER_THROUGH
fi
export CAS_READER_INPUT="${_cas_rx_root}/tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/rx-lift-prescribed-stages.cas"
export LEAN_NUM_THREADS=1
cd "${_cas_rx_root}"
exec "${_cas_rx_lake}" env lean "${_cas_rx_root}/scripts/probes/rx_lift_runtime.lean"
