# Reuse record: `gov-readmission-gate`

`check_acceptance_permanent.py` admits or corrects assertions only under `AGENT_ROLE=acceptance`; `check_authorship.py` assigns a change to `admitted.json`'s assertions or corrections to the acceptance role.

## Queries
- the existing permanence script (extended in place, not duplicated).

## Owner
- `scripts/check_acceptance_permanent.py`.

## New code
One environment check and one content-aware path rule.
