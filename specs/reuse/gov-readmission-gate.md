# Reuse record: `gov-readmission-gate`

The existing permanence checker is read-only. The former caller-set role label and
admission/correction/retirement commands have been removed; accepted inputs belong to the
independent acceptance transition, not a candidate check.

## Queries
- Existing permanence checker and its build/CI callers.
- Existing accepted-ledger and independent acceptance requirements in architecture policy 2.

## Owner
- `scripts/check_acceptance_permanent.py` and the existing acceptance review channel.

## New code
A read-only accepted-ledger input and regression tests for the observed self-admission channel.
No replacement role label or approval service is introduced.
