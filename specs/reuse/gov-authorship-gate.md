# Reuse record: `gov-authorship-gate`

`scripts/check_authorship.py`: a commit's `Agent-Role` must match its paths, and each author writes in one role, across the four repositories.

## Queries
- git's own mechanisms: commit trailers (`git interpret-trailers`, `%(trailers)`), used as the declaration; `CODEOWNERS` (GitHub) assigns reviewers by path but cannot tell agents apart when one account pushes every commit;
- existing gates in this repository: `check_acceptance_permanent.py`, `check_reuse_records.py` (the same Python-gate shape, reused).

## Owner
- git (`log --since`, `diff-tree`, trailers); the Python standard library.

## New code
The mapping from paths to roles and the per-author role check: no tool relates git authorship to this programme's layers.
