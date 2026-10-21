# B0: handoff

The task is the B0 proof of concept, against the unchanged requirements in [INTENT.md](INTENT.md),
[architecture.md](specs/architecture.md) and the
[B0 acceptance table](specs/computational-core-plan.md#acceptance-table). A kernel session
works only by the
[kernel construction procedure](specs/computational-core-plan.md#kernel-construction-procedure-owner-instruction-2026-10-21)
and rewrites this file at its end in the form below (rule 11).

The assignment is paused. Resume only on an owner instruction.

## Branch

`b0/poc-independent-role-integration` at `7591253efc8ad03b3c1de67ced505cd521b2d8e9`. Its kernel
source is `4bc36b61e15ac2bd0abab2a48317d1423ee1b0fe`; the two later commits are documentation.
**Not pushed**: the branch exists only in `/home/dzack/gitclones/lean-cas-dsl/.git`. No worktree
of it exists on disk; create one with procedure rule 10.

No complete report exists for this kernel source (the 2026-10-20 run was stopped with an empty
report). The session starts with the baseline:

```bash
cd ../lean-cas-dsl-b0
git hash-object lake-manifest.json            # record; compare after the run
just track-main
lake build cas-harness
CAS_SAGE_PYTHON=/home/dzack/.local/bin/sage-docker-python \
CAS_GAP_PYTHON=/home/dzack/gitclones/lean-cas-dsl/.venv/bin/python \
lake exe cas-harness --computation-only --report SCRATCH/baseline.json > SCRATCH/baseline.log 2>&1
git hash-object lake-manifest.json
```

## Work list state

| Item | State |
| --- | --- |
| K1 required computations | open (all fifteen held with dispatches at `5410e70`; not yet observed at this kernel source) |
| K2 invalid inverse readings | open |
| K3 required positives | open |
| K4 membership and containment judgments | open |
| K5 closed elements as request data | open |
| K6 operands not formed by a catalogue operation | open |
| K7 maps without an observation decoder | open |
| K8 remaining request-formation gaps | open |
| K9 unavailable requests | open |
| K10 comparison used in execution | open |
| K11 route enumeration bound | open |
| K12 constructor-induced comparison cells | blocked: lean-categories constructor action on comparison cells |

## Noticed, not worked

- `/home/dzack/gitclones/lean-cas-dsl` has the owner's uncommitted `CasCatalogue/Language.lean`
  edit (a zero-family prefilter in `toElement`). It is identical to
  `/tmp/b0-poc-32c3897/original-language-restored.patch`. Leave it untouched (rule 10).
- `git worktree list` shows five prunable entries whose directories no longer exist.

## Owner actions

- Push the construction branch so it exists outside this machine:
  `git -C /home/dzack/gitclones/lean-cas-dsl push origin b0/poc-independent-role-integration`.
