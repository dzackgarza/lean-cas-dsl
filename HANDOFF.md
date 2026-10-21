# B0: handoff

The task is the B0 proof of concept, against the unchanged requirements in [INTENT.md](INTENT.md),
[architecture.md](specs/architecture.md) and the
[B0 acceptance table](specs/computational-core-plan.md#acceptance-table). The orchestrator's own session is the kernel session
and works only by the
[kernel construction procedure](specs/computational-core-plan.md#kernel-construction-procedure-owner-instruction-2026-10-21)
and rewrites this file at its end in the form below (rule 11).

## Branch

`b0/poc-independent-role-integration` at `7591253efc8ad03b3c1de67ced505cd521b2d8e9`. Its kernel
source is `4bc36b61e15ac2bd0abab2a48317d1423ee1b0fe`; the two later commits are documentation.
**Not pushed**: the branch exists only in `/home/dzack/gitclones/lean-cas-dsl/.git`. No worktree
of it is registered; create one with procedure rule 10.

Latest CI report: none for this kernel source. CI publishes the whole-suite report as the
`acceptance-report` artifact of the Gates workflow on every push to the branch; no full run
happens locally (procedure, "Running checks").

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
| K13 registration gaps (leaf dispatch) | open |
| K14 formed-module positives | open |

## Noticed, not worked

- `/home/dzack/gitclones/lean-cas-dsl` has the owner's uncommitted `CasCatalogue/Language.lean`
  edit (a zero-family prefilter in `toElement`). Leave it untouched (rule 10).

## Owner actions

- Push the construction branch so it exists outside this machine:
  `git -C /home/dzack/gitclones/lean-cas-dsl push origin b0/poc-independent-role-integration`.
