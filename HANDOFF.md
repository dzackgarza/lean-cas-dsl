# B0: handoff

The task is the B0 proof of concept, against the unchanged requirements in [INTENT.md](INTENT.md),
[architecture.md](specs/architecture.md) and the
[B0 acceptance table](specs/computational-core-plan.md#acceptance-table). The orchestrator's own session is the kernel session
and works only by the
[kernel construction procedure](specs/computational-core-plan.md#kernel-construction-procedure-owner-instruction-2026-10-21)
and rewrites this file at its end in the form below (rule 11).

## Branch

`b0/kernel`, pushed to `origin/b0/kernel`; its head is the commit carrying this file. Work in
`../lean-cas-dsl-kernel` (procedure rule 10). It descends from
`b0/poc-independent-role-integration` (`7591253`, pushed) and merges `main`.

Latest CI report: Gates run `39630187816` at `adaec09`, artifact `acceptance-report`
(`gh run download 39630187816 -R dzackgarza/lean-cas-dsl -n acceptance-report`): 75 holds,
65 gaps, 12 unavailable, 1 internal; 9 request-formation gaps, against 101 at `5410e70`.
Local targeted reports are in `/home/dzack/gitclones/lean-cas-dsl-reports/`.

## Work list state

| Item | State |
| --- | --- |
| K1 required computations | closed: all fifteen hold with dispatches (`f208613-…-targeted-k1k2.json`) |
| K2 invalid inverse readings | condition met: no ID invalid, all five form requests (`f208613-…-targeted-k1k2.json`); blocked: question-preservation assessment of their changed questions |
| K3 required positives | every assertion forms its request (`*-targeted-K3`, `*-targeted-pv5`); blocked: leaf registrations (K13) and acceptance admission (owner) |
| K4 membership and containment judgments | closed: no K4 ID is a request-formation gap in CI `adaec09` |
| K5 closed elements as request data | open: `series.coefficient_{zero,two,three,four}` blocked: no `lean-categories` object presents `Series.powerSeriesTAdic R`; `integration.normalized` internal heartbeat timeout (rule 4) |
| K6 operands not formed by a catalogue operation | closed: no K6 ID is a request-formation gap in CI `adaec09` |
| K7 maps without an observation decoder | closed: no K7 ID is a request-formation gap in CI `adaec09` |
| K8 remaining request-formation gaps | open: condition met in targeted reports (`*-targeted-lim`, `*-targeted-par2`, `*-targeted-rest`); awaiting one CI report at or after `d838691` |
| K9 unavailable requests | closed: requests use the declared `extent` and `constructionApex` forms (contract `f7b047b`); the backend errors are leaf work (`*-targeted-rest2`) |
| K10 comparison used in execution | open |
| K11 route enumeration bound | open |
| K12 constructor-induced comparison cells | blocked: lean-categories constructor action on comparison cells |
| K13 registration gaps (leaf dispatch) | open |
| K14 formed-module positives | open |

## Noticed, not worked

- `/home/dzack/gitclones/lean-cas-dsl` has the owner's uncommitted `CasCatalogue/Language.lean`
  edit (a zero-family prefilter in `toElement`). Leave it untouched (rule 10).
- CI "The kernel carries no mathematics" fails at the branch base: seven probe modules are not
  imported by `CasGates.KernelPurity`, and `CasCatalogue.Semantic` refers to
  `LeanCategories.Catalogue.Realization`, which is outside `allowedModules`.
- CI "Build and audit": `CasAcceptance/LiftProbes.lean:29` is ambiguous on `kernel` (two
  structural routes, no registered comparison); this is K12's probe.
- Reading `h(0)` inside the comprehension of `integration.normalized` takes 113 s; its
  realization then exhausts heartbeats in `whnf`.

## Owner actions

- Question-preservation assessment (construction directive B): CI's
  `check_question_permanence.py` reports every ID changed, because
  `CasAcceptance/Permanent/questions.json` records an older hash format and a question identity
  embeds the `lean-categories` revision. The kernel changes of 2026-10-21 also add trace node kinds
  (`objectField`, `powerObjectMap`) to the questions that use them.
- Decide whether `LeanCategories.Catalogue.Realization` (typed catalogue realization witnesses)
  belongs in `CasGates.KernelPurity.allowedModules`.
- `lean-categories` has no registered object for `Series.powerSeriesTAdic R`, the summable-families
  parameter of the power-series sum binder; no acceptance-table row names it.
