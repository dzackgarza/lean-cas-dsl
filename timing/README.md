# Timing records and cost table

`runs.jsonl` records `just loop`, `just slow` and `just milestone`
(`scripts/feedback.sh`). New entries include the command, source and dependency revisions and
diff hashes, input hashes, toolchain and environment context, workload hash, attempted sources,
phase durations and statuses, overall status, and any reason for a long run. A loop records build,
fresh consumer execution and selected acceptance separately. Its unique directory is
`.tmp/logs/<UTC>-<command>.<unique>/`, containing `context.json` and `output.log`.

`acceptance.jsonl` records each selected acceptance invocation (`scripts/accept_files.sh`): input
and manifest hashes, build and worker durations, worker statuses, completeness, outcomes, and the
report hash. Its unique directory is `.tmp/logs/accept-<UTC>-<unique>/`; `<stem>.json` contains the
file's statement and setup milliseconds, `worker<N>.log` contains live completed-statement
diagnostics, and `report.json` contains the current combined report. `.tmp/accept-run.json` is the
latest current report, not a cumulative history. Timing records are committed with the work that
produced them.

Older entries have fewer fields. Their successful build status does not establish fresh consumer
execution. Compare measurements using the recorded source, dependencies, environment and complete
selected inputs; inspect the phase statuses as well as the total.

## Current measured feedback costs

These measurements are from 2026-11-22. Seconds below are rounded to three decimal places; the
JSONL records retain full precision. All acceptance measurements use the entire unchanged named
file, including its original definitions and continuations.

| Workload | Measured cost | Recorded phases or scope | Result |
| --- | --- | --- | --- |
| `ellipses`, original full-file baseline | 74.630 s end to end | Original empty-provider manifest bytes; before context at `8792c0c` | Status 0 under the old runner; not proof of repaired freshness |
| Warm `CasRuntime.SessionTests`, original cached runner | about 18 s | Cached build; the consumer did not execute again | Not a fresh feedback measurement |
| Warm `CasRuntime.SessionTests`, repaired runner | 87.334 s end to end | Build 19.174 s; fresh execution 58.759 s | Status 0; the unchanged public consumer executed again |
| `ellipses`, full file after the producer completeness repair | 96.564 s end to end | All eight named assertions and the original definitions | Status 0; eight reported gaps |
| `ellipses`, full file after the streaming repair | 136.156 s end to end | Same complete input | Status 0 |
| `ellipses`, deliberate producer fault | 81.469 s end to end | Fault reached all 13 original statements after rebuilding the owner | Status 1 |
| `ellipses`, restored producer | 105.302 s end to end | Build 21.800 s; acceptance phase 77.334 s | Status 0 |
| `ellipses`, committed repair with a quoted manifest path | 82.410 s end to end | Complete file at `283e64e`; the compact empty-provider manifest bytes passed through a path containing spaces | Status 0; eight gaps, no historical rows |
| `numbers`, original unmodified full-file worker | about 334 s for the worker | Worker duration, not an end-to-end loop total | 13 holds and 6 gaps, including a definition row |
| `numbers`, current complete acceptance invocation | 303.408 s | Includes actual build and preparation | 19 rows: 18 named assertions; 13 holds and 6 gaps |
| Interrupted-worker regression | 336.056 s for the whole test | Complete `numbers` invocation followed by an actual Lean-worker termination | Passed: the interrupted run failed and inherited no named rows |
| Partial-report regression | 357.937 s for the whole test | Both original consumers finished successfully; one generated `ellipses` row was removed before aggregation | Passed: status 1, incomplete coverage, missing ID identified, no historical replacement |
| Failed parent-build control | 8.851 s | A deliberately absent build target prevented selected acceptance execution | Passed: nonzero status, acceptance unattempted, prior current report archived and absent from the current path |
| Missing local consumer regression | 159.271 s for the whole test | Complete `ellipses` execution 146.477 s; rejected missing local consumer 5.893 s | Passed: status 2, no build attempted, null source hash, previous report archived and no current report |
| `RealizationProfileTests`, existing independent manifest | 66.299 s end to end | Actual `/repos/lean-cas-dsl-leaves/leaves.json`; build 17.942 s, execution 35.302 s | Status 0; the default batch's absent-manifest failure remains recorded |
| `ellipses`, original-manifest owner fault | 217.508 s end to end | Original manifest hash `d2c5de…3732`; build 54.061 s, acceptance phase 155.974 s | Status 1; all 13 original statements reported the deliberate owner fault |
| `ellipses`, exact frozen-owner restoration and original manifest | 134.196 s end to end | Owner bytes restored to `39c1b0c`; build 32.978 s, acceptance phase 94.487 s | Status 0; all eight named assertions reported their current gaps |
| Complete milestone at `39c1b0c` | 7002.597 s end to end | Original four build targets; all 93 source consumers attempted; all 17 acceptance files | Status 1; build 45.548 s, fresh execution 5567.248 s, acceptance phase 1360.793 s |
| Complete acceptance selection within that milestone | 1360.567 s | Both original workers completed with status 1; complete report coverage | All 153 named IDs: 41 holds, 99 gaps, 6 invalid, 5 internal, 2 ambiguous; definition rows: 14 gaps and 1 invalid |

The selected provider context and reported outcomes determine what each execution established.
In particular, the no-provider gaps remain gaps. The phase measurements do not isolate catalogue
import time or identify an algorithmic cause. Both the historical `numbers` worker and the current
complete acceptance invocation exceed the 300-second short-loop bound. Their scopes differ;
these observations do not establish a runtime speedup.

The before-run provider manifest was `{"backends": [], "registrations": []}\n` (SHA-256
`d2c5de0407983489e96660cd889807436fd6d1ff2ed492f00cfa4404128d3732`). Earlier repaired runs,
including the quoted-path control, used the compact serialization (SHA-256
`d9e110fb841d38a0f7ded5ca3041e5a30b4678f860bb996eb55411abbc01e38d`). The decoded manifests
are equal. The final owner fault and exact restoration used the original file and hash, with
unchanged whole ellipses input, dependencies, toolchain and host. The restored owner SHA-256 is
`6cbff16c314b62ed8105bf6fa67da118c10674946ff2bf7a197a5199bac7108a`. No speedup is claimed.

The full batch's `complete=true` means report coverage. Its status remains 1. The compiler
callers `SourceRingTests`, `SourceSubsetTests` and `QuestionObservation` reject an `Array SourceTerm`
where they expect a `SourceTerm`. `RealizationProfileTests` lacks the default provider manifest;
its separate existing-manifest run passes. The named acceptance failures and gaps remain due
under #92 and the existing functional/input owners. Neither report coverage nor holds counts
establish independent mathematical acceptance. The interrupted earlier batch remains recorded
with status 143; it was stopped to repair the missing-local-consumer defect.

## Historical cost table

Constitution C24 requires a measured cost table before optimization. These dated observations
retain the earlier workload and frequency; a current measurement must establish its own scope
and freshness. "Factor" is how often the cost was paid.

| Operation | Historical cost per run | Factor | Aggregate | Priority | Measurement needed | Remaining measured cost |
| --- | --- | --- | --- | --- | --- | --- |
| Milestone (both test aggregates, `CasDsl`, `CasDslTests`, 17 acceptance files) | About 75 min (2026-11-20) | Once per batch; run after about 15 single changes on 2026-11-19 and 20 | About 19 h | 1 | The complete current measurement is above. `just loop` is the change loop; the milestone requires a reason and a clean tree. | Current 7002.597 s; status 1 |
| `CasRuntime.SessionLiftTests` | 498 s (2026-11-20) | Each milestone and each loop naming it; rebuilds after reader, lowerer or runtime changes | 8 min per use | 2 | Profile the whole consumer with `just profile`; it reads RX-LIFT statements using a protocol peer. | Historical 498 s |
| `CasDslTests.Boundary` | 474 s (2026-11-20) | Each milestone | 8 min per milestone | 3 | Measure catalogue import and the notebook-boundary check separately. | Historical 474 s |
| Acceptance file `ellipses`, eight named assertions | Lean process 131–175 s; end-to-end loop 162–200 s (2026-11-20, four runs) | Each loop naming the file | About 3 min per loop; two files exceeded the limit | 1 | The old statement/setup report total was 36 s. Establish the remaining costs with a current profile before attributing them to imports or proposing import changes. | Current complete-file measurements above |
| Acceptance, all 17 files, two workers | About 35 min (2026-11-20, one process per file) | Each milestone | 35 min per milestone | 2 | Current worker and statement records cover the unchanged full selection. | Current 1360.567 s; status 1, complete coverage |
| Acceptance file `polynomials` | Over 6 min alone (2026-11-20); `numbers`, `finite_sets` and `polynomials` together took 15.5 min | Each loop naming it | — | 2 | The earlier handoff noted about 127 s for admission evidence `p ≠ 0` in `polynomials.factors`. The current full-batch statement record is 52.130 s; it does not isolate admission evidence or import cost. | 52.130 s for the statement within the full batch |
| `CasRuntime.SessionComputationTests` | 173–199 s (2026-11-20) | Each loop on a statement outcome | About 3 min per loop | 4 | Measure the complete consumer under fresh execution; profile if it exceeds the loop bound. | Historical 199 s |
| Reader test modules (`CasCompiler.Source…Tests`) | 14–58 s each (2026-11-20) | One selected module per loop | Under 1 min | — | Re-measure when the selected module or its dependencies change. | Historical 14–58 s |
