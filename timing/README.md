# Timing records and cost table

`runs.jsonl` holds one record for each run of `just loop`, `just slow` and `just milestone`
(`scripts/feedback.sh`): time, revision, targets, acceptance files, seconds, status and, for a long
run, its reason. `acceptance.jsonl` holds the seconds of each acceptance worker and its files
(`scripts/accept_files.sh`); the acceptance report of a file (`.tmp/acc/<file>.json`) holds the
milliseconds of each statement and of its setup. Both files are committed with the work that produced them.

## Cost table

Constitution C24 requires this table before any optimization. A row is a measured cost. "Factor"
is how often the cost is paid. Update the row when the cost is measured again; delete it when the
cost is under the limit of the short loop (300 s) and no longer multiplies.

| Operation | Cost per run | Factor | Aggregate | Priority | Proposed remedy | Remaining measured cost |
| --- | --- | --- | --- | --- | --- | --- |
| Milestone (both test aggregates, `CasDsl`, `CasDslTests`, 17 acceptance files) | about 75 min (2026-11-20) | once per batch; it was run after each of about 15 single changes on 2026-11-19 and 20 | about 19 h | 1 | Done: `just loop` is the loop of a change; the milestone needs a reason and a clean tree. | 75 min per milestone |
| `CasRuntime.SessionLiftTests` | 498 s (2026-11-20); it rebuilds after every change to the reader, the lowerer or the runtime | each milestone, and each loop that names it | 8 min per use | 2 | Not known. Profile it (`just profile`): it reads the RX-LIFT statements with a protocol peer, and its statement heartbeat limit was raised. | 498 s |
| `CasDslTests.Boundary` | 474 s (2026-11-20) | each milestone | 8 min per milestone | 3 | Not known. It imports the whole catalogue aggregate to check that the notebook surface declares nothing; measure the import against the check. | 474 s |
| One acceptance file in the short loop (`ellipses`, 8 tests) | 131 to 175 s for the Lean process (2026-11-20, four runs); the loop took 162 to 200 s | each loop that names a file | 3 min per loop; two files pass the limit | 1 | The statements take 36 s (`milliseconds` and `setupMilliseconds` in the report). The rest is the import of the whole catalogue: 20 s when its files are in the page cache, about 110 s when they are not, and on this host (7.9 GB RAM) a build evicts them. `lake`'s up-to-date check adds 20 s. Remedies to measure: an import list for each acceptance file in place of the whole catalogue; one Lean process kept alive between loops. A snapshot copy of the build outputs made the import cold on every run; named files now read the live outputs. | 131 s |
| Acceptance, all 17 files, two workers | about 35 min (2026-11-20, one process per file) | each milestone | 35 min per milestone | 2 | The runner refuses an empty list, so the loop names only the touched files. The seconds of each worker and of each statement are recorded from now on; the next milestone gives the per-file rows. | 35 min |
| Acceptance file `polynomials` | over 6 min alone (2026-11-20; `numbers`, `finite_sets` and `polynomials` together took 15.5 min) | each loop that names it | — | 2 | `polynomials.factors` checks the admission evidence `p ≠ 0` in Lean for about 127 s (handoff note); the task-list row on the evidence presentation (T059) owns the cause. | not measured per statement |
| `CasRuntime.SessionComputationTests` | 173 to 199 s (2026-11-20) | each loop on a statement outcome | 3 min per loop | 4 | Under the limit. It holds eight sessions; split it when it passes 300 s. | 199 s |
| Reader test modules (`CasCompiler.Source…Tests`) | 14 to 58 s each (2026-11-20) | one per loop | under 1 min | — | None. | — |
