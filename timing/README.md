# Timing records and cost table

The existing feedback commands keep their logs and timing evidence in the repository.
Each invocation of `just loop`, `just slow` and `just milestone` creates
`timing/logs/<UTC>-<command>.<unique>/`. Selected acceptance runs create
`timing/logs/accept-<UTC>-<unique>/` and retain their parent feedback run ID.
These paths are not ignored. Commit the records and the corresponding run directories with
the source change that produced them, including failed and interrupted executions.

## Feedback checkout evidence

The changed-extension control executes the original public command in an owned
shared Git clone. Its finalizer leaves every tested source, modified input and
diagnostic at the original `checkout/` path. Before retiring the execution
`.git` directory, `scripts/feedback_checkout.py` archives its literal contents
and the complete working tree, retains the exact queried authority blobs as
ordinary files, and verifies an extracted copy against the original bytes,
modes, timestamps, HEAD, refs, index and Git status. The full working-tree
archive also preserves generated files already ignored by the parent repository.

Each `checkout-evidence-*/manifest.json` records the archive hashes, all file
hashes, original external object-store dependencies and the observed available
and missing reachable object IDs. The raw Git metadata keeps those dependencies
unchanged. This preserves the execution's actual state; it does not reconstruct
unrelated missing history or claim the shared clone was self-contained.
The authority input copies retain their original Git object IDs and SHA256 hashes.

The finalizer runs in the existing control's `finally` block. An error before
verified archival leaves the original `.git` in place and records the failure;
there is no ignore rule or clean-tree exception. Only after verification and
durable archive writes is that archived metadata retired. The source and output
files then belong to the parent repository as ordinary evidence, not a gitlink.
If metadata retirement itself fails, the record remains `retirement-failed`;
its verified archive is still restorable after verification is repeated.
Earlier capture or verification failures cannot be restored as successful archives.

An existing owned clone is finalized explicitly with `retain CHECKOUT
--authority-revision COMMIT --authority-path PATH ...`. The paths are the exact
checkpoint and extension input already used by its unchanged-input observation.
`restore EVIDENCE --destination NEW_DIRECTORY` verifies the artifacts and restores
the tested files and literal Git metadata into a new directory. Restoration needs
the original external stores to reproduce their recorded state; the retained
authority blobs and source/diagnostic archives remain directly readable independently.
Commit the ordinary files and complete evidence directory with the producing
source change. Keep the clean committed-tree requirement unchanged.

## Recorded units

| Evidence | Location | Scope |
| --- | --- | --- |
| Run summary | `timing/runs.jsonl`, run directory `result.json` | Complete command, actual result, setup/build/execution/acceptance costs, selected inputs and source/dependency/environment tuple |
| Module starts and results | `timing/modules.jsonl`, run directory `steps/*.json` | One original selected test module, its exact source hash and fresh Lean process, including imports, fixtures, construction and nested work |
| Statement computations | `timing/computations.jsonl`, run directory `computations.jsonl` | Every top-level and executed nested statement, including successful definitions; the actual runner's start and completion events |
| Application events | Run directory `application/*.jsonl` | The native session's ordered diagnostic events, including computation and file starts/completions |
| Run and phase journal | Run directory `events.jsonl` | Starts persisted before setup or execution, completed statuses, and incomplete execution evidence |
| Console diagnostics | Run directory `output.log`; acceptance `build.log` and `worker<N>.log` | The current commands' unfiltered output and actual failures |
| Acceptance summary | `timing/acceptance.jsonl`, acceptance run directory `result.json` | Current input and manifest hashes, worker statuses, timing completeness, report coverage and outcomes |

Each module and computation record includes its run ID, revision, environment, input hash and
`context.json` path. The full context includes source diff hashes, dependency revisions and
diffs, input hashes, toolchain details, command, workload hash and the reason for a long run.
It is captured through the same native build environment for feedback and acceptance.
The initial journal and provisional context are written before expensive setup. If context
resolution itself fails, `context_status` remains `pending`; the failed run does not acquire
a complete environment tuple.

Dependency fingerprints use Lake's loaded workspace, including `--packages` overrides. The
`resolution` field records the actual package directories, configuration files and Lake arguments.
The `timing/` evidence directory is excluded from source and dependency diff/untracked
fingerprints, so creating a run log does not change an otherwise identical workload.
Each dependency's `revision`, changed files and untracked hashes describe that selected directory;
`manifest_pin`, `manifest_path` and `matches_manifest_path` separately describe its relation to the
checked-in manifest. A manifest pin does not identify an overridden source checkout.

## Inclusive costs and shared setup

A module's `seconds` measures its complete fresh Lean process. Its `shared_setup_seconds`
references the same run's preparation and dependency build, which are performed once for the
selection. `inclusive_seconds` is the sum. Several modules therefore share the same setup
cost; their inclusive values must not be summed to estimate the run's wall time. The run's own
`seconds` is the measured end-to-end wall time.

File statement records preserve the native `computation.started` and `computation.timing`
events. Direct public calls preserve `statement.started` and their terminal event; their
identities use the session and original event sequence. A file wrapper owns its contained
statement entrance, so the collector records that computation once. Direct text calls include
parsing, and rejected text retains its actual parse-failure event and measured start.
The original statement text has its own hash; the containing module's input hash comes from
the captured step or context, never a later read of the source file.

`seconds` includes statement execution, source construction, nested work and the setup
required by that statement. File parsing remains in the file's cumulative setup. Direct calls
carry their prior retained definitions' setup in the returned session. A file run includes
that incoming setup and returns its measured file preparation and retained construction
costs for subsequent statements or files, counting each inner execution interval once. Earlier definitions
can be necessary for several later statements, so these inclusive costs overlap. Successful
setup definitions have their own records.

Nested records have `unit=nested_statement` and use the native session plus child-start
sequence as their identity. `parent_computation` and `root_computation` follow the actual
event ancestry. Each record retains its own execution time, the enclosing computation's
setup, the measured shared preflight before the enclosing scope's first child, and the
native runner's preceding retained-sibling setup. The same rule applies through deeper
scopes. These are inclusive, overlapping costs; no future sibling work is charged as
preflight and no shared cost is divided arbitrarily. File `statements`, `executed` and
`records` count top-level items; `nested_records` separately counts actual child starts.

Each statement additionally references the run's shared preparation/build cost, its native
step's startup cost and its own session preparation. The session header names the exact
recorded step and selected source. Startup ends at the first session's measured preparation
start on the same monotonic clock; every session separately measures manifest/profile loading,
owner initialization and source-session construction. The fields `shared_worker_setup_seconds`
and `shared_session_setup_seconds` retain those separate amounts, including for ordinary
module execution. They contribute to `inclusive_seconds` without arbitrary division among
statements. Missing or contradictory startup/preparation evidence leaves the corresponding
cost and inclusive total unknown and coverage incomplete. The acceptance run's wall time and
worker durations remain the appropriate totals for a parallel selection.

A computation executed while Lake builds a dependency uses that step's captured prior setup.
Its owning build is excluded from its shared cost, so its execution is counted once. The
record identifies this boundary as `shared_setup.before_step`. Later fresh module execution
and acceptance workers include the completed dependency build as earlier shared work.

## Failed and partial executions

A module start is persisted before invoking Lean. A completed failure records its real status
and duration; a selected module blocked by setup/build failure records `module.not_run` with
no invented execution duration. A handled interruption records the elapsed partial work and
`complete=false`. If the process is killed before an exit handler can run, the start journal,
context and live logs remain in the repository without an invented completion.

The statement runner writes each computation start before its work and flushes each event.
The acceptance collector reads these native events, including unfinished starts, independently
of the final report. Exact file-run IDs, original statement counts, executed counts and input
hashes check timing coverage, including definitions that need no report row. Missing,
duplicate, malformed or unfinished timing events keep timing coverage incomplete. Each
native trace must retain its original session header and contiguous event sequence; deleting
both ends of a nested computation cannot erase it silently. After a sequence gap, surviving
terminal events and elapsed work remain recorded while completeness stays false.
A complete timing stream cannot repair a missing or corrupted acceptance report.
Interrupted preparation and build phases close their elapsed boundary at interruption and
retain `unfinished_phase`. The generated metadata is replaced atomically. Damaged metadata
still produces an incomplete failure journal while preserving reports supported by the
original context and inventories; it cannot erase another file's completed outcomes.
A paired native file begin and read/parse failure records a complete failed attempt, with
its actual terminal duration, original failure and unknown parsed statement count. Such a
record can belong to a passing invalid-input control; it creates no successful statement.
An unclosed file begin remains incomplete.

A nested record retains the child's staged `outcome` separately from the exact
`enclosing_outcome` and `enclosing_published` result. A staged hold is not promoted to a
public hold. A child with its own completion and a recorded enclosing failure has a
complete timing observation while publication remains withheld. Missing child completion
or enclosing outcome leaves it incomplete. Unattempted continuations remain the original
parent observations; the collector invents no start, duration or child outcome for them.

The report still uses the original admission and regression checks. `<stem>.json` contains the
current file's unchanged outcome records, and `report.json` combines only this selection.
`.tmp/accept-run.json` remains the latest current report. An incomplete report cannot inherit
historical rows, and collecting timings does not regenerate an acceptance baseline.

`tests/feedback/test_feedback.py` retains the original freshness, missing-consumer,
interrupted-worker and damaged-report controls. The module/statement timing control runs
`just loop CasCompiler.ContextTests ellipses` through the original public commands, checks
the complete admitted file, and verifies the persisted records and logs. The warm
`CasRuntime.SessionTests` control checks every direct session entrance and all six top-level and two nested computations
of its original public application-log fixture, including the nested definition, original
causal links, setup costs and separate enclosing publication. That same control removes a
complete interior child pair only from a copy of its actual trace and requires incomplete
timing while preserving later terminal results and the original log. The acceptance timing
control also reuses its actual trace and worker-start record to reject missing or impossible
startup boundaries without replacing them with zero setup. The interruption and
damaged-report controls additionally verify that their current evidence survives failure.

The 300-second development-loop rule is unchanged: an over-limit loop finishes, reports the
warning and records its failure status. Explicit long runs keep their stated reason. Older
entries and `.tmp/logs` evidence retain their historical locations and fewer fields; a
successful old build alone does not establish fresh module execution.

## Original extension observations and outcome columns

`just loop --extension STEM` executes the complete original file under
`tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/`.
The option can be repeated and combined with ordinary module or admitted-file selections.
The input preflight checks the original checkpoint bytes and its recorded source hash;
the three original supplements absent from that checkpoint use their adding revision's
exact Git blob. A changed file or checkpoint fails before native preparation. The
acceptance run retains this authority in `selection.json` and its full input hashes.

Extension workers use the existing `computing` mode. Their report rows carry
`inputKind=extension`, `admitted=false` and `computing=true`; observing a result does not
add the file to the admitted assertion inventory or regenerate an outcome baseline.
The current worker's original result and complete timing/report coverage determine the
command status.

Current report rows retain `kind` and `fails` and include the additive `stratum` column.
An unread source form has `kind=gap`, `stratum=unsupportedSource` and `fails=true`.
Infrastructure failures before interpretation retain `kind=internal`, `fails=true` and
`stratum=null`. The regression comparator accepts older reports without the additive
column using their original kind-based semantics, while an explicit failure or an
`unsupportedSource` stratum remains a failure in current reports. An unchanged `kind`
therefore cannot conceal a newly classified source failure.

## Application traces

A native kernel session writes an append-only JSONL stream through
`CasTools.ApplicationLog`. Feedback and acceptance place it in their run directory's
`application/` subdirectory. Other session entrances use `timing/application/` by default;
`CAS_APPLICATION_LOG_DIR` selects another directory. Diagnostics remain in the file and do
not become ordinary notebook or language output.

Completed historical application streams may be archived as `.jsonl.gz` when their expanded
diagnostic payload is disproportionately large. The corresponding `result.json` keeps the
compressed path and records the compression/verification method; decompression is byte-exact.
Active session streams are always written as ordinary append-only `.jsonl` files.

Each line has `schema`, an independent `session` nonce, an increasing `sequence`,
`parents`, `monotonicMilliseconds`, an `event` name and its structured `data`.
Wire schema 2 stores only `data` as an exact JSON graph with a root and a topologically
ordered node table. Repeated complete JSON values share earlier nodes; no field, selected
structure or provenance is omitted. Number nodes retain the exact integer mantissa and
nonnegative decimal exponent. `CasTools.ApplicationLog.decodeEvent` / `readEvents` and
Python `scripts/application_log.py:loads_application_event` restore the original structured
`data`; the envelope and its schema number stay unchanged. Both readers accept schema 1,
and reject unknown versions, malformed constructors, duplicate keys and invalid references.
The timing collector reads one native line at a time and preserves exact decimal literals
in the expanded start/completion events it writes to derived records.

Parent sequence numbers refer to that same session stream. The nonce is a diagnostic
identifier; creating a log does not allocate a semantic binding or occurrence. The
`session.started` header links the feedback run, context and worker, and records the native
toolchain and supplied session metadata.

Follow a computation from `statement.started` and `statement.read` through
`request.prepared`/`request.execute`, `realization.selected`, `dispatch`,
`reply.admission.started` and `reply.admitted` or `reply.rejected`, then
`binding.retained` and `statement.finished`. These events retain the actual source text and
position, selected reading, prepared operation and operands, chosen registration, reply
admission, binding identities and outcome. `realization.missing` records the operation
address for which the session had no registration. Failed or interrupted statements retain
their emitted events and outcome or interruption entry.

A `statement.child.finished` event can record `staged=true` while its publication remains
`pending enclosing cell`. That describes work retained inside the active transaction.
The enclosing `statement.finished.published` records the actual publication result.
Neither an admitted reply nor a successful child alone establishes that its enclosing cell
committed. File and computation timing events share these session/parent links, so the
duration records can be followed back to the same actual execution.

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

## T354: complete cardinality observations within the focused loop

The consumer is the first original item of `tests/acceptance/sets.cas`,
`sets.card.z4_cubed` (`assert |(ℤ/4)^3| = 64`). The focused
`CasRuntime.SessionCostTests` parses that file, retains the item's original source
context and position, and executes it once through `KernelSession.run` with an
explicit empty manifest. It requires an attempted `noImplementation` outcome at
`meth.cardinality`, zero leaf dispatches, and unchanged source bytes.

The historical statement records at `5f708f9f` and `a3168b87` took 505.564 and
504.462 seconds. The inherited complete snapshot serializers at `51dbfefe` and
guarded graph reuse at `06c0c83` already address that expansion. The current
before-check measurement, `20261127T015147Z-loop.SSPHyT`, completed in 83.703 seconds:
13.437 seconds of preparation, 14.919 seconds of build, and 54.386 seconds of fresh
execution. Its original statement took 22.317 seconds. No additional production
optimization was applied for T354.

### Cost triage

The multipliers below belong to this one-statement consumer. Nested observation and
request costs are included in the statement time; they must not be added to it again.

| Operation | Cost per call in the before-check run | Actual multiplier | Aggregate | Priority and remedy | Remaining measured cost in the three complete checks |
| --- | --- | --- | --- | --- | --- |
| Repeated complete observation transport | Native assembly 0.390 / 0.253 s; readable assembly 0.096 / 0.097 s; graph sharing 0.688 / 1.192 s | Two prepared requests | 2.716 s, nested | The historical superlinear row comes first. Existing retained-owner snapshot memoization and completed-object graph traversal preserve sharing before transport; every field remains. | Native 0.537–0.684 s; readable 0.154–0.212 s; sharing 1.709–2.055 s, each total over both requests |
| Full request preparation | 1.352 / 2.235 s | Two requests | 3.587 s, nested | Includes the observation row; no further work is needed for the focused bound. | 3.183–3.868 s over both requests |
| Original statement execution | 22.317 s | One statement | 22.317 s | The registered missing implementation is the required kernel outcome. Remaining runtime cost belongs to later performance work. | 21.697–23.668 s |
| Build of the actual imports | 14.919 s | One build | 14.919 s | Preserve the focused dependency target. | 8.936–14.544 s |
| Feedback preparation | 13.437 s | One preparation | 13.437 s | Preserve actual environment and dependency capture. | 10.088–30.474 s |
| Fresh Lean execution outside the statement | 32.069 s | One process | 32.069 s | Includes imports, fixture setup and log checks; no isolated startup improvement is claimed. | 25.166–61.255 s, now including the full descriptor assertions |

The two actual prepared descriptors contain 1,417 and 1,439 canonical graph nodes.
Expanding their child references as trees would visit 2,560,189 and 5,499,810 nodes.
Those logical values remain present. The serializer and codec reuse immutable
subgraphs instead of repeatedly traversing expanded copies.

### Complete check

At committed revision `14b0cff`, the complete test compares every actual prepared and
executed observation with its raw schema-2 wire graph: decoding and canonical
re-encoding must reproduce the entire graph. It also checks the exact inventories
of all four descriptor fields, both native fields, all twelve request fields and all
eight readable fields. Requests are matched by their original program and occurrence;
their complete native and readable descriptors must agree before execution and at
execution. Selection and source-snapshot fields remain present in each roundtrip.

| Run | Whole loop | Build | Fresh execution | Status |
| --- | --- | --- | --- | --- |
| `20261127T015501Z-loop.6QA7X4` | 130.730 s | 14.544 s | 84.923 s | Pass |
| `20261127T015712Z-loop.omSWkT` | 84.645 s | 14.121 s | 59.073 s | Pass |
| `20261127T015838Z-loop.5w1xdP` | 66.822 s | 8.936 s | 46.972 s | Pass |

All three runs used the same committed consumer bytes, reported clean source, and
executed the complete check. Their median is **84.645 seconds**, below 300 seconds.
The observed slowest-to-median spread is 1.544; differences within that spread are
not reported as performance gains.

The earlier interrupted setup (`20261127T014209Z-loop.PBlehd`, status 143) and initial
test type-inference failure (`20261127T014542Z-loop.fuGoWT`, status 1) remain recorded.
Neither executed the statement, and neither is a passing performance observation.
The corrected before-check run and all three complete checks are retained in
`runs.jsonl` and `modules.jsonl`; their raw logs remain at their recorded disk paths.

## T112 terminal timing records

At `99824a6`, the exact three-case feedback gate passed in 228.308 s end to end
(221.707 s reported by unittest): `FeedbackRecordTests.test_passing_module_writes_one_row`,
`FeedbackRecordTests.test_failing_module_writes_fail`, and
`FeedbackRecordTests.test_terminated_run_writes_interrupted`. Every check runs the public
`just loop` command in its owned core-only checkout. The controls verify the twelve terminal
fields against actual Git, Lean/image, source, step, signal and gzip-byte evidence.

| Native run | Target | Terminal status | Public loop seconds |
| --- | --- | --- | ---: |
| `20261127T023654Z-loop.f0S5JZ` | `FeedbackPass` | pass | 48.592 |
| `20261127T023759Z-loop.sgUZWb` | `FeedbackFail` | fail | 42.647 |
| `20261127T023856Z-loop.aZt1QX` | `FeedbackPass` | interrupted | 51.059 |

The exact emitted module and run rows are retained in their existing JSONL streams. Their
run directories are also retained at the recorded paths, with unchanged compressed log bytes.
The complete outer gate log and result are under `timing/logs/t112-feedback-gate-99824a6/`.
The earlier 358.816 s failed fixture gate remains there too: its initial passing fixture
needed an explicit IO type, and its interruption scan missed a child created by a Lake
worker thread. The corrected fixture writes directly to its original output handle; process
scans cover every thread while preserving command, directory and group ownership checks.

Native container controls verified the actual image digest, stdin, exit status, host TERM
propagation and direct-container image provenance. A baseline now requires its final
`run.finished` event. All 2,348 formerly indexed raw log files were removed from the index
with their on-disk SHA-256 values unchanged; `git ls-files timing/logs` is empty.
