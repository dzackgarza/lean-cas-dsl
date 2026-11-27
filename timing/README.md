# Timing records and cost table

The existing feedback commands keep their logs and timing evidence in the repository.
Each invocation of `just loop`, `just slow` and `just milestone` creates
`timing/logs/<UTC>-<command>.<unique>/`. Selected acceptance runs create
`timing/logs/accept-<UTC>-<unique>/` and retain their parent feedback run ID.
Raw logs and checkout evidence remain on disk under the ignored `timing/logs/` directory.
Commit the timing rows and cost conclusions, including failed and interrupted executions.
Each finalized log is identified by its path and SHA256 in its timing row.

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
the existing `timing/logs/` ignore rule applies to these local artifacts. Only after verification and
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
Retain the ordinary files and complete evidence directory under `timing/logs/`;
commit the timing rows that identify their finalized logs by path and hash.
Keep the clean committed-tree requirement unchanged.

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

## T127 statement phase boundaries

At clean revision `1108e97`, `just loop CasRuntime.SessionLogTests` passed in
178.725 s (`20261127T025437Z-loop.vp7tKr`): preparation 51.247 s, build 12.847 s,
execution 113.634 s. It runs only the original `sets.implemented.card_fin` statement
from `sets.cas`, with the real protocol peer and with an empty manifest. The inherited
whole-file assertions remain unchanged in `CasRuntime.SessionFileLogTests`, still included
in the original aggregate.

The peer case held with exactly one `meth.cardinality` registration on `obj.sets.fin`
and took 39.918 s for its statement. The empty case took 19.561 s and ended with
`noImplementation` at `meth.cardinality`, with no dispatch. The native assertions verify
the schema-2 stream, source span, causal parents, setup and statement timing, balanced
lowering, exact prepared/executed descriptor identity, ordered read/lower/prepare/dispatch/
admit/retain boundaries and terminal outcomes.

`FeedbackTests.test_application_log_codec_preserves_exact_values` also passed: 0.003 s
inside unittest, 6.919 s for its public command. Its unchanged test source and original
revision are retained with `codec-result.json` and `codec.log.gz` in the passing run
directory. The original phase run interrupted by TERM (127.120 s) and the failed
JSON-result equality elaboration control (118.977 s) remain in the timing streams and
raw run directories. Required-field extraction was preserved in the corrected comparisons.


## T359: generated-consumer startup in the T300 check (2026-11-27)

The following measurements used the five-case T300 command at
`cc292ef8c4596d1f288deb8294e0c2ff1cdc9ddc`. Its public command selects
`AcceptanceRunTests.test_unread_form_fails_and_peer_dispatches`,
`FeedbackTests.test_extension_is_an_unchanged_kernel_observation`,
`FeedbackTests.test_changed_extension_file_fails_before_execution`,
`SuiteTests.test_empty_selection_is_a_current_failure` and
`SuiteTests.test_missing_input_is_infrastructure_failure` through
`just test-feedback`. Confirmation runs add only unittest's `--durations 0`
reporting option. All five selectors, original inputs and assertions remain.

The baseline bundle is `timing/logs/t300-gate-baseline-cc292ef/`.
Its `cost-evidence.json` retains the gate records and the original native run
summaries, IDs, clocks and log hashes. The bundle retains the incomplete third
measurement as well as the three complete passing checks; incomplete work is
excluded from the passing-run statistics. Raw evidence stays on disk under the
ignored `timing/logs/` path, with the copied console logs compressed and hashed.

### Confirmed trigger

| Measurement | Complete five-case command | Unittest portion | Result |
| --- | ---: | ---: | --- |
| Gate 1 | 774.010554485023 s | 750.661 s | All five cases pass |
| Gate 2 | 504.69886631006375 s | 488.647 s | All five cases pass |
| Gate 3 | Unknown: incomplete measurement | Unknown | Retained; excluded from passing statistics |
| Gate 4 | 1378.6847329642624 s | 1348.504 s | All five cases pass |

For the three complete passing checks, the median is
774.010554485023 s. The spread is the slowest divided by the median,
approximately 1.781222135764739. The procedure's trigger threshold is therefore
300 s times that spread, approximately 534.366640729422 s. The median exceeds
this threshold, so the contingency is required. The source is unchanged across
these baseline runs; their variation is not a measured improvement.

### Non-overlapping baseline accounting

The following partitions the complete command, not just its unittest portion.
The two acceptance workers each have one file. Their recorded startup prefix is
`shared_worker_setup_seconds`: the first session's actual preparation start,
minus the original worker-step start, on the monotonic clock. Prefixes are
counted once per process step and session preparation once per session. File
windows are the original `file.begin` to terminal event. Parent acceptance
phases contain their children, so child totals are not added to parent totals.

| Exclusive interval | Gate 1 (s) | Gate 2 (s) | Gate 4 (s) |
| --- | ---: | ---: | ---: |
| Two worker startup prefixes | 246.000000 | 123.807000 | 252.972000 |
| Four parent/child preparations | 120.998181 | 85.810318 | 102.085602 |
| Four parent/child build-command windows | 102.336909 | 54.782581 | 54.971366 |
| Two original file windows | 47.350000 | 41.398000 | 46.959000 |
| Two session preparations | 1.178000 | 1.040000 | 1.224000 |
| Changed-extension preflight's reported run | 14.698263 | 13.119070 | 16.879220 |
| Empty-selection whole test case | Not separately recorded | 36.094000 | 327.020000 |
| Missing-input whole test case | Not separately recorded | 28.364000 | 400.252000 |
| Remaining unassigned time | 241.449201 | 120.283897 | 176.321545 |
| **Complete command** | **774.010554** | **504.698866** | **1378.684733** |

The unrounded intervals reconcile exactly with each command total. Displayed
values are rounded to six decimals. Gate 1's unassigned pool includes its two
unmeasured SuiteTests case windows; neither is replaced by zero. The pools also
retain fixture creation/retention, runner finalization, time between recorded
boundaries and the outer command. Their mechanism remains unassigned. A
build-command duration does not establish how much native code was recompiled;
the `3979 jobs` success summaries do not distinguish rebuilt jobs from cache hits.

The SuiteTests columns are whole test-case windows, inclusive of their public
`just probe` command and harness. They are not isolated import timings. These
controls reject an empty selection or a missing input and execute no DSL
statement. The two acceptance worker prefixes also include command entry and
Lake setup before session preparation. Their file and session costs are
separately measured above.

For comparison at the same case boundary, gate 2 reports fixture 251.640 s,
extension 141.999 s and changed-extension 30.505 s; gate 4 reports 273.884 s,
299.965 s and 46.831 s respectively. These inclusive case times are another
view of the table and must not be added to its intervals.

### Ordered cost triage and the first remedy

The largest affected operation is startup of the four freshly generated Lean
consumers. The baseline generators omit the `module` header. In pinned Lake,
`prepareLeanCommand` calls `setupExternalModule`, which calls
`fetchTransImportArts` with `!header.isModule`. The non-module path promotes
transitive imports to `importAll` and selects `info.allArts`, including private
artifacts. The module path follows the actual public and meta import graph.
This identifies the redundant loading mechanism without bypassing Lake's
setup or dependency checks. The baseline bundle's
`pinned-lake-source-evidence.json` has SHA256
`e60058f8cd39112d1cffc5918c2b8cb33a6e5cdf561436043e4dc25242bc2c61`;
its pinned `Lake/Build/Module.lean` has SHA256
`cd7b3e4802980fb9a9c1ed116650b2a95231917e4e024ca5b46b4f3821effa5c`.

The baseline bundle's `process-tool-observations.json` retains the live
`t300-gate4-probe-sample` and `t300-gate4-pressure` observations. At
03:54:20 UTC the verified empty-probe Lean process, PID 285599, had
`/proc/285599/io` `read_bytes=8484274176` (`rchar=4663959`) and
RSS 2,897,324 KiB; the associated Lake process had used 19.18 CPU seconds. These
are point-in-time process counters, not an isolated import duration. The
`process-observations.jsonl` stream also retains the third measurement's startup
samples and the fourth measurement's final process observation.

The table uses gate 4 for cost per call and actual multipliers. The startup row
combines the two measured worker prefixes with the two whole SuiteTests windows;
its aggregate is explicitly inclusive of those tests' harness. It is not a
claim that all 980.244 s was spent importing. The rows partition the gate using
the same boundaries as the preceding table.

| Operation or unresolved interval | Cost per call in gate 4 | Actual multiplier | Aggregate | Priority and remedy | Remaining measured cost after the change |
| --- | --- | --- | ---: | --- | --- |
| Legacy generated-consumer startup paths | Worker prefixes 115.815 / 137.157 s; SuiteTests whole cases 327.020 / 400.252 s | Four fresh generated consumers | 980.244 s | First, T359: add the module header in the two existing generators so Lake follows the required import graph. | Pending three complete unchanged checks |
| Unassigned intervals outside the measured windows | Not isolated | Actual residual of this complete gate | 176.321545 s | Keep explicit; attribute from the next complete measurement before selecting another remedy. | Pending |
| Feedback and acceptance preparation | 29.246803 / 30.966544 / 15.444601 / 26.427654 s | Two parent and two child preparations | 102.085602 s | Minutes: retain the actual context/provenance work and reassess after the first remedy. | Pending |
| Explicit build commands | 9.898861 / 19.169869 / 9.594350 / 16.308286 s | Four commands | 54.971366 s | Seconds: preserve the selected dependency targets and actual Lake build. | Pending |
| Original file execution windows | 43.161 / 3.798 s | Two unchanged files | 46.959 s | Seconds: preserve the actual cardinality, unread-form and extension observations. | Pending |
| Changed-extension rejection, reported preflight run | 16.879220 s | One original changed-input control | 16.879220 s | Seconds: preserve the rejection before build/execution; its surrounding harness remains in the residual. | Pending |
| Session preparation | 0.567 / 0.657 s | Two sessions | 1.224 s | Seconds in aggregate: no separate remedy is selected. | Pending |

The T359 change is exactly the `module` header prefix in the acceptance worker
generator in `scripts/accept_files.sh` and in `SuiteTests.run_suite` in
`tests/feedback/test_feedback.py`. Fresh `lake lean`, generated setup, native
CasNative loading, direct imports, Lean options, source inputs and every
assertion remain. No post-change timing or semantic result is established by
this baseline section. T359 remains open until three complete unchanged checks
have median at most 300 s; then work returns to T300. No gain or completion is
claimed before those checks.


### First complete check after the generated module headers

At `3ebdf3d89628a13dd00af8e6f0eab6ee531464ca`, the unchanged five-case
command passed in 517.3431395450607 s on 2026-11-27, starting at
04:10:01.044094 UTC. Its unittest portion was 501.744 s. The case durations
were fixture 222.588 s, extension 166.060 s, changed extension 36.723 s,
empty selection 33.030 s and missing input 43.276 s. These are inclusive
case windows, not isolated native startup measurements.

The durable evidence bundle is `timing/logs/t359-gates-3ebdf3d/`. It retains
this gate's actual result and cost snapshot, compressed original output, and
semantic/setup observations. Later gate records are added there only as they
become available; no collector rerun supplies this first-run evidence.

The observed actual generated setup contains zero private-artifact entries,
compared with 3,947 in the legacy baseline. The canonical full extension report
matches the baseline, with SHA256
`1dd911f14e9e2d10d84547540e55c74c7d2c54b732ecec7e5354a606aaff5c04`.
All five original semantic controls pass. This establishes the observed setup
and report results; one run does not establish a timing gain or completion.

The fixture's original parent and acceptance run IDs are
`20261127T041010Z-loop.WnRedJ` and `accept-20261127T041122Z-pk4vCZ`,
inside its retained `acceptance-kernel-nal8mkwk/checkout/`. The extension's
run IDs are `20261127T041351Z-loop.h5bsoz` and
`accept-20261127T041439Z-vU9Tcg`. The changed-extension preflight is
`20261127T041639Z-loop.GGggM3`, inside the retained
`changed-extension-ikkynwd2/checkout/`. Each original native result and log
remains at its recorded `timing/logs/` location.

#### Ordered exclusive intervals

The table is a complete, non-overlapping partition of the command using the
recorded nested boundaries. A parent acceptance step contains its child run;
a child contains its worker-status window; that window contains the original
worker step. The narrower intervals replace their containing totals instead
of being added to them. Repeated computation rows do not multiply shared costs.

| Recorded interval | Actual count | Seconds | Attribution at this measurement |
| --- | ---: | ---: | --- |
| Preparation | Five parent/child/preflight windows | 115.528048461 | Largest separately timed phase; its suboperations are not isolated and it is not all assigned to cost area E. |
| Worker-step start to first session preparation | Two workers | 93.033070698 | Includes command entry and Lake setup as well as Lean startup. |
| Empty-selection and missing-input whole cases | Two cases | 76.306000000 | Includes their public probe and harness; no DSL statement executes. |
| Explicit build commands | Four commands | 65.106954898 | Command wall time, not isolated compilation time. |
| Case time outside the parent reported run | Three cases | 46.902086090 | Fixture/preflight harness and finalization; archive observations below are nested here. |
| Original file begin to finish | Two files | 42.384000000 | Fixture 38.239 s and full extension 4.145 s. |
| Parent run time outside preparation and named phases | Three parents | 20.805218130 | Gaps between the recorded parent boundaries. |
| Complete command outside unittest | One outer window | 15.5991395450607 | Outer invocation boundary. |
| Child run time outside preparation, build and worker-status window | Two children | 14.494048273 | Child-side setup/finalization between those boundaries. |
| Parent acceptance step outside the child reported total | Two steps | 13.137867073 | Entry and completion around the child's reported window. |
| Worker-status window beyond its original worker step | Two workers | 7.031971897 | Status/step recording and surrounding worker completion. |
| File finish to original worker-step end | Two workers | 5.952734480 | Remaining native/worker completion after file execution. |
| Session preparation | Two sessions | 0.987000000 | Actual prepared-session durations. |
| Unittest total outside the rounded reported case durations | One reconciliation interval | 0.067000000 | Test framework time and reporting precision; not assigned to a native operation. |
| Session preparation end to file begin | Two sessions | 0.008000000 | Recorded native gaps. |
| **Complete command** | | **517.3431395450607** | **Exact reconciliation of the recorded intervals.** |

The preparation calls are 49.539108779 s for the fixture parent,
20.524438369 s for the extension parent, 16.626399260 s and 16.592141761 s
for their respective acceptance children, and 12.245960292 s for the
changed-extension preflight. These five calls supply the first row's actual
multiplier; their total does not identify which operation within preparation
is expensive.

For this finer partition, worker prefixes use the recorded nanosecond step
start and millisecond session-preparation start directly. They are
50.774820992 s for the fixture and 42.258249706 s for the extension.
The existing collector fields instead total 93.034 s because their formula
first floors the step starts to milliseconds. The 0.000929302 s difference
is that known precision convention; it is not additional work. Original file
and session boundaries are used directly for the subsequent intervals.

The worker-status windows are 94.759454890 s and 54.637322185 s, while their
owning steps are 91.475872753 s and 50.888932425 s. Using the former as the
native step would incorrectly absorb another 7.031971897 s into startup or
file execution. The table keeps those wrappers separate.

#### Existing archive observations and remaining measurement gaps

The fixture's case time outside its parent reported run is 17.684004639 s.
Its existing archive window is nested within that interval: wall-clock
nanoseconds 1795752820074379920 to 1795752829981706483, duration
9.907326563 s. The changed-extension case has 23.053682856 s outside its
reported preflight; its archive window is wall-clock nanoseconds
1795753016217313968 to 1795753028446151552, duration 12.228837584 s.
These archive durations are annotations of already counted case windows,
not extra cost rows. Their clock is wall time, distinct from the monotonic
native phase clock, so the two timestamp domains are not aligned or mixed.
The extension case accounts for the remaining 6.164398595 s in that table row.

The next measurement targets preparation's existing operations: the checkout
process guard, native identity/command entry, Lake workspace resolution, and
source/dependency fingerprint capture. The current records do not isolate
those costs. The two SuiteTests also need the probe's command/startup boundary
separated from their whole case before assigning all 76.306 s to startup.
Runner collection, log drain/compression and fixture retention remain
unassigned within the precisely located surrounding intervals. Their sum is
not declared to be one operation or one cost area.

Under the loop-performance procedure, this new table precedes another remedy.
Preparation is top by the currently recorded phase boundary; extending the
private-artifact remedy without attributing the remaining work would bypass
that triage. The unchanged subsequent gates supply the required new median.
No before/after timing gain or T359 completion is claimed from this first
517.3431395450607 s check. The completion target remains a median of three
complete unchanged checks at most 300 s.

The second attempted check at the same revision lost its tool session during
the first fixture. Its outer wrapper remains incomplete with an unknown exit
status. Both actual native runners retained status 143, `TERM`, and incomplete
results; no passing outer duration is inferred. The original output, process
observations, native results and verified fixture archive are retained in the
same evidence bundle. This attempt is excluded from complete-check medians.

The next measurement adds `context-preparation.json` after a successful context
publication. It measures existing identity, Lake resolution, dependency and
source fingerprints, toolchain capture and publication operations separately,
using monotonic clocks. These timings do not enter the original context,
environment or workload fingerprint. Failed captures retain their existing
failure records; the sidecar does not manufacture a successful capture.


### Traced attribution after the generated module headers

The five original cases passed at `f1e9bb0528d4dad793b5560260b8f8bf5f3a736e`
under an explicit process trace. The diagnostic wrapper measured
1050.1462601721287 s, and unittest measured 1021.837 s. Tracing overhead is
included: this is diagnostic evidence, not a normal performance-median sample.
The original result, output, syscall census, context profiles and native
records are retained in `timing/logs/t359-profile-f1e9bb0/`.

The census reconstructs successful executable images, resumed syscalls and
re-exec boundaries. It counts actual Python executables, not Python names in
a wrapper's argv. All 96 Python launches have complete argv and observed
startup bounds. The 22 stdin launches were matched to the existing image
attestation, prior-workload guard, selection readers, worker status and
finalization code. The 95 harness launches are covered by the reviewed
launcher change; the one protocol-peer launch is excluded.

The table below partitions one wall-clock trace envelope, from the first
selected executable entry to the last observed exit. Its intervals are
pairwise disjoint and sum exactly to 1033.911727 s. This envelope differs from
the outer monotonic command measurement; their timestamps are not aligned or
their durations added. Nested Lake calls are removed from their Python
parents. The test-driver lifetime is not counted again around its children.

| Operation or unresolved interval | Cost per call | Actual multiplier | Aggregate seconds | Priority and remedy | Remaining measured cost |
| --- | --- | --- | ---: | --- | --- |
| Automatic initialization of harness Python interpreters | Aggregate / 95; each interval is an observed lower bound | 95 fresh interpreter launches | 249.410591 | First, minutes, cost area E: disable automatic site initialization only at the audited stdlib harness launchers. | Pending normal unchanged checks |
| Generated consumer after its Lean executable entry | 110.390705 / 53.683371 / 37.677226 / 39.923322 s | Two acceptance workers and two SuiteTests consumers | 241.674624 | Minutes: preserve fresh execution, imports and peer. These are enclosing upper windows, not isolated Lean startup. | Pending |
| Unassigned intervals within the observed executable envelope | Not isolated | Exact residual of this envelope | 175.558166 | Keep unresolved; not one operation or one cost area. | Pending |
| Explicit Lake build commands | Aggregate / 4 | Four original commands | 119.553314 | Minutes: retain actual selected dependency builds. This is command time, not isolated compilation. | Pending |
| Lake generated-consumer setup before Lean entry, including Elan | Aggregate / 4 | Four original commands | 117.397924 | Minutes: retain actual setup, options, plugins and native library preparation. | Pending |
| Remaining helper activity after startup, excluding nested native commands | Aggregate over actual helper intervals | Existing helper process intervals; enclosing test-driver body excluded | 68.272145 | Minutes: contains original bookkeeping, fingerprinting and report work; no skip or cache is introduced. | Pending |
| Lake workspace resolution | Aggregate / 4 | Four feedback-context commands | 58.829389 | Seconds: retain fresh dependency selection and provenance. | Pending |
| Lean and Lake version commands | Aggregate over actual version invocations | Four Lake and nine Lean commands | 3.215574 | Seconds: unchanged. | Pending |
| **Observed executable envelope** | | | **1033.911727** | **Exact interval reconciliation.** | |

Each generated-consumer invocation contains exactly one Lean exec with the
matching target path. The pinned Lake source `Lake/CLI/Actions.lean`
prepares the command, spawns the child and waits for it; `Lake/CLI/Main.lean`
awaits that evaluation before exiting. Thus the observed owning Lake exit
bounds its consumer. The four missing Lean exit events remain missing:
241.674624 s is an upper inclusive window, not an invented Lean lifetime.
Even this entire upper window is smaller than the observed 249.410591 s
harness-initialization lower bound. The protocol peer's 3.788222 s startup
bound is nested in the consumer window and is not counted separately.

The successful-context sidecars independently measure the original operations
on their monotonic clock: four Lake resolutions total 59.478413057 s;
66 dependency Git captures total 27.870710974 s; four source fingerprints
total 4.152640155 s. Identity totals 1.742573527 s, toolchain/environment
0.926275340 s, and all configuration/input/workload/publication spans together
0.159783211 s. These values explain the measured preparation work but are not
added to the trace partition. Interpreter initialization occurs before these
sidecars begin.

The remedy adds exactly 40 `-S` argv entries in the existing harness
launchers: 13 in `feedback.sh`, 21 in `accept_files.sh`, one image-attestation
launcher in `container.sh`, the `test-feedback` recipe, and four helper
subprocesses in `test_feedback.py`. The interpreter executable, helper
programs, source inputs, assertions, peer command, manifests, Lean commands,
process ownership, traps and finalization order are unchanged. The commit
hook's comment rule also removes 73 full-line comments from `justfile`,
preserving every recipe shebang and string.

The audited helpers import only the standard library and their existing local
helpers. Native Python 3.14.10's normal startup loaded Sage/IPython and 885
modules; the component observation with `-S` loaded 49. The isolated component
times, 1.708761710 s and 0.057580895 s, are diagnostic observations and are not
multiplied into a claimed whole-loop gain. Numeric limits, decimal context,
encoding and virtual-environment prefixes agree. The only differing
environment name was `MPMATH_NOSAGE`, which none of these helpers consumes;
the peer retains its original site initialization. Python's documented
`-S` option disables automatic `site` processing; it does not enable
optimization or remove assertions:
https://docs.python.org/3.14/using/cmdline.html#cmdoption-S

Both independent reviews restored the exact semantic baseline by removing the
40 flags. The complete test AST and all ten embedded Python ASTs match their
originals after that reversal. The deployed files match the reviewed hashes;
`bash -n`, `just --list`, Python parsing and `git diff --check` pass.
The trace parser, exact argv mapping, reviewed patch and interval partition
are retained with the diagnostic bundle.

Trace SHA256:
`d39136c3df7c3c801c45fa8b8604a178f4aa0341e3e2a8b0cd3edc4fb936f173`.
Compressed trace SHA256:
`b6d4960d7bef081e8f6a82ef7d3db98927343a2e9a587be21efbb07737d261ca`.
Compressed unittest output SHA256:
`521379ae1ca0d8d21d8fcb84bd5784d38a789a02e0c539521d02fbfb4fbe7123`.

This checkpoint establishes the attribution and applies the scoped remedy.
At this revision the timing target applied to the five-case command.
The generic T359 checkbox remains unchecked under the contingency rule.

### Normal recheck and native worker preparation

The three complete, unchanged T300 five-case checks at
4738022fcfeb299c4b80f32f7e5962a027fc2173 all passed their assertions:

| Run | Outer seconds | Unittest seconds | Result |
| --- | ---: | ---: | --- |
| 1 | 287.2983792978339 | 284.767 | 5/5 pass |
| 2 | 374.839264173992 | 371.091 | 5/5 pass |
| 3 | 522.7041107369587 | 514.903 | 5/5 pass |

The median is 374.839264173992 s, so the active T359 instance is not closed.
The exact commands, results and output are in
timing/logs/t359-gates-4738022/. Source, dependency and image identities agree;
these observations do not establish a stable gain from one unusually fast run.

The following ordered triage uses the complete third normal check. Values are
rounded to milliseconds. The residual collects the unassigned intervals; it
is not asserted to be one operation. The named intervals are disjoint: child
acceptance phases are not counted again inside the parent acceptance envelope.

| Operation or interval | Cost per call | Actual multiplier | Aggregate seconds | Priority and remedy | Remaining measured cost |
| --- | --- | ---: | ---: | --- | --- |
| Worker entry to session preparation | 58.159 / 86.452 s | Two workers | 144.611 | First, minutes, area E: remove repeated native Lake workspace and dependency preparation while retaining the full imports and fresh Lean execution. | Pending unchanged normal checks |
| Remaining wrapper, finalization and unassigned intervals | Not isolated | Residual of the whole check | 94.310 | Keep separated from native startup; no remedy is inferred for this residual. | Unchanged |
| Empty-selection and missing-input cases | 42.032 / 45.028 s | Two complete cases | 87.060 | Preserve the original public probe and its failure assertions. | Unchanged |
| Parent, child and preflight preparation | Aggregate / 5 | Five windows | 83.322 | Preserve current source/dependency capture and the native preparation failure controls. | Unchanged |
| Explicit native builds | Aggregate / 4 | Four commands | 62.284 | Preserve the existing builds; share their native workspace and dependency jobs with worker preparation. | Pending |
| Original file execution | 47.851 / 3.266 s | Two files | 51.117 | Preserve statements, peer registration, dispatch and outcomes. | Unchanged |
| **Complete check** | | | **522.704** | | |

A process-only diagnostic of the same check was interrupted by SIGTERM. Its
outer result remains incomplete, with no known outer exit status; it is not a
normal timing sample or a completed five-case check. Its first three unittest
cases passed and both acceptance workers completed before interruption.
Original evidence is retained in timing/logs/t359-startup-4738022/.

Clone/thread ancestry identifies the actual native Lean thread-group exit entries,
including the exit_group calls made by worker threads rather than the exec
thread. The two completed standalone worker Lake preparations take
62.407449 s and 58.006163 s, totaling 120.413612 s before Lean starts.
The subsequent Lake windows, from the child's exit_group entry to Lake's exit,
total 3.880500 s; these also include process termination and reaping.
The native Lean windows, from exec to exit_group entry, are separately
198.686423 s and 122.559144 s; they include import loading and actual execution
and are not all assigned to startup. Completed native Lake envelopes outside
those Lean windows total 503.886827 s: 240.860235 s in
explicit builds, 138.732480 s in resolved-context calls, 120.413612 s in worker
preparation, and 3.880500 s after the child exit entries. These diagnostic wall-clock
intervals are not added to the normal check's monotonic phase measurements.
The exact normal partition and the thread-aware diagnostic partition are in
normal-gate3-phase-partition.json and interrupted-process-partition.json in the
diagnostic directory. completed-worker-native-windows.json retains the separate
native monotonic file/session observations.

The remedy adds a standard Lake target to the existing acceptance build. It
calls the pinned Lake.prepareLeanCommand in that build's existing FetchM and
job store, then atomically publishes all current worker commands. It introduces
no persistent preparation cache. The original generated sources and imports,
native executable, module and package options, plugins, environment overlays
and setup files remain those of lake lean. Required setup serialization still
runs; the two extra Lake processes, repeated workspace loads and repeated
dependency-job discovery are removed.

The existing stdlib feedback helper validates the current context, worker,
source path and exact source bytes, applies the native environment entries in
order, restores Python's interpreter-installed ignored signals, and execs the
prepared Lean command in the existing process group. The original shell
step-start and step-finish boundaries remain, so missing or stale preparation
also retains a current timed failure. The step records name the actual helper
entry command; the same-run preparation manifest retains its exact native
continuation. There is no alternate launch or old-record fallback.

The unchanged native preparation/build and worker interruption controls remain
required. No tests, original acceptance inputs, protocol-peer command or
admission records change. The T359 completion condition remains three complete
normal checks with median at most 300 s followed by the full feedback suite.

### Native import paging after shared worker preparation

The three unchanged normal checks at
495f12754b0ace3af7b28c897ee405696f2633db all pass their original five cases:

| Run | Outer seconds | Unittest seconds | Result |
| --- | ---: | ---: | --- |
| 1 | 418.16677846200764 | 410.387 | 5/5 pass |
| 2 | 451.8845957107842 | 443.610 | 5/5 pass |
| 3 | 467.0192006970756 | 462.106 | 5/5 pass |

The median is 451.8845957107842 s. This does not close T359 or establish
a stable timing gain. The exact commands and results are retained in
timing/logs/t359-gates-495f127/. The fresh complete third-run partition is
gate-3-phase-partition.json in that directory; its disjoint intervals reconcile
exactly to the outer duration. The following table rounds them to milliseconds.

| Operation or interval | Cost per call | Actual multiplier | Aggregate seconds | Priority and remedy | Remaining measured cost |
| --- | --- | ---: | ---: | --- | --- |
| Empty-selection and missing-input public probes | 88.882 / 39.727 s | Two complete cases | 128.609 | First, minutes, area E: isolate native import loading at the unchanged consumer boundary. These are whole cases, not isolated import timers. | Pending |
| Acceptance worker entry to session preparation | 57.617 / 50.068 s | Two workers | 107.685 | The same import-loading investigation; preserve the generated source and native setup. | Pending |
| Parent, child and preflight preparation | Aggregate / 5 | Five windows | 69.819 | Preserve current source and dependency capture. | Unchanged |
| Original file execution | Aggregate / 2 | Two files | 56.783 | Preserve statements, dispatch, admission and outcomes. | Unchanged |
| Explicit native builds | Aggregate / 4 | Four commands | 50.247 | Preserve current native dependency jobs. | Unchanged |
| Remaining wrapper, finalization and unassigned intervals | Not isolated | Disjoint residual | 53.876 | No causal assignment from the residual alone. | Unchanged |
| **Complete check** | | | **467.019** | | |

Read-only process resource samples during the third normal run are retained in
gate-3-resource-samples.jsonl. In the observed 56.749 s before the peer worker's
first application log, the last sample has 16.85 s cumulative process CPU,
1,597,874,176 read bytes and 16,240 major faults. The first sample is after process
birth, so this is not an exact whole-process prefix. Summed thread scheduling
delays are not a complete wall-clock attribution.

A separate import-only component diagnostic uses the exact original module
header and a byte-identical copy of the native worker setup, with Lean's
existing --profile option. It executes no acceptance statement and is not a
replacement timing gate. Native import takes 73.2 s of the 78.46979770809412 s
child duration, with 20,145 major faults. Its output and resource record are in
timing/logs/t359-import-495f127/. All compared setups have SHA256
41b267c76841e52f242ab483de4a7f44012b4915ac7ee8af877895dcb9383a64:
3,941 import entries, no private artifacts, unchanged options and plugins.
Their public interfaces total 992,271,760 bytes, server parts 59,329,936 bytes,
IR signatures 693,616 bytes and IR bodies 250,420,752 bytes.

The pinned Lean compacted-region loader maps files without a read-ahead advice
call. A second component diagnostic advises the exact native importArts paths
with POSIX_FADV_WILLNEED before the same child command. The 15,764 advice calls
take 1.1351758120581508 s; the inclusive diagnostic takes 19.607110326178372 s,
with a 16.3 s native import timer and 3,225 child major faults. Evidence is in
timing/logs/t359-import-prefetch-495f127/. This single comparison does not control
cache state or host contention and establishes no stable speedup. It motivates
the read-ahead experiment measured below.

The remedy reuses the existing feedback helper for both launch sites. The
acceptance path retains its current context and exact-source checks. The public
probe uses a Lake script that follows Workspace.evalLeanFile: one current
workspace, one runBuild/prepareLeanCommand job, and one spawn/wait. Only the
spawned executable and argument prefix change to the stdlib Python exec
prelude; all native environment entries, working directory, standard streams
and process-group settings remain attached to the prepared command.

The common prelude reads that command's exact setup, advises every importArts
path, restores the existing signal defaults and execs the original executable
with the original native arguments and environment. Advice is included in the
existing measured consumer interval. It neither alters artifacts nor
substitutes prior observations; failures are not converted into success.
The tests, generated sources, extension bytes, protocol peer and assertions
remain unchanged.

Native source and advisory-operation references:

- https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/library/module.cpp
- https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/lake/Lake/CLI/Actions.lean
- https://www.man7.org/linux/man-pages/man2/posix_fadvise.2.html

The comparison below repeats the original five-case command three times. The component measurements do not replace it.

### Read-ahead recheck and native probe handoff

The original normal five-case command was repeated three times at
e256b14908ba29d99cbb62815b46deec854acf4d. All assertions passed:

| Run | Outer seconds | Unittest seconds | Result |
| --- | ---: | ---: | --- |
| 1 | 520.5485467547551 | 515.458 | 5/5 pass |
| 2 | 418.8737179939635 | 413.851 | 5/5 pass |
| 3 | 449.6257436098531 | 445.268 | 5/5 pass |

The 449.6257436098531 s median is above 300 s and differs from the preceding
451.8845957107842 s median by less than the observed spread. Read-ahead has
not established a whole-check gain and is removed. The exact commands, outputs
and results remain in timing/logs/t359-gates-e256b14/.

The fresh Step 4 partition uses the complete third run, not the earlier
first-run ordering. normal-gate3-phase-partition.json in that directory
reconciles its disjoint intervals exactly; normal-gate1-phase-partition.json
retains the different first-run partition. Rounded third-run values follow.

| Operation or interval | Cost per call | Actual multiplier | Aggregate seconds | Priority and remedy | Remaining measured cost |
| --- | --- | ---: | ---: | --- | --- |
| Empty-selection and missing-input public probes | 107.979 / 110.613 s | Two complete cases | 218.592 | First, minutes, area E: prepare the exact native command once, then retire Lake before Lean runs. Whole cases include preparation and execution. | Pending unchanged normal trio |
| Parent and child preparation | Aggregate / 4 | Four windows | 52.468 | Preserve current identity and dependency capture. | Unchanged |
| Original file execution | Aggregate / 2 | Two files | 48.248 | Preserve original statements, dispatch, admission and outcomes. | Unchanged |
| Explicit native builds | Aggregate / 4 | Four commands | 47.690 | Preserve current native jobs. | Unchanged |
| Worker entry to Session setup | 14.328 / 25.953 s | Two workers | 40.281 | Already runs after the build Lake exits; preserve current source checks and native setup. | Unchanged |
| Remaining wrapper, finalization and unassigned intervals | Not isolated | Disjoint residual | 27.275 | No causal assignment from this residual. | Unchanged |
| Changed-extension rejection | 15.072 s | One whole case | 15.072 | Preserve its before-execution failure. | Unchanged |
| **Complete check** | | | **449.626** | | |

A read-only process observation during a probe found its live native Lake
parent at 819,380 KiB RSS. This is not a measurement of exclusively reclaimable
physical memory: mappings can be shared. The native prepare/spawn/wait path
nevertheless retains that process while Lean executes. The one-use handoff
removes this overlap; its timing benefit remains to be measured.

The existing stdlib helper now invokes one prepare-only Lake script with
inherited streams, directory, environment and process group. Lake uses the
same runBuild/prepareLeanCommand job, validates the existing inherited
SpawnArgs defaults, and atomically writes its exact executable, arguments and
ordered environment overlay into a private temporary command transport. The
helper waits for Lake to exit successfully before consuming that command.
A signaled preparation child retains native wait-status convention, 128 plus
the signal number. The transport directory is removed before the helper
restores the existing signal defaults and execs the native command. The
native setup file remains alive. No workspace, prepared command or execution
result is cached across invocations.

The worker target and probe share the same native command serialization and
exec owner. Acceptance context, source-path and source-byte checks remain.
The whole preparation and execution stays inside the unchanged public probe
and unittest timing boundaries. Native setup contents, original consumers,
tests, extension inputs, peer protocol and assertions are unchanged.

The implicit-core investigation is retained separately and is not implemented
by this remedy. Read-only mid-import mappings are summarized in
implicit-core-mapping-summary.json; the last sample has 1,160,640 KiB of
private interface mappings but only 60,512 KiB RSS in those mappings. These
are not completed-import totals or per-file fault attribution. The observed
PID's lifetime counters can also include its Python prelude before exec.
Pinned Environment.lean eagerly maps all available interface parts when a
module is absent from importArts; the explicit 3,941-entry setup therefore
does not describe every loaded core artifact. The native API, visibility and
shadowing constraints are retained in builtin-artifact-api-audit.json.
No source import or private artifact is removed on the basis of mapping size.

The [task list](../specs/001-categorical-research-language/tasks.md#phase-0--fast-edit-to-result-feedback) defines the current T300 timing input and the KM0 milestone controls.

## T300 focused runner check and KM0 extension observation, 2026-11-27

The focused command ran the peer-dispatch and changed-extension controls in the Sage container. Both passed. The public command took 262.57 s including startup (256.463 s inside unittest). The fixture checkouts retain the inputs and probe logs.

| Control | Fixture evidence directory under `timing/logs/feedback-tests/` | SHA256 of `public-loop.log` |
| --- | --- | --- |
| Peer dispatch and unread form | `acceptance-kernel-4n425l65` | `a7e3c2ff8d491ed4c374c83394c921830784a75ceb9b8029b093cca595fec2cb` |
| Changed extension | `changed-extension-fl0tw0cs` | `72b1286e263d9d6c0a9ebed68a971e697849e11ef2ea118bc0b5f2a38b0002f7` |

At clean kernel revision `322724d`, the KM0 extension observation passed in 104.72 s including startup. Run `20261127T085652Z-slow.c4O67m` produced all five statement rows for the unchanged RX09 input. The file returned status 1, consistent with the failed statements in its report. The control checked their reporting, source identity and admission status. KM16 owns the mathematical outcomes.

## Current T300 timing closure and KM0 regressions, 2026-11-27

The current focused command is
`just test-feedback AcceptanceRunTests.test_unread_form_fails_and_peer_dispatches FeedbackTests.test_changed_extension_file_fails_before_execution`.
It passed three comparable normal runs in 262.57 s, 220.73482937179506 s and
161.5567361372523 s, measured around the complete public command including startup.
The first measurement is the preceding recorded check; the final two ran at `5b332c4`.
Their median is 220.73482937179506 s and the latest passing run is
161.5567361372523 s. Both meet the 300 s closure bound. This closes the active
process-startup contingency for this focused command; it does not change any of
the historical five-case measurements or establish a causal speedup.

The three peer fixtures have identical input SHA256
`d8ab9de93c523c674a42ec640c8fbe53bdcdb9cfa6724f57a929e183d46485e9`,
Lean version, image digest, and copied runner and peer files. The complete series,
fixture paths and public-log hashes are retained in
`timing/logs/t300-focused-5b332c4/series-summary.json`, SHA256
`58886d97e8d524656dd6c8b7946125fe7a1559f6a02b347216288246f31f4be5`.

The separately prescribed KM0 command ran the unchanged-extension, empty-selection
and missing-input controls with `--durations 0`. All three passed; the complete
public command took 101.07277150824666 s (99.290 s inside unittest).

| KM0 regression | Case duration | Result |
| --- | ---: | --- |
| Complete unchanged RX09 observation | 54.842 s | Pass |
| Empty selection is a current failure | 23.855 s | Pass |
| Missing input is an infrastructure failure | 20.591 s | Pass |

The unchanged RX09 long run is `20261127T090657Z-slow.fH6rCy`. Its file status is
1, as required by the failed kernel observations; the control verifies that the
complete report, source identity, admission status, timing and exit status agree.
The regression transcript is `timing/logs/km0-regressions-5b332c4/gate-1-output.log`,
SHA256 `4f9f48f8e84d1fb1ac8763fde28d4a9be0b9cdad3b4c385b541224a5db627673`.
