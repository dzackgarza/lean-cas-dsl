# Contribution references

- [Permanent constitution and independent-author/input boundaries](.specify/memory/constitution.md)
- [Current FR-012–FR-015: independent formalization and computation-only leaves](specs/001-categorical-research-language/spec.md)
- [Current source contract: actual cells, allowed choice data, mandatory errors and separate responsibilities](specs/001-categorical-research-language/contracts/mathematical-input.md)
- [Released computational-interface design and public-only handoff boundary](specs/001-categorical-research-language/contracts/computational-runtime.md)
- [Contribution policies and permitted inputs](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6574924066)
- [Architecture, ownership and evidence](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574949858)

The linked policies determine which inputs each author may receive. The rules below apply to
implementation contributions; the released leaf contract retains its own owner.

The maintained [mathematical execution model](specs/architecture.md) reconstructs the *owner's* intended category-level software encapsulation, not merely a set of prohibitions. A category-aligned computational leaf may realize multiple accepted **constructors, common methods and immediate functor actions**, whereas one manifest `(operation, input form, backend)` is a **computational registration**, not the category itself. For the owner design statements in summary, see [#91 source A](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942015918), [formal contract B](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942060158), and [current implementation map C](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942116552). They are source input for the requirements, not a new acceptance process.

## Mathematical implementation rules

Read [the execution model](specs/architecture.md) before designing a fix. These rules apply C23;
they do not grant kernel or leaf authors authority to create missing mathematics.

| Rule | Required contribution | Defective substitute |
| --- | --- | --- |
| MATH001 | Name the source declaration, formal domain, selected data and consuming continuation. | Start from a backend class or serialized shape. |
| MATH002 | Compute functor targets through public object and morphism constructors; use the resulting target interface. | Add private cross-leaf conversions or per-source forwarding methods. |
| MATH003 | Derive inherited applicability from the accepted composite and its comparisons, including arrow actions. | Select the shortest or first registered route, or equate routes by endpoints. |
| MATH004 | Apply the declared classifier refinement using its evidence; retain any selected structure. | Infer mathematical membership from a list, or treat existence as a chosen basis. |
| MATH005 | Repair the boundary that lost a selected occurrence, endpoint or cone and update its consumers. | Recover a candidate by equal expressions, registry scans or apex recognition. |
| MATH006 | Prepare dependent inputs from their formal interface and route every public call through common preparation. | Add a named-construction runtime algorithm or a separate deferred-call interpreter. |
| MATH007 | Preserve the unchanged public mathematical workload and independent extension consumer. | Replace it with an opaque provider, helper assertion or dispatch count. |
| MATH008 | Consume new accepted declarations through the same generic kernel; run the prescribed extension trials against their frozen kernel, contract and old consumer. | Add a recognizer or repair an old leaf to accommodate the trial. |

Explain the required mathematical relationship and its retained computational association in the
change's rationale. Verification must distinguish structural transport checks from mathematical
correctness and independent acceptance. Documentation of a requirement does not establish its
implementation. An upstream formal gap is a lean-categories task that the task list holds before
its consumer. The workstream does that task in lean-categories as a formalization author, from the
mathematics ([execution order](specs/001-categorical-research-language/tasks.md#execution-order));
a downstream repair cannot invent the missing theorem or definition.

## Task rows and open questions

**SPEC001 — a task row holds a requirement, not a decision.** A task row that says "decide X
against the contract", written where two implementations differ => read the specification, the
data model and the contracts; write the passage that settles X and its acceptance condition in the
row. A question that none of them settles is a gap of the specification: it goes to
`/speckit-clarify` and into `spec.md`, and the task names that clarification as its input.

**SPEC003 — a task names its check.** A task written as a list of obligations ("retain each
mandatory datum's source boundary …") with requirement traces and no observable test => one
mechanism, its files, one check (`just loop "<test module>" [acceptance files]` within 300 s,
with a protocol peer or an empty manifest), the reason that the check fails at the tip, its inputs
and its trace. An obligation with no check goes into the task whose check covers it.

**SPEC002 — "no test states it" is not a status.** "The required behaviour has no test, so the
item is open" => derive the acceptance condition from the governing passage, write the failing
test, then repair.

## Feedback loops

Use the selected toolchain and dependency tuple of the kernel implementation worktree (locate it
with `git worktree list`). These recipes describe that checkout; documentation on `main` does
not establish that its implementation commands are present there. Dependency refresh and SDK
setup are explicit operations.

`scripts/feedback.sh` runs from the host or inside the research container. For a named local
module, the focused command builds its `+Module:deps` and then uses `lake lean` to execute the
actual source afresh. An explicit `+Module:facet` selects an artifact build and requires a
selected acceptance consumer in the same invocation. For example,
`just loop "+CasCatalogue.TestSuite:leanArts" ellipses` rebuilds the suite producer and runs the
whole unchanged `tests/acceptance/ellipses.cas` file.

| Command | Use | Bound and records |
| --- | --- | --- |
| `just loop "MODULES" [FILE …]` | After a change: freshly execute the test modules of the changed mechanism, then the complete affected acceptance files. Put several modules in the quoted argument; file arguments are stems of `tests/acceptance/*.cas`. | 300 seconds for the whole command. A completed overrun returns nonzero and records both the execution outcome and the exceeded bound. There is no kill timer. |
| `just loop "+MODULE:FACET" [--manifest PATH] FILE …` | Build the named artifacts and run their selected public acceptance consumer. | The same ordinary-loop bound; an artifact build alone cannot supply the consumer result. |
| `just slow "REASON" TARGET … [-- acceptance arguments …]` | Run the same selected workload explicitly when it needs longer. Use `--` before acceptance arguments, including an optional `--manifest PATH`. | Record a reason of at least 20 characters. The command is allowed to finish without the ordinary-loop bound. |
| `just milestone "REASON"` | After a batch and before its kernel-branch push or handoff: build both test aggregates and the notebook targets, freshly execute their test modules, and run every acceptance file. | A stated reason and clean committed tree are required. Current costs belong in `timing/README.md`. |
| `just stop` | Stop every `lake` and `lean` process of this checkout. A build started through `docker exec` can continue after its caller stops. | — |
| `scripts/accept_files.sh [--manifest PATH] FILE …` | Run complete selected acceptance files. An empty selection is refused. Do not build concurrently: the consumer reads the live build outputs. | Per-run build, worker and total times go to `timing/acceptance.jsonl`; each statement and its setup retain their timing in the report. |
| `just test-feedback [TEST …]` | Check changes to feedback mechanics through the actual process and report regression controls in the research container. Optional unittest selectors rerun only the named controls. | Run for changes to the feedback commands or report producer, rather than for each mathematical source edit. |
| `just probe FILE` | Elaborate a temporary Lean file after Lake rebuilds its imports. | — |
| `just build-production` | Build the connected `CasRuntime.Session` production closure without test modules. | — |
| `just setup-sdk` | Provision the pinned contract SDK environment once before protocol tests. | — |
| `just profile TARGET` | Run a separate diagnostic profile when that measurement is needed. | — |

An acceptance invocation without `--manifest PATH` uses the empty-provider diagnostic. Supply
the actual manifest for a provider-backed observation, for example
`just loop "+CasCatalogue.TestSuite:leanArts" --manifest PATH ellipses`.
A `gap` or `unavailable` result does not establish the selected assertion; diagnostic process
success is not mathematical completion.
The entire selected file runs with its original definitions, assertions and later uses.

Builds use Lake's native diagnostic threshold to suppress information and warnings from
successful build jobs. Failed-job diagnostics remain visible. Fresh consumer output streams
without that filter, including each completed statement's outcome and timing.

`timing/runs.jsonl` records the command, selected targets and inputs, source revision and change
hash, actual dependency revisions, toolchain and host, input hashes, phase statuses, build,
execution and acceptance times, and total elapsed time. Each invocation has its own directory
under `.tmp/logs/`. `timing/README.md` holds measured costs and their remedies.

`.tmp/accept-run.json` contains only the current selected observation. Earlier runs remain in
their own logs; their rows are not merged into current success. Missing, partial, duplicate or
foreign reports and failed processes produce a nonzero result. Report completeness and
mathematical success remain distinct. `scripts/accept_files.sh --baseline` accepts a complete
recorded current report as the regression comparison base; its gaps and failures remain gaps
and failures.

The latest attempted `loop` or `slow` observation of the exact workload and tuple governs a
repeat. An unchanged workload whose latest observation exceeded 300 seconds is refused by
`loop`; repair the cost or run that exact selection explicitly. For example,
`just slow "Measure the complete selected consumer" +CasCatalogue.TestSuite:leanArts -- ellipses`
retains the same input. A new source or dependency selection gets its own measurement.

**LOOP001 — the loop of a change is the changed mechanism.** A reader-rule change followed by
both test aggregates and every acceptance file => `just loop "CasCompiler.SourceEqualityFormTests"`,
then the affected unchanged public consumer. Choose complete relevant consumers and keep their
definitions and assertions; current costs come from the timing records.

**LOOP002 — the long run needs a reason and a milestone.** `just milestone` after each commit =>
one milestone after a batch, with the reason recorded; each commit message of the batch names the
short loop that checked it and says that the aggregates were not rerun.

**LOOP003 — a slow test is a defect with a row, not a habit.** An over-limit
`CasRuntime.SessionLiftTests` in every iteration => a row in `timing/README.md` with its
measured cost and remedy; until the remedy, use the milestone or an explicit `just slow` run.
Keep the complete original consumer when measuring its cost.

**LOOP004 — one run at a time, and no run left behind.** A second build started while one runs,
or a stopped caller whose build continues in the container => `just stop`, then one `just loop`.

**LOOP005 — stale build outputs are not a result.** `lake env lean FILE` against changed
imports, or a cached test target standing in for fresh execution => `just loop` on the actual
module, which rebuilds its dependencies and executes its source. A skipped consumer or failed
parent build cannot leave an earlier acceptance report as the current result.

After a focused change, rebuild its affected public consumer and exercise the same mathematical
input and continuation. Protocol peers check framing, dispatch, retained values and lifecycle;
the original mathematical workload still uses its independently supplied computations and
assertions. A cached elaboration is not a fresh external execution.

T114/#84 makes this a current, continuing obligation under C21. A report from an older revision,
a skipped input or a failed selected run cannot supply a successful current result. T028 publishes
the source-derived category interface; T200–T224 must preserve the loop at each actual implementation
boundary, including operation with unrelated optional engines absent. Shared code and engines
remain permitted dependencies under C22 and must be stated when claiming locality.

Keep checked source declarations below runtime state, specialized source rules below reader
assembly, and transport/lifecycle mechanisms below source lowering. Narrow public imports from
their actual exported types and executable dependencies; do not mechanically make every import
private or split a genuinely recursive mechanism merely to reduce file size. Test provisioning
belongs in the explicit setup command, never in `run_cmd` or a production import.

The ordinary build has no profiling prerequisite or automatic second profiling run. Functional
development may use the limits it needs under C21; the original final mathematical budgets are
unchanged. Any claim of a faster feedback loop must compare one actual functional edit at fixed
dependencies and inputs, including the affected rebuild and original public result. That
measurement does not replace the remaining functional work or its independent acceptance.

The runtime session imports the source-session API from `CasCompiler.ReadSession`.
Standalone `cas_source%` notation is exported by `CasCompiler.Read` and the `CasCompiler`
and `CasRuntime` aggregate modules; importing the narrow `CasRuntime.Session` module does
not export that notation elaborator or its executable import dependencies.
