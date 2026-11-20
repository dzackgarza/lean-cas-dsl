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
implementation. An upstream formal gap is reported to its owner under the existing independent
input rules; a downstream repair cannot invent the missing theorem or definition.

## Task rows and open questions

**SPEC001 — a task row holds a requirement, not a decision.** A task row that says "decide X
against the contract", written where two implementations differ => read the specification, the
data model and the contracts; write the passage that settles X and its acceptance condition in the
row. A question that none of them settles is a gap of the specification: it goes to
`/speckit-clarify` and into `spec.md`, and the task names that clarification as its input.

**SPEC002 — "no test states it" is not a status.** "The required behaviour has no test, so the
item is open" => derive the acceptance condition from the governing passage, write the failing
test, then repair.

## Feedback loops

Use the repository's selected toolchain and dependency tuple. Dependency refresh and SDK setup
are explicit actions; an ordinary source build does not change them.

The loop of each change is short. The long run is for a milestone. The recipes make the short
loop one command and put a stated reason, a clean tree and a record in front of the long run
(constitution C24). `scripts/feedback.sh` implements them; they run from the host or from inside
the research container.

| Command | Use | Cost |
| --- | --- | --- |
| `just loop "TARGETS" [FILE …]` | After each change: build the test module of the changed mechanism (several targets in one quoted argument), then the acceptance files that the change touches (stems of `tests/acceptance/*.cas`). | Limit 300 s. The run is recorded. A target whose last recorded run was over the limit is refused. |
| `just slow "REASON" TARGET …` | A target over the limit, when its result is needed now. | The reason (20 characters or more) is recorded. |
| `just milestone "REASON"` | Before a push of the kernel branch, before a handoff, and after a batch of changes: both test aggregates, the notebook targets and every acceptance file. | About 75 min on 2026-11-20. Needs a reason, a clean tree and a head that the last milestone did not check. |
| `just stop` | Stop every `lake` and `lean` process of this checkout. A build started through `docker exec` continues after its caller stops. | — |
| `scripts/accept_files.sh FILE …` | The acceptance part alone. With no file it refuses; `--baseline` makes the last run the comparison base. Do not build while it runs: named files read the live build outputs. | One file costs 130 to 200 s (`timing/README.md`). Seconds go to `timing/acceptance.jsonl`; each statement's milliseconds are in its report. |
| `just probe FILE` | Elaborate a temporary Lean file after Lake rebuilds its imports. | — |
| `just build-production` | Build the connected `CasRuntime.Session` production closure without test modules. | — |
| `just setup-sdk` | Provision the pinned contract SDK environment once before protocol tests. | — |
| `just profile TARGET` | A separate diagnostic profile, when that measurement is needed. | — |

`timing/runs.jsonl` holds one record for each run (time, revision, targets, seconds, status,
reason). `timing/README.md` holds the table of measured costs and their remedies. The full output
of each run is in `.tmp/logs/`.

**LOOP001 — the loop of a change is the changed mechanism.** A change to one reader rule followed
by both test aggregates and all 17 acceptance files (75 min) => `just loop
"CasCompiler.SourceEqualityFormTests"`, and `just loop "CasRuntime.SessionComputationTests"
numbers` when a statement outcome changes (25 s to 4 min).

**LOOP002 — the long run needs a reason and a milestone.** `just milestone` after each commit =>
one milestone after a batch, with the reason recorded; each commit message of the batch names the
short loop that checked it and says that the aggregates were not rerun.

**LOOP003 — a slow test is a defect with a row, not a habit.** Waiting 8 min for
`CasRuntime.SessionLiftTests` in each loop => a row in `timing/README.md` with its measured cost
and its remedy; until the remedy, the target runs in the milestone or through `just slow`.

**LOOP004 — one run at a time, and no run left behind.** A second build started while one runs,
or a stopped caller whose build continues in the container => `just stop`, then one `just loop`.

**LOOP005 — stale build outputs are not a result.** `lake env lean FILE` on a file whose imports
changed (Lean exits with status 139 and no message) => `just loop` on the target, which rebuilds
the imports first.

After a focused change, rebuild its affected public consumer and exercise the same mathematical
input and continuation. Protocol peers check framing, dispatch, retained values and lifecycle;
the original mathematical workload still uses its independently supplied computations and
assertions. A cached elaboration is not a fresh external execution.

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
