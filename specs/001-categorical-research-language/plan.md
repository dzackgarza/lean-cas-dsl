# Implementation Plan: Categorical research language

**Feature:** `001-categorical-research-language` · **Updated:** 2026-11-25 (Asia/Taipei).

**Authority:** [current permanent constitution][C], especially C6 and C21; [owner's current functional handoff][H]; [specification and scenarios][S1]; [requirements and acceptance][S2]. **Operative tasks:** [Part 1 — functional implementation][T1] and [Part 2 — leaf delivery, proofs, independent assessment and performance, after functionality][T2]. These complete bodies replace the former subsystem-first phase order and its predecessor tables. They are not amendments to be applied to an older task list.

**Historical scope of the November 9 replanning:** correct the implementation plan, task order and completion tests. It changes no application code, mathematical definition, protected question/expected answer, constitutional rule, dependency lock, or task/reviewer completion marker. The plan continues the existing integration rather than starting a replacement project. The [planning-failure analysis][F] is diagnosis; this body and the task bodies are the actual replacement work order under the owner's handoff.

## Summary and completion target

Make the kernel fully ready to accept leaf work, then deliver all independently required V1 computations and observations. Every required generic capability must work through the public interface: no lowerer, executor, source-selection gate, result continuation, advertised protocol operation or public entrance may remain a stub. The full mathematical product, higher/infinite scope and later full-B0/parity assignments remain those of the constitution and specification; a successful toy example or first construction is not kernel readiness.

The required production composition is:

`public source → complete selected judgment → compiled OperationalProgram → concrete prepared-request executor → actual framed provider invocation → admitted retained result → subsequent source use`.

The lowerer and concrete executor are separate implementation responsibilities using the existing dependent request/response interface. They follow the [task order](tasks.md#execution-order). Connecting them is part of their functional story, not a final integration phase after protocol research, preservation proofs, exports or independent trials. The public command must use this composition, not continue using the old reconstruction interpreter while helper programs exercise the new components.

The source/runtime boundary remains categorical and independently specified. A leaf implements the released computational obligations; it does not define the categories, laws, choice family, denotation or correctness criterion. A declared preferred route under C6 is registration data selecting an admitted binding, not a proof that routes agree. Actual accepted comparison cells retain their components and coherence. Missing required data produce the prescribed error before dependent dispatch.

## Technical context and retained decisions

| Responsibility | Decision and limit |
|---|---|
| Language/runtime | Lean 4.33.0 on the kernel branch (T105 ports it to the toolchain of the research image, #90), ordinary checked Lean term formation, source-derived dependent programs, actual runtime value/owner/transaction state. Python supplies the released SDK and notebook client, not a second mathematical interpreter. |
| Logs and timing records | FR-043 (constitution C24), current work of Phase 0. `scripts/feedback.sh` writes one record for each run (`timing/runs.jsonl`, `timing/acceptance.jsonl`). T112 adds a record for each test module and each computation and keeps the run logs in the repository. T127 makes the kernel session write an application log of each statement; later tasks extend it with their mechanisms. Diagnostics shown to the user stay opt-in (#8). Forming an object dispatches nothing that no statement has demanded. |
| Mathematical authority | Independently accepted lean-categories declarations, actual structural/constructor actions, complete operation families and abstract computation interfaces. Kernel/leaf authors do not commission subject mathematics shaped to their implementation. |
| Operational substrate | Reuse CSLib `PFunctor.FreeM` at `3951377e5a3f5772737f11cd62bc5bb6a72f95d1` and PolyFun stateful handlers at `a5895e454254a400774fa396b64d5b968f0933df`, with compatible Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. These libraries provide sequencing, not a CAS lowerer or concrete executor. |
| Dependency policy | Actual compatible own-organization latest-main inputs at delivery; record exact diagnostic tuples without making every upstream change a new implementation phase. Do not change locks merely to revise this plan. |
| Existing work | Reuse adequate context/source intake, value/owner/transaction/scope machinery and structural route closure. The handoff explicitly says not to rebuild T005, T006, T008–T011, T018 or the existing T053/T054 closure merely to obtain fresh internal evidence. Inspect actual current source before relying on a historical completion statement. |
| Storage | Immutable committed Environment-backed program/value/observation data; active-transaction staging; nonrollbackable live owner/reservation/transport-ID metadata. No second completed-payload store. |
| External boundary | Data-only versioned framing, exact dependent roles and scoped references, existing engines, retained callable ownership, no automatic retry/replay or provider-priority fallback. All advertised deferred/suspended behavior needs a real kernel handler. |
| Platform | Existing authorized execution environment and actual CAS/notebook surface. No owner-machine access, new persistent environment or alternate frontend is a planning prerequisite. |
| Legacy bridge | T024/T025 are retired by the current owner order. Do not revive v1 bridge work as a prerequisite. Existing retained implementations move to v2 through their separate public-only owners after kernel readiness, in the computational-milestone tasks T200 to T224. Their original mathematics and acceptance questions remain unchanged. |
| Budget phase | C21 governs: functional work may use the time/memory/heartbeat limits needed. Original budgets remain final obligations, including the 99-root 3×3 specimen under 60 seconds and RX-LIFT's shared 200,000 heartbeats/full 22-binding prefix. Fast development feedback remains an immediate continuing priority; other optimization cannot select functional work except the narrow C21 cannot-finish-at-all exception. |

The scoped contracts remain [mathematical input][M], [computational runtime][R], [data model][D] and [notebook session][N]. Their behavioral requirements remain binding. The schedule in this plan and tasks implements the current C21 order; it does not reintroduce their historical first-use-proof, early-freeze, v1-bridge or budget gates. Exact changes of responsibility and proof ownership are specified below, not left to an implementer to reconcile contradictory task dependencies.

## Constitution check and repaired planning defects

The former plan failed to make its first story independently functional: it put the protocol story before the lowerer and public entrance that its own test required. It also placed integrated drivers behind proofs and broad support tasks, and treated requirement tags and an acyclic graph as evidence of adequate functional sequencing. Those are rejected planning assumptions, not waivers for implementation.

The corrected design has these consequences:

- C0–C4: every story reaches actual public behavior through the same source-derived lowerer/executor; no test-provided request or executor supplies the production capability being claimed.
- C5–C8: actual selected routes, cells, allowed choices and defining maps survive compilation, execution and later use. Native well-typedness does not erase additional source-required coherent data.
- C6: enumeration of first bindings is distinct from proving agreement. Complete-family definitional agreement or independently formalized comparison can establish agreement; a declared preferred route selects an admitted reading without asserting agreement. Without the required resolution data, ambiguity is reported before execution. No shortest route, backend success or unregistered theorem search substitutes.
- C9–C13: mathematical authorship, candidate computation and independent acceptance remain distinct; original observations, extension trials and exact lifetime/publication rules remain due.
- C16–C20: preserve existing useful implementation, remove transferred reconstruction paths and inspect the actual public responsibility path. Documentation edits do not claim implementation or independent approval.
- C21: current fast development feedback comes first and remains active. Complete kernel functionality comes before substantial leaf work, self-consistency-only evidence, frozen trials, preservation/correctness proofs and final mathematical/runtime performance work. Actual type/domain/data/owner checks needed to perform a function remain part of that function; postponing proof documentation does not permit an unsound runtime shortcut. A task that needs a declaration missing from lean-categories has a lean-categories task before it, and the workstream does that task there as formalization work ([execution order](tasks.md#execution-order)).
- C22: kernel work and leaf work are accepted separately. A kernel check observes kernel behaviour with a protocol peer or an empty manifest; a computed mathematical result is leaf work ([M1 checkpoints](#m1-checkpoints)).
- C23: category implementations are built in the order of the structural scaffolding of the categories, in milestones of their own after kernel readiness ([computational milestones](#computational-milestones)).

The governing constitution is [v4.0.0](../../.specify/memory/constitution.md) of 2026-11-25. Its adoption record names each amendment and its source; version 4.0.0 records the [owner instructions of that date](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-7155201731).
C0, C9, C21, C23 and C24 state source-derived complete category interfaces, separate
dependency relations, real locality, continuing feedback and full choice-sensitive assessment.
No amendment changes an original mathematical question or a final budget. Earlier
constitution hashes remain historical input provenance.
C24's timing records, test-run logs and application logs are current work (FR-043): C21 puts
only final performance and self-consistency evidence after functionality.

## November 17 source-to-result correction

The [current handoff](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6726232237) and functional tasks supersede older reader-first sequencing. Repair the complete selected source construction and its actual continuation: retain exact occurrences/endpoints and universal data, prepare generic dependencies, use the common source boundary for provider requests, construct genuine public target objects/arrows, apply formal classifier refinements and complete generic operation growth. Delete each transferred recovery path in the same implementation change. Retain already adequate source/runtime/rule separation; do not reimplement it for another receipt.

The explicit focused-command, production/test target and SDK-provisioning corrections support those functional changes. Tests stay outside the production target; provisioning stays outside Lean elaboration; a focused build streams once without a profiling gate. Functional source/provider consumers remain the endpoint of that loop. #84's current changed-source feedback is an immediate priority under C21 and remains part of functional work. Final mathematical/runtime optimization remains after functionality.

## Concrete production architecture

### 1. Read and preserve the selected mathematical request

`Context`, `Read`/`Elaborate` and `Resolve` consume the accepted declarations and complete local/universe context. Definitions, local hypotheses, mathematical assertions and execution requests remain distinct. Abstract declarations use the scoped assumption behavior required by [#86](https://github.com/dzackgarza/lean-cas-dsl/issues/86), never new global axioms. Preserve source positions and exact selected dictionaries, parameters and generalized-point domains.

Structural closure derives all first-binding routes from accepted declarations at their actual supported rule signature. Reuse the existing exact closure; do not rebuild it to answer the different question of universal semantic equivalence. Selection at the actual program boundary consumes accepted whole-family agreement or the C6 declared preferred route. A preferred route must refer to an admitted surviving binding and be retained with the reading; it is not runtime tie-breaking by cost, order or provider success.

An explicit cell keeps its actual boundary, components, direction, required coherence and occurrence. An independently specified allowed-choice computation keeps its admissible family, supplier, stage and dependent continuation fixed before dispatch, then retains the actual returned candidate. Different allowed outputs need not be equal. An ordinary ambiguous request is not converted into a new choose-a-route operation. Missing formal selection, malformed supplied evidence, interrupted checking, absent realization and missing computational choice data retain their prescribed distinct outcomes.

### 2. Compile source statements, not manually assembled test programs

T032 owns the actual source-to-`OperationalProgram` transformation in `CasCompiler/Lower.lean`. It consumes the retained context, checked declaration/computation families, source roles and complete result layouts. It compiles variables, constants, lambdas, applications, lets, records, projections and the required source computations. Under C22 the lowerer evaluates no eliminator, recursor or definition body; T033 makes each such form, and each value with no published operation, end in the no-implementation outcome. Further generic mathematical forms extend that same compiler, not a second interpreter.

Prerequisite computations remain parametric callables at their actual arguments. Capture actual runtime bindings and preserve all formal context needed for the declared operation. A noncomputable mathematical definition is not an instruction to synthesize a backend algorithm by unfolding choice. The independently specified computational interface supplies that boundary.

The compiler must produce its requests itself. Manually making an `OperationalProgram` in a test exercises the runtime, not T032. The lowerer does not wait for completed provider handlers or independent assessment; it emits the existing prepared operational signature. The executor implements that signature independently, then T038 joins them through the public entry.

### 3. Execute prepared requests with a kernel-owned concrete executor

T013 owns the production interpreter/dispatcher that supplies the previously missing executor. It must bind a prepared primitive request to the selected live connection (`FramedConnection.invokeControlBefore`), admit the response at its fixed dependent role, retain it in the active transaction and continue the operational program. A generic handler taking an application-supplied executor is not completion of this task.

T019 provides projection and application of actual stored fields, compiled closures and native callable values. T020 provides actual owner-bound export invocation, including complete published/dependent context and fresh invocation-local capture frames. T021 validates complete replies/exports/captures and request-local disposal. T026 supplies actual exact-demand construction and realization selection, not merely profile parsing or a fixed-point calculation over a graph manufactured by a test. These functions are composed by T013; none is approved by supplying its missing production operation in a test callback.

Selection of a realization occurs after the mathematical question is fixed. Zero eligible realizations is the specified computational gap, one selects the actual call and multiple remain computational ambiguity. Retain exact primitive/generic/fused identities. Fixed finite demands use the declared grounded analysis; result-dependent demands remain closures until their actual arguments exist. No test-only closure, absent-as-unknown conversion or retry-until-success path supplies the result.

T022/T023 complete deferred requests and adaptive suspension in the same executor, using actual children, scoped captures, released permits, one-resume tokens and exact backward result associations. They depend on the working invocation path; they are not prerequisites to authoring the lowerer or connecting the immediate public path. The story and final kernel are not complete while an advertised generic protocol feature is missing. When a suspended leaf asks for an operation that no leaf implements, the kernel returns the no-implementation outcome to that leaf, and the leaf continues under its own control logic (constitution C22; [runtime contract][R], section 6).

### 4. Retain the result for the next mathematical use

T042 binds dependent fields to actual earlier returned values. T043/T044 implement the selected lift and subsequent factor; T046/T048/T049 complete successive lift, universal data and constructed-map use. Actual object/image/inclusion/comparisons/captures remain associated. The kernel cannot rebuild another apex, insert identity for a nonidentity component or infer a producer from equal expressions/bytes.

Whole-reply admission is atomic. Valid staging supports later expressions in the same active cell; whole-cell commit publishes the full delta. Abort/cancellation publishes none of that cell's new references. Existing committed values remain usable under their genuine owner dependencies. Stored independent portable fields are not invalidated by an unrelated sibling's owner. A whole-record demand or captured callable still needs all its real dependencies.

### 5. Make the real public entrances use this composition

T038 connects `#cas`, the public statement runner and service/derived preparation to the new lowerer and production executor. It has functional prerequisites only: complete source/prepared roles, selection/error gate, concrete executor and result binding. It does not wait for differential/series expansion, full suspension support, compiler preservation proofs, a complete audit export or frozen trials merely to establish this connection.

Transferred uses lose the old `Language`/`Realize` recognition, endpoint retry, producer reconstruction and alternate completion writes through T051/T064. No new caller enters the superseded path. The existing acceptance driver is adapted at T041 without a proof prerequisite; it calls the public production interface rather than creating requests or injecting an executor. Its original mathematical inputs and expected outcomes remain intact. Required source dependencies block their affected uses only; the inherited numeral issue does not prevent implementing the generic lowerer, executor or other already specified source forms.

## Functional stories and their complete paths

The stories retain the specification's user outcomes. Shared code is implemented at its first actual use, then reused. Story dependencies below describe functional interfaces, not a requirement to finish unrelated areas before authoring the next function. No phase is declared complete on the strength of a helper-only test. All required stories must work before kernel readiness; a story boundary is not a reduced deliverable or permission to stop.

| Story | Complete implementation responsibility | Functional observation through the public path |
|---|---|---|
| US1 — connected calculation | Source/contexts, exact arithmetic/sets/functions/polynomials/differentials/primitive interfaces, real lowerer, concrete executor and public command | Original source is compiled and dispatched; its actual result is bound and used by the next source expression. Requests and executor are not supplied by the test. |
| US2 — complete construction and later use | Actual dependent record/lift/limit/mediator/factor results and successive uses | The actual returned construction's nonidentity comparison and defining/factor maps are subsequently applied at their declared endpoints. An apex-only answer fails. |
| US3 — selected structures and higher/dependent comparisons | Required cell/choice gate, classifiers, reindexing, domains, constructor/higher actions | The selected components act; required omission is rejected before dependent dispatch; legitimate declared choices remain actual data. No global quotient or unregistered proof search replaces the judgment. |
| US4 — exact/infinite/qualified work | Lazy/indexed/symbolic full interfaces, exact series, admitted operations, enumeration and explicit approximation/truncation | A later demand outside an earlier finite display uses the same complete object; exact requests, tolerance and mathematical admission retain their meaning. |
| US5 — growth | Generic source projection, immediate structural composition, operation propagation and both extension directions | New accepted declarations are consumed by the same compiler/executor and old consumer, without per-object forwarding or a second hierarchy. Formal fresh independent trials occur later, not as a gate on implementing this behavior. |
| US6 — computational extension | Complete invocation/projection/application/deferred/suspension service and accurate public contract, reusing the earlier production path | A public-contract producer's actual result reaches an unchanged consumer through supported services. All advertised generic behavior is implemented; successful negotiation alone fails this condition. |
| US7 — real notebook | Actual new execution path in worker/client, committed state, cancellation/owner/snapshot rules and inert queries | Connected cells use retained results; explicit execution performs work, inspection performs none; no replay resurrects old choices/owners. |
| US8 — mathematical discovery/display | Source-derived discovery, retained metadata, once-only mathematical rendering and actual provenance | Users inspect actual selected data and full applicability independently of provider availability, without executing lazy components or executable formatters. |

US2–US6 use the shared production path developed with US1; this dependency is explicit, not a claim that a protocol-only phase is independently executable. Their generic capabilities use that interface in the fixed task order; the interface does not authorize separate active tasks. US7/US8 are real integration, not mock frontends or post-delivery polish. US9 is Phase 0 of the task list (T114, T112, T127). US10 is delivered by the [computational milestones](#computational-milestones).

## Completion milestones

These are complete delivery outcomes, not file/module counts or a second task queue.
[Tasks](tasks.md#execution-order) retain stable IDs, definitions and execution order.
[GitHub #10](https://github.com/dzackgarza/lean-cas-dsl/issues/10) owns the roadmap and evidence;
native milestones record each issue's full closure stage. A broad owner issue can contribute
functional work earlier while retaining its later proof and acceptance obligations.

| Milestone | Complete observable outcome | Owners and scope |
| --- | --- | --- |
| [M0 — Fast edit-to-result feedback](https://github.com/dzackgarza/lean-cas-dsl/milestone/1) | A substantive edit in the current owner rebuilds affected executable dependencies and runs the unchanged public consumer within the normal focused-loop bound. Current diagnostics, failures and timings are truthful. Retain this behavior throughout development. | #84, T114/US9; reuse T016's completed work without treating its historical timing as current readiness. T112 and T127 (FR-043: timing records, test-run logs, application logs) continue this capability as the first unchecked tasks. |
| [M1 — Complete generic categorical kernel](https://github.com/dzackgarza/lean-cas-dsl/milestone/2) | F: all Part 1 functionality works through real public entrances, including complete constructions and later use, both functor actions, selected lifting/refinement/comparisons, higher/infinite interfaces, protocol, notebook/lifetime, discovery/display and both directions of growth. Its checks observe kernel behaviour and require no computed mathematical result (constitution C22). It has [checkpoints](#m1-checkpoints). | #92; #66/#69 and #82/#85/#91 supply their functional responsibilities; #86 closes here. The first complete construction is an internal step, not this milestone. |
| [M2 — V1 category implementations and delivery](https://github.com/dzackgarza/lean-cas-dsl/milestone/3) | The [computational milestones](#computational-milestones) deliver the category implementations in mathematical order. All required V1 category implementations supply actual computations, defining data and later uses through the released contract; publish and build one compatible mathematics/kernel/contract/leaf/notebook tuple. | #93, T200–T212 and T105; #90 supplies the research-image toolchain/Mathlib port. |
| [M3 — Independently accepted V1](https://github.com/dzackgarza/lean-cas-dsl/milestone/4) | All #24 A–F obligations, independent mathematical assessment, preservation arguments, frozen extension trials and original final budgets hold together on the delivered tuple. | #24 and full closure of #66/#69/#82/#85/#91; #97 records #10's unchanged V1 closure condition; the project root remains open through M4/M5. |
| [M4 — Full B0 and classified Sage coverage](https://github.com/dzackgarza/lean-cas-dsl/milestone/5) | Complete #19's K1–K14 computations and the separate versioned Sage coverage denominator, including required hypotheses, defining maps and continuations. | #19, #20, #21, #22, #23; the computational milestones T213–T224. Their bounded construction/input work can inform V1 before their later full closure. |
| [M5 — Research and client completion](https://github.com/dzackgarza/lean-cas-dsl/milestone/6) | Complete the retained research facade, installation portability, unit-group delivery, opt-in logging and actual research-use demand work against their existing outcomes. | #68, #34, #3, #8, #13. These remain outside the V1 denominator. |

M1 consumes the functioning development loop. M2 consumes F and the usable released contract.
M3 consumes the delivered candidate. Within a milestone, use actual task inputs; a missing input
blocks only its dependent work. Native issue dependencies encode those real completion inputs,
not a requirement to stop every other task.

The image port stays T105/M2. Bring it forward only when the actual available environment cannot
build an active functional task. A fresh image or broad dependency refresh is not an invented M0
prerequisite when the current compatible environment already supports the work.

For full B0, F and the usable released contract establish implementation readiness. V1-required
implementation and delivery have priority. Otherwise runnable broader work need not wait for an
evidence-only V1 tail, provided it does not displace V1 completion. Final V1 acceptance is neither
full-B0 completion nor a new mathematical input to broader algorithms.

### M1 checkpoints

M1 closes on F. Before F, these checkpoints close one at a time. A checkpoint is one observation of kernel behaviour through the public session `CasRuntime.KernelSession`, on the original source inputs that its row names, with a protocol peer or an empty manifest (constitution C22; SC-014). It closes when the observation holds on the kernel branch. It claims only itself. It satisfies no user story: the acceptance of a story needs computed results and is assessed when the category implementations exist. It checks no task box, and the independent assessment of the same inputs stays in Part 2. Issue #92 holds the checklist.

The observation of a checkpoint is first made in the closing of the task that its last column names. It is part of that task, so it serves the active task. A checkpoint that does not hold then is observed again at the close of each later task until it holds. A condition on the source text, such as the removal of a mechanism, belongs to the definition of a task (T116, T117, T051, T064) and not to a checkpoint.

No checkpoint was evaluated on 2026-11-25. A checkpoint whose observation already holds at the close of its task is checked then. The observation, not a task box, decides.

`RX` inputs are the files of `tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/`. "Tests to add" is the section "Public-path tests to add" of the task list.

| Checkpoint | Observation | Inputs | First observed at the close of |
| --- | --- | --- | --- |
| M1.1 — Typed carriers | A different source input of equal value is rejected. Two bindings with equal defining expressions stay distinct through a projection, a substitution and a later call. An absent selection is an error at the reader. Two selected limits with one apex keep their own cones. | The controls of T116 (a), (b) and T117 (a) to (c) | T117 |
| M1.2 — Connected statement path | A source file runs through one session. Each statement is read, lowered and dispatched to a protocol peer at its registered address with its actual operands. The reply is admitted and retained, and a later statement uses that value with no second dispatch. | `tests/acceptance/sets.cas`: its definitions `A`, `f` and `g` and the later statements that use them | T038 |
| M1.3 — Forms of connected calculation | Every statement of the permanent acceptance files reads to its registered meaning. With an empty manifest, each computational statement ends in no implementation at a registered address. No statement ends in an internal error or a reader gap. | Every file of `tests/acceptance/*.cas` | T075, the last task that adds a reader or lowerer form |
| M1.4 — Construction and later use | The original RX-LIFT source with its 22 bindings prepares each lift field, comparison and factor request at the selected lift, with the earlier outputs as operands. The returned object, maps and factor are the operands of the later requests. Two selected limits with one apex keep their own cones. | `rx-lift-prescribed-stages.cas`, `rx-lift-source-comparison.cas`, RX08; the limit statements of `sets.cas` | T049 |
| M1.5 — Selected structures | The inputs select their routes, cells, classifiers and reindexing before dispatch. A required omission is refused with no dispatch. A declared choice-producing operation binds the member that the peer returns (T115). | RX05, RX06, RX07; an operation that lean-categories#182 registers | T115 |
| M1.6 — Exact, infinite and qualified requests | The inputs prepare requests that keep the exact source, the tolerance and the full index family. A demand outside an earlier finite display reaches the same retained object. | RX09; the ellipsis, series and approximation statements of the permanent files | T069 |
| M1.7 — Growth | A new accepted declaration reaches an unchanged consumer, and a new generic operation reaches an existing object, with no kernel edit. | RX01 to RX04; rows T073 and T075 of "Tests to add" | T075 |
| M1.8 — Computational contract | A peer written from the published contract alone uses deferred and suspended service, and an unchanged consumer receives its output. A peer that asks for an operation with no implementation receives the no-implementation outcome and continues. The published interface matches the built kernel. | RX10; rows T022, T023 of "Tests to add" | T101 |
| M1.9 — Notebook | The cells run through the worker and one session: values retained across cells, inert queries, cancellation and owner rules. | `notebooks/kernel-v1.ipynb` | T093 |
| M1.10 — Discovery and display; old path removed | Discovery and inspection read retained data and execute nothing. `#resolve`, `#methods` and `cell%` answer from the new resolver. | The workflow questions of `notebooks/kernel-v1.ipynb`; the commands of `CasDslTests/Cells.lean` | T064 |

### Issue tree and task order

The native root is [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10), which stays open
through every retained phase. V1 completion is recorded by M3/#97 under the unchanged
#66/#69/#24 condition; it does not close the project root while M4/M5 remain.

| Direct-root milestone ledger | Ordered complete work owners |
| --- | --- |
| [#94 — M0](https://github.com/dzackgarza/lean-cas-dsl/issues/94) | #84 / T114 |
| [#95 — M1](https://github.com/dzackgarza/lean-cas-dsl/issues/95) | #92 / F, with the M1 checkpoint checklist in #92; #86 at T030 within F |
| [#96 — M2](https://github.com/dzackgarza/lean-cas-dsl/issues/96) | #93 / T200–T212 (computational milestones), then T105; #90 within T105 |
| [#97 — M3](https://github.com/dzackgarza/lean-cas-dsl/issues/97) | #24; full remaining obligations of #66, #69, #82, #85, #91 |
| [#19 — M4](https://github.com/dzackgarza/lean-cas-dsl/issues/19) | #22 / full B0 and classified Sage delivery; #20, #21, #23 supply full-parity inputs |
| [#98 — M5](https://github.com/dzackgarza/lean-cas-dsl/issues/98) | #68, #34, #3, #8, #13 |

`itree next` selects the completion owner; the unchecked task order selects the current work
within its scope. #84/T114 came first and is closed on its complete current loop evidence;
later tasks inherit the continuing C21/C24 obligation. T112 and T127 (FR-043) are the first
unchecked tasks. They continue that capability under #92 and do not reopen #84. The former
full-#85 blocker of #84 is obsolete.
M1 consumes that capability, M2 consumes F, and M3 consumes the delivered candidate. Native
group blockers prevent a later proof/assessment owner or subsidiary delivery issue from being
selected ahead of those required inputs.

Execute #86's whole scoped-declaration requirement at T030 and close it on its original
acceptance within #92. Execute #90's whole image requirement at T105 and close it on its
original acceptance within #93. Their sibling positions do not postpone those implementations
until after F or delivery. The broad M3 owners contribute their functional requirements at
the existing positions under #92; their later full closure never gates that functionality.

Within M3, #24 coordinates the remaining Part 2 work in document order with its separately
assigned proof, engineering and independent-assessment owners. Close each broad owner only
when its own complete requirements hold; its later sibling position does not postpone its
contribution until after acceptance. T110 records V1 closure at #97 and preserves #10 for
the remaining project phases.

These native completion dependencies do not prohibit the work needed to restore an actually
missing environment for the active task. Perform the necessary #90 port work as support for
that active task under the existing exception, without adding a full-F-before-repair cycle.
If native traversal must select #90 for that observed repair, temporarily remove M2/#96's
#92 blocker while retaining #93's own #92 blocker; restore ordinary M2 readiness once the
active environment is usable. This does not complete #90's full image acceptance.
A missing independent input still blocks only its actual consumers. Full B0's executed
coverage consumes F and #20/#21/#23, without a #24 evidence-completion prerequisite; early
source/input work remains available. #22 owns both complete M4 execution outcomes already
specified in #19. Its whole issue is not blocked by unrelated full-Sage inventory work:
the full-parity input order remains #20 → (#21 and #23) → the corresponding executions,
while existing B0 questions use their actual available inputs. Close every owner only on
its entire requirement and #22 only on both full outcomes. Verify resumed selector results
against this task source.

### Architecture realized at these milestones

The [mathematical execution model](../architecture.md#category-interfaces-computational-dependencies-and-build-boundaries)
separates mathematical meaning, public computational realization and physical build dependencies.
M1 realizes public constructor and operation conformance, with complete selected objects/maps,
generic composition and a category-indexed computational interface generated from accepted declarations
through the existing exporter. The independent registry remains semantic authority. M2 supplies the required category implementations against that boundary.
M3 establishes the original independent correctness, general preservation and frozen-extension
obligations. A port registration, category name or packet shape establishes none of these outcomes
by itself. Private library reuse remains permitted; public interoperability cannot require
private cross-leaf representations.

## Computational milestones

Computational work is leaf work (constitution C22, C23; FR-042). It has version milestones of its own, separate from the completion milestones above. They start after kernel readiness: the contract that an implementation is written against is published by T028, completed by T100 and T101, and released at F. Each milestone is one task of the task list (T200 to T224), with its categories, its statements, its engine, its upstream tasks and its moved registrations stated here. Issue #93 holds the checklist of T200 to T212; M2 closes when they hold on one published tuple (T105). T213 to T224 belong to M4 (#19, #22). The computation behind the table is the research record [`research/milestones.md`](research/milestones.md) (data in `research/milestones.json`), which lists every statement and registration of each milestone.

**Prerequisites.** The implementation of a category follows the implementations of the categories that its structural functors and classifier forgets reach (`research/scaffolding.json`, lean-categories `443fba9`). 49 of the 100 registered categories have such a chain to `cat.sets`. The other 51 follow one rule: **a category with no structural chain to `cat.sets` is implemented after the categories that its formal definition is built from** — the argument categories of $\mathrm{Arr}$, $\mathrm{Core}$, a slice, a coslice, a functor category or a category of elements; the base and the classifier host of a refinement; the parameter categories of a family fibre; the host of a classifier total. An atom with none of these inputs (`cat.cardinals`, `cat.cardinalities`, `cat.ordinals`, `cat.walking_pair`) is a root: no implementation precedes it, and it enters with the first milestone that needs it. A category whose structural functor lean-categories does not register yet enters after the upstream task that adds that functor, at the place that the functor gives it. Reason: an object of a built category is made of objects and maps of its inputs (an object of $\mathrm{Arr}(D)$ is a map of $D$; an object of $\mathrm{refine}(B, c)$ is an object of $B$ with evidence for $c$), so its public constructors consume their public constructors, exactly as a structural functor makes its source consume its target (C23, "functor actions construct their targets"; MATH002). The order applies the changes of the upstream tasks that precede the milestones: T131 adds the additive tower (`cat.additive_magmas`, `cat.additive_semigroups` below `cat.additive_monoids`), T133 replaces `cat.partially_ordered_sets` and `cat.totally_ordered_sets` by one tower of orders and puts `cat.boolean_algebras` above bounded lattices, and the scaffolding-gap tasks of lean-categories add the structural functors of the lattice, form, ideal, scheme, cusp and crystal categories.

**Membership.** A milestone holds the prerequisite closure of its categories, less the categories of earlier milestones. A milestone comes after each milestone that holds a prerequisite of one of its categories, and after each milestone that holds a category on the route of every statement that uses its categories (the Boolean-algebra statements read the numerals of a ring, so Boolean algebras follow rings). Milestones that need no other milestone are ordered by the depth of their categories, the smaller first, then by name; their order sets no dependency. The V1 milestones come first (V1 priority, see [completion milestones](#completion-milestones)), then the milestones with full-B0 statements, then the milestones whose statements the classified Sage coverage supplies.

**Statements.** The stated result of a milestone is the set of original workload statements whose selected route stays within the categories of that milestone and the milestones before it (FR-042). The routes are those of `research/workload-routes.json` (the 287 statements of the permanent and extension files) and of the 18 statements of the K3 and K14 files (`tests/acceptance/b0-required-positives.cas.proposed`, `b0-formed-positives.cas.proposed`). A typing judgement (question kind `settled`, 19 statements) holds by elaboration and is no milestone's result. **V1 statements** are the 134 extension statements and the 15 K1 identifiers that #24 keeps as required computational assertions (149 statements). The other 137 are **full-B0 statements** (#19). A milestone task closes on its V1 statements; the full-B0 statements of the V1 milestones are the result of T213.

**Reading of ℤ and ℚ.** The list uses the readings that the selection rules give (C6, FR-016, FR-022): a written ℤ or ℚ has a reading at each registered object of that name, and readings whose complete operation families are definitionally equal are one reading. The commutative ring ℤ forgets to the ring ℤ by an identity (`NamedCommutativeRings.integersIdentification := Iso.refl _`, lean-categories `Catalogue/Semantics/Algebra/NamedCommutativeRings.lean:33-35`; the same for ℚ at `:48-50` and for the field ℚ at `Fields.lean:75-76`). So a ring operation on ℤ or ℚ has one reading, and a registration at the ring reading serves it. A statement needs `cat.commutative_rings` or `cat.fields` only when its operation is declared there. These are the ring rows of the recorded readings. The kernel report of 2026-11-22, which reads ℤ as the commutative ring and ℚ as the field under `+`, comes from a reader that forms one object candidate of a name (the T007 worktree row "Object candidates of a written name", T030, T059); it does not move a statement to a later milestone.

**Kernel computation.** Each kernel-side evaluation of the table "Kernel computation (C22)" of the task list ends in the no-implementation outcome when its Part 1 task closes. The milestone that holds the owner of the evaluated operation supplies the computation (column "Kernel evaluation" below).

| Task | Milestone | Part | Categories (without `cat.`) | V1 / full-B0 statements | Engine (container version) | Upstream tasks | Registrations moved | Kernel evaluation |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| T200 | Sets | M2 | sets, core_sets, cardinals, cardinalities | 23 / 5 | Sage 11.0.beta5: sets, maps, products, disjoint unions, power sets, `cardinality()`; Catlab.jl 0.17.7 (limits of finite sets) for pullbacks, through juliacall 0.9.36 and Julia 1.12.7, declared in the Julia project of the leaf repository | T119, T120, T121, T123, T129, T134 | 30 (`sage`, `gap`, `gap-groups`, `sage-power-set`, `sage-set-limits`, `sage-fin-rev`, `sage-presentations`, `sage-symbolic`) | equality of elements; application and composition of maps; projections of a product; the graph of a map |
| T201 | Finite sets | M2 | finite_sets | 3 / 1 | Sage: `FiniteEnumeratedSet`, `Sets().Finite()`, `FiniteSetMaps` | T119, T135 | 2 (`sage`) | the list of the elements of a finite carrier |
| T202 | Orders | M2 | preorders, partial_orders, linear_orders | 4 / 0 | Sage posets (`Poset`, `is_lequal`); an order-preserving map is a set map with Sage's comparison | T133 | 0 | $<$ and $\le$ on ℕ |
| T203 | Rings | M2 | magmas, semigroups, monoids, groups, additive_magmas, additive_semigroups, additive_monoids, additive_commutative_monoids, semirings, additive_groups, rings | 15 / 56 | Sage: ℤ, ℚ, ℤ/n, gcd, factorization; GAP 4.16.1 through Sage `libgap` for groups | T122, T131, T132 | 25 (`gap`, `gap-groups`, `sage-symbolic`) | arithmetic of ℕ, ℤ and ℤ/n; gcd and primality; the multiplication, unit and inverse of an instance |
| T204 | Group automorphisms | M2 | core_groups | 13 / 0 | GAP through `libgap`: `AutomorphismGroup`, conjugation | T134 | 0 | — |
| T205 | Commutative rings | M2 | commutative_monoids, commutative_rings | 18 / 47 | Sage: polynomial rings, quotient rings, `det`, `trace`, `charpoly`, `roots`, `factor`; Singular 4.4.1 inside Sage for several variables | — | 18 (`sage-presentations`, `sage-symbolic`) | — |
| T206 | Topological monoids | M2 | hausdorff_topological_commutative_monoids | 5 / 0 | Sage `LazyPowerSeriesRing` over ℤ | T128 | 0 | — |
| T207 | Modules | M2 | modules_total, modules_r | 10 / 0 | Sage free modules over ℤ, ℤ/n and fields | — | 3 (`sage-modules`, `sage-set-limits`) | the scalar action of an instance |
| T208 | Bilinear forms | M2 | bil_wform | 3 / 5 | Sage `IntegralLattice`, `discriminant_group`; PARI 2.17.4 through `cypari2` 2.2.6 | — | 10 (`gap-groups`, `sage-discriminant`, `sage-modules`) | — |
| T209 | Fields | M2 | fields | 13 / 4 | Sage: ℚ, `GF(p)`, vector spaces, `right_kernel`, `dimension` | — | 1 (`sage-symbolic`) | — |
| T210 | Module rank | M2 | core_modules_r | 1 / 3 | Sage `rank` of free modules and lattices | — | 5 (`sage-modules`) | — |
| T211 | Module kernels | M2 | subobjects_sets, subobjects_modules_r, arrows_modules_r, core_subobjects_modules_r | 2 / 0 | Sage `kernel` of module maps, submodules, `dimension` | T134, T138 | 0 | membership in a subset |
| T212 | Formed modules | M2 | bilin_module, arrows_bilin_module | 39 / 2 | Sage free modules with an inner-product matrix over ℚ, `submodule`, restricted Gram matrix | T130, T134 | 4 (`sage-bilinear-lift`) | — |
| T213 | Full B0 in the V1 categories | M4 | (those of T200 to T212) | 0 / 123 | the engines of T200 to T212; SymPy 1.14.0 for limits, series and integrals, with the Sage symbolic ring and Maxima 5.49.0 where SymPy returns an unevaluated form | T124, T125, T128, T136, T137 | 0 | — |
| T214 | Group kernels | M4 | arrows_groups, subobjects_groups | 0 / 4 | GAP through `libgap`: `Kernel`, `AlternatingGroup`, `SignPerm` | T134 | 13 (`gap-groups`) | — |
| T215 | Boolean algebras | M4 | join_semilattices, meet_semilattices, order_lattices, bounded_order_lattices, boolean_algebras | 0 / 9 | Sage `Subsets`, `posets.BooleanLattice` | T133, T136 | 0 | — |
| T216 | Integral lattices | M4 | integral_lattice | 0 / 1 | Sage `IntegralLattice` | — | 4 (`gap-groups`, `sage-modules`) | — |
| T217 | Set constructions | M4 | arrows_sets, coslice_sets, endofunctors_sets, walking_pair, sets.pair_diagrams, slice_sets, pointed_sets, core_pointed_sets, countable_sets, enumerated_sets, core_subobjects_sets, subsets.point_predicates, subsets.subset_predicates, crystals | classified coverage | Sage (sets with a base point, `EnumeratedSets`, crystals); Catlab.jl for slices, coslices and diagram categories | T134; the crystal structural functor (scaffolding gaps) | 0 | — |
| T218 | Well orders | M4 | well_ordered_sets, core_well_ordered_sets, enumerated_monotone_sets, ordinals | classified coverage | SymPy `sympy.sets.ordinals`; Sage posets for finite well orders | T133 | 0 | — |
| T219 | Algebraic structures | M4 | magmaswithtwooperations, division_rings | classified coverage | Sage (quaternion algebras); GAP (finite magmas) | T131 | 0 | — |
| T220 | Algebras | M4 | algebras | classified coverage | Sage algebras over a base ring | — | 0 | — |
| T221 | Schemes | M4 | schemes, schemes_over, schemes_over_ring | classified coverage | Sage `sage.schemes` | T136; the scheme structural functor (scaffolding gaps) | 0 | — |
| T222 | Module constructions | M4 | module_points, based_module_indexed, coord, finite_projective_lattice, finitelygeneratedmodules, finiterankmodules, free_cover_indexed, freemodules, quotients_modules_r, torsion_free_modules, free_cover, based_module, coord_indexed, ideals_r | classified coverage | Sage modules (`fg_pid`, quotients); Oscar 1.8.2 or Macaulay2 1.24.11 for modules over polynomial rings | T118; the ideal structural functor (scaffolding gaps) | 0 | — |
| T223 | Forms over rings | M4 | modules_over_rings_ext, bilin_forms_over_rings, quad_forms_over_rings, integral_forms, lattices_over_rings, finite_projective_lattices_over_rings, finite_free_lattices_over_rings, unimodular_lattices_over_rings, integral_lattices, even_integral_lattices, cusps | classified coverage | Sage `QuadraticForm`; Hecke 0.39.22 through Oscar for forms over number fields | the refinement, form, module and cusp structural functors (scaffolding gaps) | 0 | — |
| T224 | Lattices and quadratic modules | M4 | quad_module, quad_wform, alternating_forms, lattice, subobjects_bilin_module, coord_lattice, fraction_field_perfect_finite_projective_lattice, definite_lattice, indefinite_lattice, even_lattice, finite_free_lattice, unimodular_lattice | classified coverage | Sage `IntegralLattice`, `TorsionQuadraticModule`; Hecke through Oscar for genus and isometry; PARI `qfauto` for definite lattices | the lattice structural functors (scaffolding gaps) | 0 | — |

The M2 and M4 parts settle which milestones V1 requires: a milestone with a V1 statement is M2. "Classified coverage" means that the statements of the milestone are the classified Sage computations (#20, #21, #23) whose route stays within its categories, by the same membership rule.

**Engines.** The research container holds Sage 11.0.beta5 as a source build and no passagemath; the milestones use the container Sage, because the container is the reproducible research environment and one environment cannot hold both `sage` packages (`research/engine-survey.md`, "Constraints for planning", items 1 and 2). GAP's Semigroups package does not load in the container; no statement of the milestones uses a finite semigroup or monoid given by a table, so no milestone needs it. For cardinals, no surveyed engine has infinite cardinal arithmetic, and every cardinal of the workloads is finite or $\aleph_0$. A finite cardinal is Sage's `cardinality()`. The cardinal is $\aleph_0$ when Sage gives `cardinality()` $= +\infty$ and puts the set in `EnumeratedSets`, its category of countable sets: ℤ, ℕ and $\{2n \mid n \in \mathbb{N}\}$ are there, which covers `sets.card.integers` (V1), `sets.card.naturals` and `comprehension.even_card` (probe in `research/milestones.md`). Sage does not put $\mathbb{Z}^2$ (as a module or as `cartesian_product([ZZ, ZZ])`) in `EnumeratedSets`, so no engine gives $\aleph_0$ for `lattices.card.a2` (K13) and the cardinalities $\aleph_0$ of `formed.card.hyperbolic_fixed` and `formed.card.hyperbolic_variable` (K14). These three full-B0 statements of T213 wait on owner question Q1 below. No statement needs an uncountable cardinal. The engine of each row is the recommendation of the survey for its families (`research/engine-survey.md`, "Recommendation summary"); `sage.schemes`, Sage crystals and the cusps of `sage.modular` are not in that survey, and their milestones add them to the survey record before the implementation.

**Owner question Q1 (infinite cardinals).** The established-implementations policy forbids a leaf to hand-roll an algorithm, and #19 requires each K13 and K14 statement to be computed through registered execution. No engine computes $\aleph_0 \cdot \aleph_0 = \aleph_0$. Which computation supplies $|\mathbb{Z}^2| = \aleph_0$: a cardinal implementation that computes the arithmetic of finite cardinals and $\aleph_0$, with Mathlib's `Cardinal` theorems as its cited reference, or a proof procedure registered in lean-categories that settles these closed propositions, with the computation-only report of #19 recording no leaf for them?

**Rings.** `cat.rings` reaches `cat.monoids` by three structural routes at `443fba9`: directly, through semirings, and through its additive group read as a group. The registered cell `cell.rings.multiplicative_monoid.semiring` compares the first two. Along the third, `·` denotes the addition of the ring; T131 (lean-categories#193) makes `fun.additive_groups.to_groups` non-structural and puts one multiplication at magmas and one addition at additive magmas, with the richer rows as their restrictions. T132 (#194) gives the numerals of a ring as the numerals of its underlying semiring, and T122 (#186) the numeral of additive monoids. Groups are in the ring milestone: at `443fba9` a ring reaches groups, and the 13 RX-03 statements of T203 need groups with the ring chain. SC-015 (`2 * 3 = 6 in ℤ`) is the stated attainment of T203.

**Each milestone task** (constitution C17, C22, C23 and the established-implementations policy):

1. The leaf code is in `lean-cas-dsl-leaves` (`backends/` and `leaves.json`), written by a public-only author (role L) against the released contract and the generated category interfaces of T028.
2. The C17 survey record is the section of `research/engine-survey.md` for each family of the milestone, extended in the commit of the implementation and on issue #93 with each operation's routine, its source and revision, the decision and its reasons. The survey can keep an existing binding, for example `mor.sets.matrix_ker` with Sage `right_kernel()`.
3. Each operation is glue over the chosen engine and hand-rolls no algorithm. The control logic of an operation is glue and stays with its leaf (C22).
4. The registrations of the row move into the category implementation and migrate to the v2 SDK; a hand-rolled registration (`lim.sets.pullback`, `lift.bilin_module.restrict#obj`) is replaced by the engine routine.
5. The implementation computes no field that no request demands (FR-043), builds and runs with its actual dependencies only (C24), and leaves the kernel and the earlier implementations unchanged (C12, C23).

## Implementation order and dependency correction

1. T114's current changed-source/public-consumer feedback under #84 is complete; preserve it during the remaining work. Complete its timing records, test-run logs and application logs (T112, T127; FR-043). Then retain adequate existing foundations and prepare the actual source/public driver interfaces. Do not reopen checked setup to produce new receipts. A missing mathematical input becomes a lean-categories task before its consumer, and the workstream does it there ([execution order](tasks.md#execution-order)); downstream mathematics never fills it.
2. Implement T032 lowering and T013's concrete execution composition at their positions in the [task order](tasks.md#execution-order). Functional outputs needed by the executor are T017–T021/T026; source selection is T053–T056. These are parts of one functioning path, not preliminary standalone release projects.
3. Bind actual results and connect T038; remove transferred fallback paths. T041's real driver is prepared without T039 or broad mathematical coverage as a prerequisite. T027's shared outcome classification does not depend on completing suspension first.
4. Complete every required generic mechanism, protocol behavior, notebook and discovery/display function. No per-construct export freeze, preservation proof or early contributor trial gates this expansion. Full kernel readiness, not a first scalar or first RX-LIFT, enables substantial leaf work.
5. Separately situated leaf authors deliver the category implementations in the order of the [computational milestones](#computational-milestones), as established-engine glue against the actually built released contract. The retained registrations move into those implementations. Integration then publishes T105's compatible tuple, including #90. No kernel-informed formalization assignment is bundled into leaf work.
6. Complete independent assessment, source-to-machine/correctness arguments, original fixed and frozen-extension observations and the final performance phase on that delivered tuple. Relevant corrections republish the tuple and reexecute affected obligations without weakening them.

The former edges T041←T039, T030←T029, T038←the complete deferred/suspension chain, expansion←T079, and functional construction←self-consistency-only proof/audit tasks are removed in the actual task entries. Proof responsibilities formerly mixed into functional T016/T043/T044/T046/T053–T056/T061 are assigned to T014/T039/T052/T062/T070/T076/T096 as appropriate. Nothing is declared proved by that reassignment. Required source-law validation in an actual invocation remains functional and cannot be omitted.

## Validation and retained final obligations

Functional checks ask whether the actual public responsibility path exists and performs the claimed operation. If the same test could pass with the lowerer or concrete executor deleted because its fixture supplies that function, it is not a check of that story. Test-only providers may check protocol failure mechanics, but are not mathematical execution. Existing independent mathematical assertions remain the authority for their answers; no new easier specimen replaces them.

During functional work use the actual source, role and runtime checks needed to implement behavior, with sufficient resources. Do not select work from reading counts, repeated frozen exports, green internal audits or benchmark failures. Self-consistency-only evidence and general proof completion come after required functionality under C21. A red expensive aggregate does not prohibit implementation of other required functions.

The final denominator is unchanged: all 153 permanent readings; 134 positive extension questions in 14 files (105 original plus 29 completion); protected negative/environment controls; RX01–RX10 and complete RX-LIFT; at least four real-engine workflows across three areas with all 17 original connected assertions; all prescribed independent extensions and mechanism arguments. Full B0 K1–K14, all 26 K13 IDs and broad Sage parity remain separately assigned by #19.

Final performance retains the original 99-root 3×3 specimen, strict under-60-second total on the measured host and phase accounting, and full RX-LIFT with 22 prerequisites and the shared 200,000-heartbeat preparation/evaluation limit. Earlier higher-limit functional runs do not discharge those final budgets. Neither changing a required question nor calling a timeout an expected negative satisfies them.

Proof obligations retain their original quantifiers: semantic safety under arbitrary provider behavior; conditional preservation/progress under independently fixed primitive relations and stated operational hypotheses; actual complete execution/independent assessment of the designated delivery. Generic library laws, structural validation and arbitrary provider correctness are not interchangeable. Independently frozen trials keep contributor choice, permitted inputs, zero accommodation and affected repair/refreeze/rerun requirements, but no longer block implementing required kernel capabilities.

## Source organization recorded at `e24045ca`

This section records how the source on branch `integration/kernel-v1-20261106` is organized and which engineering choices it makes. Read the source before you rely on a statement here.

### Production path

Source text runs through `SourceSession.readStatement` (`CasCompiler/ReadSession.lean`, `ReadExpression.lean`; `Read.lean` retains the term-notation facade and public exports) → `CasCompiler.lowerTerm` (`Lower.lean`) → `CasRuntime.Kernel.execute` → the framed provider connection → a retained binding. `#cas` and `#cas_tests` call it through `CasRuntime.KernelSession` (`CasRuntime/Session.lean`). The reader produces native Lean terms whose meaning comes from lean-categories registry rows; it computes nothing. Computation is dispatched to leaves, and without leaves a computational statement ends in `NoImplementation`.

### Source facts added through `9165255`

- **Selected data in the reader.** `NativeSourceCategory.limit` and `SourceCategoryBinding.limit` hold the row and the cone of a limit; `sourceLimitLeg?` reads them. A named map states its ends as projections of its own arrow; `declaredEndpoint` (`CasCompiler/SelectedMorphism.lean`) gives the declared end, and each reader rule that inspects the source or target of a map uses it.
- **Statements.** `SourceStatement.settled` holds every settled typing judgement of an assertion. `X ⊆ Y` for named sets is such a judgement, settled by `sourceCoercion?`.
- **Outcomes.** The reader tags an unknown name (`unknownSourceNameTag`); the session keeps the definitions that did not read (`KernelSession.unread`) and reports a use of one as that definition's outcome. The dependency check tags a missing runtime value with its binding (`missingValueTag`).
- **Trial readings.** `keepTrialAmbiguity` raises an ambiguity that a candidate reading produced; other failures of a trial are discarded.
- **Aggregate.** `CasCatalogue.lean` does not import `Language`, `Realize`, `Codec` or `Admission`.
- **Feedback.** `just loop`, `just slow`, `just milestone`, `just stop` (`scripts/feedback.sh`); run records in `timing/`; the acceptance report of a file holds the milliseconds of each statement.

### Dependency boundaries

Checked computation declarations and `ProgramBoundary` belong to `CasCompiler/Program.lean`. Runtime operand binding, request and response admission, and the operational signature belong to `CasRuntime/PreparedRequest.lean`. Source-only program work imports the former; lowering and execution consume the latter.

`CasCompiler/SourceRoutes.lean` owns first-binding route formation and retains its immutable source inventory. `OperationFamily.lean` owns whole-family preparation; `FamilyConversion.lean` owns native family agreement. `SourceCarrier` imports route formation directly. The numeral, method and operation readers import their required family operations explicitly. Cell comparison and coherence remain in `Resolve.lean`.

`CasRuntime/Realization.lean` selects from the admitted manifest and frozen profile. `Encode.lean` prepares dependent invocation packets. `Kernel.lean` consumes both. Connection and transport modules remain independent of source-language reading.

The expression reader now assembles typed rule modules, and runtime manifest/connection/invocation/demand responsibilities have separate owners with `Kernel.lean` as assembly. These source cuts must remain while their consumers are corrected; moving a responsibility is not proof that its mathematical preparation has been repaired. These boundaries must preserve the original source-to-result computations, including constructed values consumed through their target-category interface. Focused checks establish only the behaviour they exercise; independent mathematical acceptance remains separate.

### Engineering decisions

Each is a delegated engineering choice (constitution C17), except the kernel-side decisions of equality in rows 3 and 7. Those two contravene C22, and T113 replaces them. Choices that change what a leaf sees must be published by T028.

1. **Arguments of a published operation** are the dependent invocation context of execution contract §4.1 (`kind`, `prepared_role`, `parameters`, `bindings`, `arguments`, `argument_layouts`, `result_layout`). A registered named constant is a descriptor `{"ctor": <catalogue id>, "args": [...]}`.
2. **Operation address**: the family id, with `#<field>` when the reached field is not the first computational field.
3. **Named elements**: a generator is the descriptor `<object id>#generator`, a subset literal the descriptor of its `SubsetLiteralEntry` id whose finite set is the array of its elements (each element a retained slot), an admitted element the data of the value it admits under its own role (an element of a subtype is the record whose one field is that value), a numeral the descriptor of its `NumeralEntry` id (`{"ctor": "num.rings", "args": [<ring>, k]}`), each at its explicit parameters. A comparison with a numeral decides the closed equality in Lean. This contravenes C22: no procedure registered in lean-categories takes part. T113 replaces it (rows T113 of "Kernel computation (C22)" in the task list).
4. **Delayed families** are closures; realization is selected when an action reaches actual arguments.
5. **Input forms**: the complete-request form `<id>#input`, plus the exact form of each argument that is a registered named object.
6. **Retention**: a definition keeps a runtime value when its evaluation dispatched to a provider or its value holds a closure of a published family or provider-owned data (a delayed lift); other definitions, including lambdas and matrix literals the user wrote, are read from their definition.
7. **Questions**: a question about a retained value compares returned packets; a closed question is discharged in Lean through the registered literal evaluations (`CasCatalogue/Evaluation.lean`). `x ∈ Y` and `x in Y` for an object `Y` are settled by reading `x` in `Y`. This choice contravenes C22 where the session decides the equality of returned values itself; task T113 replaces it.
8. **Evaluation algebra**: `p(a)` for `a` in the coefficient ring uses `Under.mk (𝟙 R)` (lean-categories `Polynomials.evaluation_own`); otherwise the unique registered `R`-algebra on the argument's set.

## Artifact and source map

The feature directory holds the artifacts: [specification][S1]/[requirements][S2], this plan, [research](research.md), [data model][D], [mathematical input][M], [runtime][R], [notebook][N], [validation][Q], and [tasks Part 1][T1]/[Part 2][T2]. The [requirements-quality checklist][CHK] (`checklists/architecture.md`) remains reviewer-owned; this plan edit does not approve its markers.

Production locations remain `CasCompiler/{Context,Elaborate,Read,Resolve,Program,Lower,Correctness}.lean`, `CasRuntime/{Value,Owner,Occurrence,Transaction,Execute,Realization,Inspect,Correctness}.lean`, actual `CasDsl`/`CasCatalogue` public entrances, the released contract/SDK and the actual notebook worker/client. Task locations are implementation responsibility, not an obligation to preserve redundant helpers or match historical file organization.

The exact Spec Kit task/analysis instructions used in the prior plan are pinned at `34a0d388eac671d656eb05b125ad3ed6056168ed`: [tasks command](https://github.com/github/spec-kit/blob/34a0d388eac671d656eb05b125ad3ed6056168ed/templates/commands/tasks.md), [task template](https://github.com/github/spec-kit/blob/34a0d388eac671d656eb05b125ad3ed6056168ed/templates/tasks-template.md), [analysis](https://github.com/github/spec-kit/blob/34a0d388eac671d656eb05b125ad3ed6056168ed/templates/commands/analyze.md). Their functional-story checks motivate the corrected boundaries; the user's current constitution/handoff governs project-specific sequencing and full scope. No native Spec Kit CLI run or implementation build is claimed by this documentation revision.

[C]: ../../.specify/memory/constitution.md
[H]: https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6726232237
[S1]: spec.md
[S2]: spec.md
[M]: contracts/mathematical-input.md
[R]: contracts/computational-runtime.md
[D]: data-model.md
[N]: contracts/notebook-session.md
[Q]: quickstart.md
[T1]: tasks.md
[T2]: tasks.md
[F]: https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6737120228
[CHK]: checklists/architecture.md

## Required model at implementation entry

Read [the mathematical execution model](../architecture.md), constitutional C23 and
[MM001–MM012](spec.md#mathematical-model-acceptance) before applying this plan.
The local source, runtime, session and data-model contracts state the same preservation boundary.
Each implementation change must reach its original public mathematical continuation. Work records
and evidence remain in their owning issues.

The [development boundaries](../../AGENTS.md#development-boundaries) and
[feedback loops](../../CONTRIBUTING.md#feedback-loops) apply to that same implementation.
They specify boundaries for source preparation, actual request binding, generic execution and final assembly;
they do not authorize preserving reconstruction machinery behind those interfaces.
