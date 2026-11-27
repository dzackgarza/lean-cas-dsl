# Implementation Plan: Categorical research language

**Feature:** `001-categorical-research-language` · **Updated:** 2026-11-25 (Asia/Taipei).

**Authority:** [current permanent constitution][C], especially C6 and C21; [owner's current functional handoff][H]; [specification and scenarios][S1]; [requirements and acceptance][S2]. **Operative tasks:** the [task list][T1]: Part 1 is the kernel; Part 2 holds the category implementations, the notebook unit, the functional work of M4 and M5, then the evidence and the final performance.

## Summary and completion target

Make the kernel fully ready to accept leaf work, then deliver all independently required V1 computations and observations. Every required generic capability must work through the public interface: no lowerer, executor, source-selection gate, result continuation, advertised protocol operation or public entrance may remain a stub. The full mathematical product, higher/infinite scope and later full-B0/parity assignments remain those of the constitution and specification; a successful toy example or first construction is not kernel readiness.

The required production composition is:

`public source → complete selected judgment → compiled OperationalProgram → concrete prepared-request executor → actual framed provider invocation → admitted retained result → subsequent source use`.

The lowerer and concrete executor are separate implementation responsibilities using the existing dependent request/response interface. They follow the [task order](tasks.md#execution-order). Connecting them is part of their functional story, not a final integration phase after protocol research, preservation proofs, exports or independent trials. The public command must use this composition, not continue using the old reconstruction interpreter while helper programs exercise the new components.

The source/runtime boundary remains categorical and independently specified. A leaf implements the released computational obligations; it does not define the categories, laws, choice family, denotation or correctness criterion. A declared preferred route under C6 is registration data selecting an admitted binding, not a proof that routes agree. Actual accepted comparison cells retain their components and coherence. Missing required data produce the prescribed error before dependent dispatch.

## Technical context and retained decisions

| Responsibility | Decision and limit |
|---|---|
| Language/runtime | Lean 4.33.0 on the kernel branch (T352 ports it to the toolchain of the research image, #90), ordinary checked Lean term formation, source-derived dependent programs, actual runtime value/owner/transaction state. Python supplies the released SDK and notebook client, not a second mathematical interpreter. |
| Logs and timing records | FR-043 (constitution C24): the Phase 0 tasks T112, T127 and T300 of the [task list](tasks.md#phase-0--fast-edit-to-result-feedback); later tasks extend the application log with their mechanisms. Diagnostics shown to the user stay opt-in (#8). |
| Mathematical authority | Independently accepted lean-categories declarations, actual structural/constructor actions, complete operation families and abstract computation interfaces. Kernel/leaf authors do not commission subject mathematics shaped to their implementation. |
| Operational substrate | Reuse CSLib `PFunctor.FreeM` at `3951377e5a3f5772737f11cd62bc5bb6a72f95d1` and PolyFun stateful handlers at `a5895e454254a400774fa396b64d5b968f0933df`, with compatible Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. These libraries provide sequencing, not a CAS lowerer or concrete executor. |
| Dependency policy | Actual compatible own-organization latest-main inputs at delivery; record exact diagnostic tuples without making every upstream change a new implementation phase. Do not change locks merely to revise this plan. |
| Existing work | Reuse adequate context/source intake, value/owner/transaction/scope machinery and structural route closure. The handoff says not to rebuild the context, program, value, owner, transaction and scope machinery (T005, T006, T009–T011, T018) or the existing route closure (T053, T054) merely to obtain fresh internal evidence. Inspect actual current source before relying on a historical completion statement. |
| Storage | Immutable committed Environment-backed program/value/observation data; active-transaction staging; nonrollbackable live owner/reservation/transport-ID metadata. No second completed-payload store. |
| External boundary | Data-only versioned framing, exact dependent roles and scoped references, existing engines, retained callable ownership, no automatic retry/replay or provider-priority fallback. All advertised deferred/suspended behavior needs a real kernel handler. |
| Platform | Existing authorized execution environment and actual CAS/notebook surface. No owner-machine access, new persistent environment or alternate frontend is a planning prerequisite. |
| Legacy bridge | T024/T025 are retired by the current owner order. Do not revive v1 bridge work as a prerequisite. Existing retained implementations move to v2 through their separate public-only owners after kernel readiness, in the category tasks of the [computational milestones](#computational-milestones). Their original mathematics and acceptance questions remain unchanged. |
| Budget phase | C21 governs: functional work may use the time/memory/heartbeat limits needed. Original budgets remain final obligations, including the 99-root 3×3 specimen under 60 seconds and RX-LIFT's shared 200,000 heartbeats/full 22-binding prefix. Fast development feedback remains an immediate continuing priority; other optimization cannot select functional work except the narrow C21 cannot-finish-at-all exception. |

The scoped contracts remain [mathematical input][M], [computational runtime][R], [data model][D] and [notebook session][N]. Their behavioral requirements remain binding. The schedule in this plan and tasks implements the current C21 order; it does not reintroduce their historical first-use-proof, early-freeze, v1-bridge or budget gates. Exact changes of responsibility and proof ownership are specified below, not left to an implementer to reconcile contradictory task dependencies.

## Constitution check and repaired planning defects

The former plan failed to make its first story independently functional: it put the protocol story before the lowerer and public entrance that its own test required. It also placed integrated drivers behind proofs and broad support tasks, and treated requirement tags and an acyclic graph as evidence of adequate functional sequencing. Those are rejected planning assumptions, not waivers for implementation.

The corrected design has these consequences:

- C0–C4: every story reaches actual public behavior through the same source-derived lowerer/executor; no test-provided request or executor supplies the production capability being claimed.
- C5–C8: actual selected routes, cells, allowed choices and defining maps survive compilation, execution and later use. Native well-typedness does not erase additional source-required coherent data.
- C6: enumeration of first bindings is distinct from proving agreement. Complete-family definitional agreement or independently formalized comparison can establish agreement; a declared preferred route selects an admitted reading without asserting agreement. Without the required resolution data, ambiguity is reported before execution. No shortest route, backend success or unregistered theorem search substitutes.
- C9–C13: mathematical authorship, candidate computation and independent acceptance remain distinct; original observations, extension trials and exact lifetime/publication rules remain due.
- C16–C20: preserve existing useful implementation, remove transferred reconstruction paths and inspect the actual public responsibility path. No task waits: an input is the result of a named task, which the workstream that needs it does first, in the role that the task names ([execution order](tasks.md#execution-order)). Documentation edits do not claim implementation or independent approval.
- C21: current fast development feedback comes first and remains active. Complete kernel functionality comes before substantial leaf work, self-consistency-only evidence, frozen trials, preservation/correctness proofs and final mathematical/runtime performance work. Actual type/domain/data/owner checks needed to perform a function remain part of that function; postponing proof documentation does not permit an unsound runtime shortcut. A task that needs a declaration missing from lean-categories has a lean-categories task before it, and the workstream does that task there as formalization work ([execution order](tasks.md#execution-order)).
- C22: kernel work and leaf work are accepted separately. A kernel check observes kernel behaviour with a protocol peer or an empty manifest; a computed mathematical result is leaf work ([M1 checkpoints](#m1-checkpoints)).
- C23: category implementations are built in the order of the structural scaffolding of the categories, in milestones of their own after kernel readiness ([computational milestones](#computational-milestones)).

The governing constitution is [v5.0.0](../../.specify/memory/constitution.md) of 2026-11-27. Its adoption record names each amendment and its source; version 4.0.0 records the [owner instructions of 2026-11-25](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-7155201731), version 4.0.1 the owner decision on established computational implementations of the same date, and version 5.0.0 the rule that a dependency is a task done first (C14, C16, C21).
C0, C9, C21, C23 and C24 state source-derived complete category interfaces, separate
dependency relations, real locality, continuing feedback and full choice-sensitive assessment.
No amendment changes an original mathematical question or a final budget. Earlier
constitution hashes remain historical input provenance.
C24's timing records, test-run logs and application logs are current work (FR-043): C21 puts
only final performance and self-consistency evidence after functionality.

## Source-to-result rule

Each functional task applies the [source-to-result rule](tasks.md#source-to-result-rule) of the task list and the [development boundaries](../../AGENTS.md#development-boundaries). The current changed-source feedback of #84 stays an immediate priority under C21; final mathematical and runtime optimization follows functionality.

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

Transferred uses lose the old `Language`/`Realize` recognition, endpoint retry, producer reconstruction and alternate completion writes through T051/T064. No new caller enters the superseded path. The existing acceptance driver is adapted at T041 without a proof prerequisite; it calls the public production interface rather than creating requests or injecting an executor. Its original mathematical inputs and expected outcomes remain intact. A required source dependency is the result of the task that supplies it, done first for its affected uses; the inherited numeral issue does not prevent implementing the generic lowerer, executor or other already specified source forms.

## Functional stories and their complete paths

The stories retain the specification's user outcomes. Shared code is implemented at its first actual use, then reused. Story dependencies below describe functional interfaces, not a requirement to finish unrelated areas before authoring the next function. No phase is declared complete on the strength of a helper-only test. US1 to US6 work before kernel readiness; US7 and US8 are the [notebook unit](#notebook-unit), after the category implementations. A story boundary is not a reduced deliverable or permission to stop.

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

US2–US6 use the shared production path developed with US1; this dependency is explicit, not a claim that a protocol-only phase is independently executable. Their generic capabilities use that interface in the fixed task order; the interface does not authorize separate active tasks. US7 and US8 are real integration, not mock frontends or polish. US9 is Phase 0 of the task list (T114, T351, T112, T354, T127, T300). US10 is delivered by the [computational milestones](#computational-milestones).

## Completion milestones

These are complete delivery outcomes, not file/module counts or a second task queue.
[Tasks](tasks.md#execution-order) retain stable IDs, definitions and execution order.
[GitHub #10](https://github.com/dzackgarza/lean-cas-dsl/issues/10) owns the roadmap and evidence;
native milestones record each issue's full closure stage. A broad owner issue can contribute
functional work earlier while retaining its later proof and acceptance obligations.

| Milestone | Complete observable outcome | Owners and scope |
| --- | --- | --- |
| [M0 — Fast edit-to-result feedback](https://github.com/dzackgarza/lean-cas-dsl/milestone/1) | A substantive edit in the current owner rebuilds affected executable dependencies and runs the unchanged public consumer within the normal focused-loop bound. Current diagnostics, failures and timings are truthful. Retain this behavior throughout development. | #84, T114/US9; reuse T016's completed work without treating its historical timing as current readiness. T351 (the inherited worktree committed by mechanism), then T112, T354 (the first statement of `sets.cas` within the loop bound), T127 (FR-043: timing records, test-run logs, application logs) and T300 (a truthful acceptance run) continue this capability as the first unchecked tasks; they are kernel milestone K0. |
| [M1 — Complete generic categorical kernel](https://github.com/dzackgarza/lean-cas-dsl/milestone/2) | F: all Part 1 functionality works through real public entrances, including complete constructions and later use, both functor actions, selected lifting/refinement/comparisons, higher/infinite interfaces, protocol and both directions of growth: every DSL script of the acceptance and extension files runs through the public session. F needs no notebook. Its checks observe kernel behaviour and require no computed mathematical result (constitution C22). It has [checkpoints](#m1-checkpoints). M1 is the sequence of [kernel milestones](#kernel-milestones) K0 to K20 and F; each is one file or one named group of files of the permanent and extension workloads, and F is the last. | #92; #66/#69 and #82/#85/#91 supply their functional responsibilities; #86 closes here. The first complete construction is an internal step, not this milestone. |
| [M2 — V1 category implementations and delivery](https://github.com/dzackgarza/lean-cas-dsl/milestone/3) | The [computational milestones](#computational-milestones) deliver the category implementations in mathematical order. All required V1 category implementations supply actual computations, defining data and later uses through the released contract; publish and build one compatible mathematics/kernel/contract/leaf/worker tuple; the notebook unit completes the delivery and republishes the tuple with the protocol-2 worker (T093). | #93, the V1 category tasks of the [table](tasks.md#complete-the-required-computational-implementations-and-actual-delivery-tuple), T352 and T105; #90 at T352 supplies the research-image toolchain/Mathlib port; the notebook unit (T083–T093, T010, T097–T099, T346–T348, T325, with lean-jupyter-kernel T003–T014; #69 and #24 hold its obligations). |
| [M3 — Independently accepted V1](https://github.com/dzackgarza/lean-cas-dsl/milestone/4) | All #24 A–F obligations, independent mathematical assessment, preservation arguments, frozen extension trials and original final budgets hold together on the delivered tuple. | #24 and full closure of #66/#69/#82/#85/#91; #97 records #10's unchanged V1 closure condition; the project root remains open through M4/M5. |
| [M4 — Full B0 and classified Sage coverage](https://github.com/dzackgarza/lean-cas-dsl/milestone/5) | Complete #19's K1–K14 computations and the separate versioned Sage coverage denominator, including required hypotheses, defining maps and continuations. | #19, #20, #21, #22, #23; the V2 category tasks (T255, T256, T258–T265) and the V3 tasks; the inventory and classification tasks T140–T147 with T225–T234; assessment and publication T160–T169. Their bounded construction/input work (T139) can inform V1 before their later full closure. |
| [M5 — Research and client completion](https://github.com/dzackgarza/lean-cas-dsl/milestone/6) | Complete the retained research facade, installation portability, unit-group delivery, opt-in logging and actual research-use demand work against their existing outcomes. | #68, #34, #3, #8, #13; tasks T148–T159, T349 and T353. These remain outside the V1 denominator. |

M1 consumes the functioning development loop. M2 consumes F and the usable released contract;
its notebook unit also consumes T105 and the category implementations of M4.
M3 consumes the delivered candidate. Within a milestone, use actual task inputs; an input is the
result of a named task, which the workstream that needs it does first ([execution
order](tasks.md#execution-order)). Native issue dependencies encode those real completion inputs,
not a requirement to stop every other task.

The image port is T352 in M2. When the actual available environment cannot build an active
functional task, T352 is the environment task of that task and the workstream does it first; an
image defect is a task of dzackgarza/sage, done there first. A fresh image or broad dependency
refresh is not an invented M0 prerequisite when the current compatible environment already
supports the work.

For full B0, F and the usable released contract establish implementation readiness. V1-required
implementation and delivery (the V1 category tasks, T105) have priority. The functional work of M4 (the V2
category tasks, T140–T147, the V3 tasks and T225–T234), then the [notebook unit](#notebook-unit), then the functional work of M5 (T148–T159),
follow the V1 delivery and come before the evidence-only work of every milestone, because C21 puts evidence-only work and final performance after required
functionality; V1 evidence (M3) keeps its priority over the evidence of M4 and M5, and final
performance (T103) is last. The V1 denominator does not grow: an M4 or M5 result is no V1
acceptance criterion. Final V1 acceptance is neither full-B0 completion nor a new mathematical
input to broader algorithms.

**Decisions for M3, M4 and M5.**

- The K3 and K14 files run unchanged (T162); their admission is the owner's act on
  `CasAcceptance/Permanent/admitted.json`.
- K1 and K13 need a registered execution in the computation-only report, as the B0 directive of
  2026-10-01 requires; a registered proof procedure may settle them in the normal report (C22).
  K4 holds in either report (#19 inventory).
- M4 is assessed by the assessment role A, with the permitted inputs of acceptance authorship, on
  the fixed questions, slices and failure controls against independent expectations (T169). #19
  prescribes no frozen extension trial for M4.
- The advertised installation of #34 is the research container's Sage 11.0.beta5 at
  `/sage/.venv/bin/python3`; no other platform is advertised (C24, platform scope).
- The unit group of #3 is `fun.monoids.units` of Groups Spec V2 (T256); its methods are those of
  its workload: the group operations of the returned group and the invariants that tell
  $(\mathbb{Z}/8)^\times$ from $C_4$. T155 observes it through the notebook path.
- The records of #8 diagnostics are the events of the application log of FR-043 for the current
  request; #8 adds their display on request and no second store.
- The consumers of #68 are the sage-extensions files that FR-093 names (present at
  sage-extensions `ce368d7`); the closure of research#606 does not affect them.
- #23 holds the higher-coherence inputs of M4 after #82 closes at M3 (T147).
- The contribution policies move from the #85 comment into `CONTRIBUTING.md` (T183).

**Diagnostic surface.** The user turns diagnostics on with Lean's option commands: `set_option trace.CasDsl.execution true` for the later cells of the session, and `set_option trace.CasDsl.execution true in #cas …` for one command; a section scope covers several commands of one cell. #8 settles this form: it applies the opt-in, per-cell or per-notebook logging ruling of August 6 through Lean's scope and trace controls, and it adds no notebook magic parser. T157 implements the classes, levels and scopes in this form.

### Kernel milestones

M1 is a sequence of small vertical milestones. Each runs one acceptance file, or one named group of statements, of the permanent and extension workloads through `CasRuntime.KernelSession` with the empty manifest and with protocol peers. Its one check is `just loop` on those files, as the [task list](tasks.md#kernel-milestones) states, together with the checks of its tasks. The order starts with `sets.cas`, as the computational order starts with sets, and ends with F. A milestone holds the tasks whose checks run its files or that its M1 checkpoint names, with the inputs that they name in `After` (including the upstream tasks of their sibling inputs) and that no earlier milestone holds; the task list places each task in its milestone and runs the milestones in this order. A defect that the run shows and that no task of the milestone owns gets its task in that milestone. The next milestone is the first one with an unchecked task.

| Milestone | Files of its check | Checkpoint | Tasks |
| --- | --- | --- | --- |
| K0 | the checks of its tasks | — | T351 T112 T354 T127 T300 |
| K1 | `sets.cas` | M1.1, M1.2 | T116 T027 T007 T303 T009 T011 T123 T308 T131 T138 T056 T017 T021 T020 T026 T121 T032 T119 T129 T113 T019 T013 T042 T038 T120 T035 T128 T048 |
| K2 | `finite_sets.cas` | — | T031 T314 T065 |
| K3 | `functions.cas` | — | T030 T305 T124 T059 T320 T321 |
| K4 | `inverses.cas` | — | none (check only) |
| K5 | `numbers.cas` | — | T053 T054 T312 T122 T132 T034 T073 T345 |
| K6 | `fractions.cas` | — | none (check only) |
| K7 | `polynomials.cas` | — | T125 T136 T036 T317 T135 T057 |
| K8 | `composed.cas` | — | T037 |
| K9 | `factorization.cas` | — | T313 T344 T066 |
| K10 | `linear_algebra.cas` | — | none (check only) |
| K11 | `lattices.cas` | — | none (check only) |
| K12 | `several_variables.cas` | — | T315 T343 T137 T316 |
| K13 | `differentials.cas` | — | T050 |
| K14 | `calculus.cas` | — | T067 |
| K15 | `series.cas`, `ellipses.cas`, `rx09-successor-series.cas`, `rx09-constant-one-rejection.cas` | M1.6 | T068 T069 |
| K16 | `algebras_schemes.cas` | — | none (check only) |
| K17 | `rx-lift-prescribed-stages.cas`, `rx-lift-source-comparison.cas`, `rx08-ordinary-kernel.cas` | M1.4 | T043 T044 T130 T046 T049 |
| K18 | `rx05-carrier-diamond.cas`, `rx06-reindexing.cas`, `rx07-f9-transport.cas` | M1.5 | T055 T309 T058 T118 T115 |
| K19 | `rx01-selected-orders.cas`, `rx02-two-subsets.cas`, `rx02-complete-core-action.cas`, `rx03-cyclic-automorphisms.cas`, `rx03-complete-automorphism-arrows.cas`, `rx04-square-bound.cas` | M1.7 | T134 T061 T323 T074 T075 |
| K20 | `rx10-fixed-execution-question.cas` | M1.8 | T018 T022 T324 T023 T028 T100 T101 |
| F | every file of the permanent and extension workloads | M1.3 | T301 T302 T304 T306 T307 T310 T311 T033 T342 T318 T319 T060 T322 T051 T064 |

### M1 checkpoints

M1 closes on F. Before F, these checkpoints close one at a time. A checkpoint is one observation of kernel behaviour through the public session `CasRuntime.KernelSession`, on the original source inputs that its row names, with a protocol peer or an empty manifest (constitution C22; SC-014). It closes when the observation holds on the kernel branch. It claims only itself. It satisfies no user story: the acceptance of a story needs computed results and is assessed when the category implementations exist. It checks no task box, and the independent assessment of the same inputs stays in Part 2. Issue #92 holds the checklist.

The observation of a checkpoint is first made in the closing of the kernel milestone that its last column names. It is part of that milestone, so it serves the active task. A checkpoint that does not hold then is observed again at the close of each later task until it holds. A condition on the source text, such as the removal of a mechanism, belongs to the definition of a task (T116, T051, T064, and the rule "Typed selections" of the task list) and not to a checkpoint.

No checkpoint was evaluated on 2026-11-25. A checkpoint whose observation already holds at the close of its milestone is checked then. The observation, not a task box, decides.

`RX` inputs are the files of `tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/`, which `just loop --extension` runs (T300).

| Checkpoint | Observation | Inputs | First observed at the close of milestone |
| --- | --- | --- | --- |
| M1.1 — Typed carriers | A different source input of equal value is rejected. Two bindings with equal defining expressions stay distinct through a projection, a substitution and a later call. An absent selection is an error at the reader. Two selected limits with one apex keep their own cones. | The checks of T116, T032 and T048 | K1 |
| M1.2 — Connected statement path | A source file runs through one session. Each statement is read, lowered and dispatched to a protocol peer at its registered address with its actual operands. The reply is admitted and retained, and a later statement uses that value with no second dispatch. | `tests/acceptance/sets.cas`: its definitions `A`, `f` and `g` and the later statements that use them | K1 |
| M1.3 — Forms of connected calculation | Every statement of the permanent acceptance files reads to its registered meaning. With an empty manifest, each computational statement ends in no implementation at a registered address. No statement ends in an internal error or a reader gap. | Every file of `tests/acceptance/*.cas` | F |
| M1.4 — Construction and later use | The original RX-LIFT source with its 22 bindings prepares each lift field, comparison and factor request at the selected lift, with the earlier outputs as operands. The returned object, maps and factor are the operands of the later requests. | `rx-lift-prescribed-stages.cas`, `rx-lift-source-comparison.cas`, RX08 | K17 |
| M1.5 — Selected structures | The inputs select their routes, cells, classifiers and reindexing before dispatch. A required omission is refused with no dispatch. A declared choice-producing operation binds the member that the peer returns (T115). | RX05, RX06, RX07; an operation that lean-categories#182 registers | K18 |
| M1.6 — Exact, infinite and qualified requests | The inputs prepare requests that keep the exact source, the tolerance and the full index family. A demand outside an earlier finite display reaches the same retained object. | RX09; the ellipsis, series and approximation statements of the permanent files | K15 |
| M1.7 — Growth | A new accepted declaration reaches an unchanged consumer, and a new generic operation reaches an existing object, with no kernel edit. | RX01 to RX04; the checks of T073 and T075 | K19 |
| M1.8 — Computational contract | A peer written from the published contract alone uses deferred and suspended service, and an unchanged consumer receives its output. A peer that asks for an operation with no implementation receives the no-implementation outcome and continues. The published interface matches the built kernel. | RX10; the checks of T022, T023 and T324 | K20 |

### Notebook unit

The notebook unit (US7, US8) is functional work after the category implementations of M4 and before the functional work of M5 and all evidence-only work. F needs none of it. Its tasks are T083 to T093, T010, T097 to T099, T346 to T348 and T325 of the task list, each with its sibling task in lean-jupyter-kernel (`specs/001-worker-protocol-2/tasks.md`). lean-jupyter-kernel T003 lands the protocol-2 worker; its toolchain task T004 follows the port of T352, so the worker and the kernel change toolchain together; its release T014 is the pin that T093 locks when it republishes the tuple. M5 consumes the unit: the client of #68 runs over the worker, and the unit group of #3 and the diagnostics of #8 use the notebook path.

### Notebook checkpoints

These kernel checkpoints (SC-014) follow the rules of the M1 checkpoints and belong to the notebook unit. Issue #93 holds their checklist.

| Checkpoint | Observation | Inputs | First observed at the close of |
| --- | --- | --- | --- |
| N1 — Notebook | The cells run through the worker and one session: values retained across cells, inert queries, cancellation and owner rules. | `notebooks/kernel-v1.ipynb` | T093 |
| N2 — Discovery and display; old resolver removed | Discovery and inspection read retained data and execute nothing. `#resolve`, `#methods` and `cell%` answer from the new resolver. | The workflow questions of `notebooks/kernel-v1.ipynb`; the commands of `CasDslTests/Cells.lean` | T325 |

### Issue tree and task order

The native root is [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10), which stays open
through every retained phase. V1 completion is recorded by M3/#97 under the unchanged
#66/#69/#24 condition; it does not close the project root while M4/M5 remain.

| Direct-root milestone ledger | Ordered complete work owners |
| --- | --- |
| [#94 — M0](https://github.com/dzackgarza/lean-cas-dsl/issues/94) | #84 / T114 |
| [#95 — M1](https://github.com/dzackgarza/lean-cas-dsl/issues/95) | #92 / F, with the M1 checkpoint checklist in #92; #86 at T307 within F |
| [#96 — M2](https://github.com/dzackgarza/lean-cas-dsl/issues/96) | #93 / the V1 category tasks, then T352 (#90), then T105, then the notebook unit |
| [#97 — M3](https://github.com/dzackgarza/lean-cas-dsl/issues/97) | #24; full remaining obligations of #66, #69, #82, #85, #91 (T170–T194 with Part 2) |
| [#19 — M4](https://github.com/dzackgarza/lean-cas-dsl/issues/19) | #22 / full B0 and classified Sage delivery (T160–T169, the V2 and V3 tasks); #20, #21, #23 supply full-parity inputs (T139–T147) |
| [#98 — M5](https://github.com/dzackgarza/lean-cas-dsl/issues/98) | #68 (T148–T152), #34 (T153, T154, T349), #3 (T155, T156), #8 (T157, T158), #13 (T159) |

`itree next` selects the completion owner; the unchecked task order selects the current work
within its scope. #84/T114 came first and is closed on its complete current loop evidence;
later tasks inherit the continuing C21/C24 obligation. T351, T112, T354, T127 and T300 (FR-041, FR-043) are the first
unchecked tasks. They continue that capability under #92 and do not reopen #84. The former
full-#85 blocker of #84 is obsolete.
M1 consumes that capability, M2 consumes F, and M3 consumes the delivered candidate. Native
group dependencies keep a later proof/assessment owner or subsidiary delivery issue after those
required inputs.

Execute #86's whole scoped-declaration requirement at T307 and close it on its original
acceptance within #92. Execute #90's whole image requirement at T352 and close it on its
original acceptance within #93. Their sibling positions do not postpone those implementations
until after F or delivery. The broad M3 owners contribute their functional requirements at
the existing positions under #92; their later full closure never gates that functionality.

Within M3, #24 coordinates the remaining Part 2 work in document order with its separately
assigned proof, engineering and independent-assessment owners. Close each broad owner only
when its own complete requirements hold; its later sibling position does not postpone its
contribution until after acceptance. T110 records V1 closure at #97 and preserves #10 for
the remaining project phases.

An environment that the active task needs and that the current container lacks is the result
of T352 (the #90 port) or of a task of dzackgarza/sage (the image). The workstream does that
task first, under the [execution-order rule](tasks.md#execution-order), and returns to the
active task; the native completion dependencies do not prevent it, and no full-F-before-repair
cycle is added. If native traversal must select #90 for that repair, the #92 dependency of
M2/#96 is removed for the repair and restored when the active environment is usable; #93's own
#92 dependency stays. T352 closes #90 on its original acceptance. An input that only an
independent role authors is the result of the task of that role, which comes before its actual
consumers. Full B0's executed coverage consumes F and #20/#21/#23, without a #24
evidence-completion prerequisite; early source/input work remains available. #22 owns both
complete M4 execution outcomes already specified in #19. Its whole issue does not depend on
unrelated full-Sage inventory work:
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

Computational work is leaf work (constitution C22, C23; FR-042). Its milestones are versions of category implementations, separate from the completion milestones above. Each category implementation is its own Spec Kit feature in lean-cas-dsl-leaves (`specs/<NNN>-<category>/`) with the versioned milestones V1, V2 and V3: V1 holds every spike computation and every statement that kernel V1 requires computed; V2 the remaining full-B0 statements of #19; V3 the classified Sage coverage of #20, #21 and #23. The work starts after kernel readiness: the contract that an implementation is written against is published by T028, completed by T100 and T101, and released at F. Each category version is one task of the task list, `Implement <Category> Spec V<n>`: the V1 tasks (M2), the V2 tasks and the V3 tasks that the classification adds (M4). A category has a task only when a row of the version has its home there: 33 categories have a leaves spec (`specs/002-cardinals/` to `specs/034-ideals-r/`), and the categories with no row in V1 or V2 have no task and no spec. The [table of the task list](tasks.md#complete-the-required-computational-implementations-and-actual-delivery-tuple) maps each task to its category, its version and its leaves spec, which cites it. Issue #93 holds the checklist of the V1 tasks; M2 closes when they hold on one published tuple (T105). The computation behind the list is [`research/category-scope.md`](research/category-scope.md) (data `category-scope.json`), which works back from each computation of the spike inventory, the workloads and the K3 and K14 files to the rows and categories that it needs.

**Order.** The implementation of a category follows the implementations of the categories that its structural functors and classifier forgets reach (`research/scaffolding.json`, lean-categories `443fba9`). 49 of the 100 registered categories have such a chain to `cat.sets`. The other 51 follow one rule: **a category with no structural chain to `cat.sets` is implemented after the categories that its formal definition is built from** — the argument categories of $\mathrm{Arr}$, $\mathrm{Core}$, a slice, a coslice, a functor category or a category of elements; the base and the classifier host of a refinement; the parameter categories of a family fibre; the host of a classifier total. An atom with none of these inputs (`cat.cardinals`, `cat.cardinalities`, `cat.ordinals`, `cat.walking_pair`) is a root: no implementation precedes it, and it enters with the first milestone that needs it (`cat.cardinals`, task T201, directly before Core of sets T203; the work starts with sets, T202). A category whose structural functor lean-categories does not register yet enters after the upstream task that adds that functor, at the place that the functor gives it. Reason: an object of a built category is made of objects and maps of its inputs (an object of $\mathrm{Arr}(D)$ is a map of $D$; an object of $\mathrm{refine}(B, c)$ is an object of $B$ with evidence for $c$), so its public constructors consume their public constructors, exactly as a structural functor makes its source consume its target (C23, "functor actions construct their targets"; MATH002). The order applies the changes of the upstream tasks that precede the milestones: T131 adds the additive tower (`cat.additive_magmas`, `cat.additive_semigroups` below `cat.additive_monoids`), T133 replaces `cat.partially_ordered_sets` and `cat.totally_ordered_sets` by one tower of orders and puts `cat.boolean_algebras` above bounded lattices, and T225 to T234 (lean-categories #201 to #210) add the structural functors of the crystal, scheme, ideal, refinement, form, cusp and lattice categories. A category that a structural route passes through but that holds no row of V1 or V2 (`cat.cardinalities`, `cat.preorders`, `cat.partial_orders`, the additive magmas and semigroups of T131, `cat.core_groups`, `cat.commutative_monoids`, `cat.core_subobjects_sets`, `cat.subobjects_modules_r`, and the semilattices and lattices of T133) has no task: the rows on its route belong to other categories, so an implementation that follows it in this order follows the implementations of the categories that it reaches; a later version that gives it a row adds its task at its place.

**Statements.** A statement belongs to the task of the category that owns its rows: the latest category, in the order above, among the homes of the rows of the statement (`research/category-scope.json`; the rows of a statement are those of `research/workload-routes.json` or of `research/spike-inventory.json`), at the version of the statement; a V2 statement whose owner category has no V2 task needs only V1 rows and belongs to the V1 task of that category (FR-042; T202, T203, T218). A typing judgement (question kind `settled`) holds by elaboration and is no task's result. A spike computation that no workload statement carries is V1; the acceptance author writes its statement into the workloads (T327) before the task whose V1 it enlarges. Each catalogue row that a V1 computation needs and lean-categories lacks (`research/category-scope.md`, "Catalogue rows that a computation needs and the catalogue lacks") is an upstream task, T328 to T341 (lean-categories #212 to #225), before the category task whose leaves spec holds the row (the home rule of the leaves shared feature, research R16); the four rows that only a spike ceiling needs (`real_arctan`, `polynomial_gcd`, `polynomial_irreducible`, `uncountable_cardinal`) have no task. A version that makes no statement computable by itself serves later categories and is accepted by their statements. A V1 task belongs to M2; a V2 or V3 task to M4.

**Reading of ℤ and ℚ.** The list uses the readings that the selection rules give (C6, FR-016, FR-022): a written ℤ or ℚ has a reading at each registered object of that name, and readings whose complete operation families are definitionally equal are one reading. The commutative ring ℤ forgets to the ring ℤ by an identity (`NamedCommutativeRings.integersIdentification := Iso.refl _`, lean-categories `Catalogue/Semantics/Algebra/NamedCommutativeRings.lean:33-35`; the same for ℚ at `:48-50` and for the field ℚ at `Fields.lean:75-76`). So a ring operation on ℤ or ℚ has one reading, and a registration at the ring reading serves it. A statement needs `cat.commutative_rings` or `cat.fields` only when its operation is declared there. These are the ring rows of the recorded readings. The kernel report of 2026-11-22, which reads ℤ as the commutative ring and ℚ as the field under `+`, comes from a reader that forms one object candidate of a name; T305 forms one candidate for each registered object of the name, and T059 keeps the owner of an element in the judgement; it does not move a statement to a later milestone.

**Kernel computation.** Each kernel-side evaluation that a Part 1 task removes (rule "Kernel computation" of the task list) ends in the no-implementation outcome when that task closes. The V1 task of the category that owns the evaluated operation supplies the computation; the task line names it.

**Engines.** The research container holds Sage 11.0.beta5 as a source build and no passagemath. Its interpreter `/sage/.venv/bin/python3` (Python 3.14.10) imports Sage and pydantic 2.14.1; the v2 SDK of the contract at `a0417b0` declares `pydantic>=2.14.3`, so the image pins pydantic ≥ 2.14.3 for that interpreter (task T326, dzackgarza/sage#45, before the first category task). The milestones use the container Sage, because the container is the reproducible research environment and one environment cannot hold both `sage` packages (`research/engine-survey.md`, "Constraints for planning", items 1 and 2). GAP's Semigroups package does not load in the container; no statement of the milestones uses a finite semigroup or monoid given by a table, so no milestone needs it. For cardinals, no surveyed engine has infinite cardinal arithmetic, and every cardinal of the workloads is finite or $\aleph_0$. A finite cardinal is Sage's `cardinality()`. The cardinal is $\aleph_0$ when Sage gives `cardinality()` $= +\infty$ and puts the set in `EnumeratedSets`, its category of countable sets: ℤ, ℕ and $\{2n \mid n \in \mathbb{N}\}$ are there, which covers `sets.card.integers` (V1), `sets.card.naturals` and `comprehension.even_card` (probe in `research/milestones.md`). Sage does not put $\mathbb{Z}^2$ (as a module or as `cartesian_product([ZZ, ZZ])`) in `EnumeratedSets`, so no engine gives $\aleph_0$ for `lattices.card.a2` (K13) and the cardinalities $\aleph_0$ of `formed.card.hyperbolic_fixed` and `formed.card.hyperbolic_variable` (K14). For these three V2 statements (tasks T260 and T262), the cardinal implementation computes the arithmetic of finite cardinals and $\aleph_0$ (sums, products and finite powers, for example $|\mathbb{Z}^2| = \aleph_0 \cdot \aleph_0 = \aleph_0$) itself and cites Mathlib's cardinal arithmetic (`Mathlib.SetTheory.Cardinal.Arithmetic`) as its reference. No surveyed engine provides it, and it is known mathematics, so it is ordinary leaf work under the policy "Established computational implementations" (constitution 4.0.1). No statement needs an uncountable cardinal. The engine of each row is the recommendation of the survey for its families (`research/engine-survey.md`, "Recommendation summary"); `sage.schemes`, Sage crystals and the cusps of `sage.modular` are not in that survey, and their milestones add them to the survey record before the implementation.

**Rings.** `cat.rings` reaches `cat.monoids` by three structural routes at `443fba9`: directly, through semirings, and through its additive group read as a group. The registered cell `cell.rings.multiplicative_monoid.semiring` compares the first two. Along the third, `·` denotes the addition of the ring; T131 (lean-categories#193) makes `fun.additive_groups.to_groups` non-structural and puts one multiplication at magmas and one addition at additive magmas, with the richer rows as their restrictions. T132 (#194) gives the numerals of a ring as the numerals of its underlying semiring, and T122 (#186) the numeral of additive monoids. At `443fba9` a ring reaches groups. Of the 13 RX-03 statements, 3 have the latest home of their rows in groups (T215) and 10 in rings (T218). SC-015 (`2 * 3 = 6 in ℤ`) is the stated attainment of the Rings V1 task T218.

**Each category task** has the authorship, survey, engine-glue, migration and dependency rules and the shared check of the [category tasks](tasks.md#complete-the-required-computational-implementations-and-actual-delivery-tuple) of the task list (constitution C17, C22, C23 and the established-implementations policy).

## Implementation order and dependency correction

1. T114's current changed-source/public-consumer feedback under #84 is complete; preserve it during the remaining work. Commit the inherited worktree by mechanism (T351), bring the first statement of `sets.cas` within the loop bound (T354), then complete its timing records, test-run logs and application logs (T112, T127; FR-043) and the truthful acceptance run (T300). Then retain adequate existing foundations and prepare the actual source/public driver interfaces. Do not reopen checked setup to produce new receipts. A missing mathematical input becomes a lean-categories task before its consumer, and the workstream does it there ([execution order](tasks.md#execution-order)); downstream mathematics never fills it.
2. Implement T032 lowering and T013's concrete execution composition at their positions in the [task order](tasks.md#execution-order). Functional outputs needed by the executor are T017–T021/T026; source selection is T053–T056. These are parts of one functioning path, not preliminary standalone release projects.
3. Bind actual results and connect T038; remove transferred fallback paths. T041's real driver is prepared without T039 or broad mathematical coverage as a prerequisite. T027's shared outcome classification does not depend on completing suspension first.
4. Complete every required generic mechanism and protocol behaviour, so that every DSL script runs through the public session (F). No per-construct export freeze, preservation proof or early contributor trial gates this expansion. Full kernel readiness, not a first scalar or first RX-LIFT, enables substantial leaf work.
5. Separately situated leaf authors deliver the category implementations in the order of the [computational milestones](#computational-milestones), as established-engine glue against the actually built released contract; integration publishes T105's compatible tuple, on the port of T352 (#90). The functional work of M4, the notebook unit and the functional work of M5 follow, in the order of the [completion milestones](#completion-milestones).
6. Complete independent assessment, source-to-machine/correctness arguments, original fixed and frozen-extension observations and the final performance phase on that delivered tuple. Relevant corrections republish the tuple and reexecute affected obligations without weakening them.

## Validation and retained final obligations

Functional checks ask whether the actual public responsibility path exists and performs the claimed operation. If the same test could pass with the lowerer or concrete executor deleted because its fixture supplies that function, it is not a check of that story. Test-only providers may check protocol failure mechanics, but are not mathematical execution. Existing independent mathematical assertions remain the authority for their answers; no new easier specimen replaces them.

During functional work use the actual source, role and runtime checks needed to implement behavior, with sufficient resources. Do not select work from reading counts, repeated frozen exports, green internal audits or benchmark failures. Self-consistency-only evidence and general proof completion come after required functionality under C21. A red expensive aggregate does not prohibit implementation of other required functions.

The final denominator is that of the specification (SC-001 to SC-004) and the [fixed inputs](quickstart.md#fixed-inputs-of-the-final-assessments) of the validation guide; full B0 K1–K14, all 26 K13 IDs and broad Sage parity remain separately assigned by #19.

Final performance retains the original 99-root 3×3 specimen, strict under-60-second total on the measured host and phase accounting, and full RX-LIFT with 22 prerequisites and the shared 200,000-heartbeat preparation/evaluation limit. Earlier higher-limit functional runs do not discharge those final budgets. Neither changing a required question nor calling a timeout an expected negative satisfies them.

Proof obligations retain their original quantifiers: semantic safety under arbitrary provider behavior; conditional preservation/progress under independently fixed primitive relations and stated operational hypotheses; actual complete execution/independent assessment of the designated delivery. Generic library laws, structural validation and arbitrary provider correctness are not interchangeable. Independently frozen trials keep contributor choice, permitted inputs, zero accommodation and affected repair/refreeze/rerun requirements, but no longer block implementing required kernel capabilities.

## Source organization recorded at `e24045ca`

This section records how the source on branch `integration/kernel-v1-20261106` is organized and which engineering choices it makes. Read the source before you rely on a statement here.

### Production path

Source text runs through `SourceSession.readStatement` (`CasCompiler/ReadSession.lean`, `ReadExpression.lean`; `Read.lean` retains the term-notation facade and public exports) → `CasCompiler.lowerTerm` (`Lower.lean`) → `CasRuntime.Kernel.execute` → the framed provider connection → a retained binding. `#cas` and `#cas_tests` call it through `CasRuntime.KernelSession` (`CasRuntime/Session.lean`). The reader produces native Lean terms whose meaning comes from lean-categories registry rows; it computes nothing. Computation is dispatched to leaves, and without leaves a computational statement ends in `NoImplementation`.

### Source facts at `7661292` (the source tree of `fc7fdf8`)

- **Selected data in the reader.** The judgement and the binding of a limit (`NativeSourceLimitSelection`, `SourceLimitSelection`, `CasCompiler/Elaborate.lean:52-88`) hold its row, cone, presentation, diagram and interface with `standardization` and `dataConstructor`; `sourceLimitLeg?` takes the leg from the retained cone. A named map states its ends as projections of its own arrow; `declaredEndpoint` (`CasCompiler/SelectedMorphism.lean`) gives the declared end, and each reader rule that inspects the source or target of a map uses it.
- **Statements.** `SourceStatement.settled` holds every settled typing judgement of an assertion. `X ⊆ Y` for named sets is such a judgement, settled by `sourceCoercion?`.
- **Outcomes.** The reader tags an unknown name (`unknownSourceNameTag`); the session keeps the definitions that did not read (`KernelSession.unread`) and reports a use of one as that definition's outcome. The dependency check tags a missing runtime value with its binding (`missingValueTag`).
- **Trial readings.** A trial reading propagates every exception and drops only an explicit applicability error; "not applicable" is a typed result of the trial.
- **Aggregate.** `CasCatalogue.lean` imports none of `Language`, `Realize`, `Codec`, `Admission` directly; `Admission`, `Codec`, `EquationData` and `Resolve` are in its closure through `CasRuntime.Session` (removal steps 4 and 6 of the task list).
- **Feedback.** `just loop`, `just slow`, `just milestone`, `just stop` (`scripts/feedback.sh`); run records in `timing/`; the acceptance report of a file holds the milliseconds of each statement.

### Dependency boundaries

Checked computation declarations and `ProgramBoundary` belong to `CasCompiler/Program.lean`. Runtime operand binding, request and response admission, and the operational signature belong to `CasRuntime/PreparedRequest.lean`. Source-only program work imports the former; lowering and execution consume the latter.

`CasCompiler/SourceRoutes.lean` owns first-binding route formation and retains its immutable source inventory. `OperationFamily.lean` owns whole-family preparation; `FamilyConversion.lean` owns native family agreement. `SourceCarrier` imports route formation directly. The numeral, method and operation readers import their required family operations explicitly. Cell comparison and coherence remain in `Resolve.lean`.

`CasRuntime/Realization.lean` selects from the admitted manifest and frozen profile. `Encode.lean` prepares dependent invocation packets. `Kernel.lean` consumes both. Connection and transport modules remain independent of source-language reading.

The expression reader now assembles typed rule modules, and runtime manifest/connection/invocation/demand responsibilities have separate owners with `Kernel.lean` as assembly. These source cuts must remain while their consumers are corrected; moving a responsibility is not proof that its mathematical preparation has been repaired. These boundaries must preserve the original source-to-result computations, including constructed values consumed through their target-category interface. Focused checks establish only the behaviour they exercise; independent mathematical acceptance remains separate.

### Engineering decisions

Each is a delegated engineering choice (constitution C17), except the kernel-side decisions of equality in rows 3 and 7. Those two contravene C22, and T113 and T312 replace them. Choices that change what a leaf sees must be published by T028.

1. **Arguments of a published operation** are the dependent invocation context of execution contract §4.1 (`kind`, `prepared_role`, `parameters`, `bindings`, `arguments`, `argument_layouts`, `result_layout`). A registered named constant is a descriptor `{"ctor": <catalogue id>, "args": [...]}`.
2. **Operation address**: the family id, with `#<field>` when the reached field is not the first computational field.
3. **Named elements**: a generator is the descriptor `<object id>#generator`, a subset literal the descriptor of its `SubsetLiteralEntry` id whose finite set is the array of its elements (each element a retained slot), an admitted element the data of the value it admits under its own role (an element of a subtype is the record whose one field is that value), a numeral the descriptor of its `NumeralEntry` id (`{"ctor": "num.rings", "args": [<ring>, k]}`), each at its explicit parameters. A comparison with a numeral decides the closed equality in Lean. This contravenes C22: no procedure registered in lean-categories takes part. T113 and T312 replace it.
4. **Delayed families** are closures; realization is selected when an action reaches actual arguments.
5. **Input forms**: the complete-request form `<id>#input`, plus the exact form of each argument that is a registered named object.
6. **Retention**: a definition keeps a runtime value when its evaluation dispatched to a provider or its value holds a closure of a published family or provider-owned data (a delayed lift); other definitions, including lambdas and matrix literals the user wrote, are read from their definition.
7. **Questions**: a question about a retained value compares returned packets; a closed question is discharged in Lean through the registered literal evaluations (`CasCatalogue/Evaluation.lean`). `x ∈ Y` and `x in Y` for an object `Y` are settled by reading `x` in `Y`. This choice contravenes C22 where the session decides the equality of returned values itself; tasks T113 and T312 replace it.
8. **Evaluation algebra**: `p(a)` for `a` in the coefficient ring uses `Under.mk (𝟙 R)` (lean-categories `Polynomials.evaluation_own`); otherwise the unique registered `R`-algebra on the argument's set.

## Artifact and source map

The feature directory holds the artifacts: [specification][S1]/[requirements][S2], this plan, [research](research.md), [data model][D], [mathematical input][M], [runtime][R], [notebook][N], [validation][Q], and [tasks Part 1][T1]/[Part 2][T2]. The [requirements-quality checklist][CHK] (`checklists/architecture.md`) remains reviewer-owned; this plan edit does not approve its markers.

Production locations remain `CasCompiler/{Context,Elaborate,Read,Resolve,Program,Lower}.lean`, `CasRuntime/{Value,Owner,Occurrence,Transaction,Execute,Realization,Inspect}.lean`, actual `CasDsl`/`CasCatalogue` public entrances, the released contract/SDK and the actual notebook worker/client. The proof tasks add `CasCompiler/Correctness.lean` and `CasRuntime/Correctness.lean`, which are absent at `7661292`. Task locations are implementation responsibility, not an obligation to preserve redundant helpers or match historical file organization.

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
