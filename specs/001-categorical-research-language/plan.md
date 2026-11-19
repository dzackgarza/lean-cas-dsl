# Implementation Plan: Categorical research language

**Feature:** `001-categorical-research-language` · **Replanned:** 2026-11-09 (Asia/Taipei).

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
| Language/runtime | Lean 4.33.0, ordinary checked Lean term formation, source-derived dependent programs, actual runtime value/owner/transaction state. Python supplies the released SDK and notebook client, not a second mathematical interpreter. |
| Mathematical authority | Independently accepted lean-categories declarations, actual structural/constructor actions, complete operation families and abstract computation interfaces. Kernel/leaf authors do not commission subject mathematics shaped to their implementation. |
| Operational substrate | Reuse CSLib `PFunctor.FreeM` at `3951377e5a3f5772737f11cd62bc5bb6a72f95d1` and PolyFun stateful handlers at `a5895e454254a400774fa396b64d5b968f0933df`, with compatible Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. These libraries provide sequencing, not a CAS lowerer or concrete executor. |
| Dependency policy | Actual compatible own-organization latest-main inputs at delivery; record exact diagnostic tuples without making every upstream change a new implementation phase. Do not change locks merely to revise this plan. |
| Existing work | Reuse adequate context/source intake, value/owner/transaction/scope machinery and structural route closure. The handoff explicitly says not to rebuild T005, T006, T008–T011, T018 or the existing T053/T054 closure merely to obtain fresh internal evidence. Inspect actual current source before relying on a historical completion statement. |
| Storage | Immutable committed Environment-backed program/value/observation data; active-transaction staging; nonrollbackable live owner/reservation/transport-ID metadata. No second completed-payload store. |
| External boundary | Data-only versioned framing, exact dependent roles and scoped references, existing engines, retained callable ownership, no automatic retry/replay or provider-priority fallback. All advertised deferred/suspended behavior needs a real kernel handler. |
| Platform | Existing authorized execution environment and actual CAS/notebook surface. No owner-machine access, new persistent environment or alternate frontend is a planning prerequisite. |
| Legacy bridge | T024/T025 are retired by the current owner order. Do not revive v1 bridge work as a prerequisite. Existing retained implementations move to v2 through their separate public-only owners after kernel readiness, under T104. Their original mathematics and acceptance questions remain unchanged. |
| Budget phase | C21 governs: functional work may use the time/memory/heartbeat limits needed. Original budgets remain final obligations, including the 99-root 3×3 specimen under 60 seconds and RX-LIFT's shared 200,000 heartbeats/full 22-binding prefix. Optimization cannot select work during the functional phase except the narrow C21 cannot-finish-at-all exception. |

The scoped contracts remain [mathematical input][M], [computational runtime][R], [data model][D] and [notebook session][N]. Their behavioral requirements remain binding. The schedule in this plan and tasks implements the current C21 order; it does not reintroduce their historical first-use-proof, early-freeze, v1-bridge or budget gates. Exact changes of responsibility and proof ownership are specified below, not left to an implementer to reconcile contradictory task dependencies.

## Constitution check and repaired planning defects

The former plan failed to make its first story independently functional: it put the protocol story before the lowerer and public entrance that its own test required. It also placed integrated drivers behind proofs and broad support tasks, and treated requirement tags and an acyclic graph as evidence of adequate functional sequencing. Those are rejected planning assumptions, not waivers for implementation.

The corrected design has these consequences:

- C0–C4: every story reaches actual public behavior through the same source-derived lowerer/executor; no test-provided request or executor supplies the production capability being claimed.
- C5–C8: actual selected routes, cells, allowed choices and defining maps survive compilation, execution and later use. Native well-typedness does not erase additional source-required coherent data.
- C6: enumeration of first bindings is distinct from proving agreement. Complete-family definitional agreement or independently formalized comparison can establish agreement; a declared preferred route selects an admitted reading without asserting agreement. Without the required resolution data, ambiguity is reported before execution. No shortest route, backend success or unregistered theorem search substitutes.
- C9–C13: mathematical authorship, candidate computation and independent acceptance remain distinct; original observations, extension trials and exact lifetime/publication rules remain due.
- C16–C20: preserve existing useful implementation, remove transferred reconstruction paths and inspect the actual public responsibility path. Documentation edits do not claim implementation or independent approval.
- C21: kernel functionality comes before substantial leaf work, self-consistency-only evidence, frozen trials, preservation/correctness proofs and performance work. Actual type/domain/data/owner checks needed to perform a function remain part of that function; postponing proof documentation does not permit an unsound runtime shortcut.

No constitutional amendment or reduced product is proposed. The current constitution was inspected at integration `fba37ec6973bcbad4acce4cab12bef9738cc0532` (constitution blob `e690013ecf4d77e746d20d4379dc47fcb04813cc`). That is input provenance, not evidence of present source functionality.

## November 17 source-to-result correction

The [current handoff](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6726232237) and functional tasks supersede older reader-first sequencing. Repair the complete selected source construction and its actual continuation: retain exact occurrences/endpoints and universal data, prepare generic dependencies, use the common source boundary for provider requests, construct genuine public target objects/arrows, apply formal classifier refinements and complete generic operation growth. Delete each transferred recovery path in the same implementation change. Retain already adequate source/runtime/rule separation; do not reimplement it for another receipt.

The explicit focused-command, production/test target and SDK-provisioning corrections support those functional changes. Tests stay outside the production target; provisioning stays outside Lean elaboration; a focused build streams once without a profiling gate. Functional source/provider consumers remain the endpoint of that loop. #84's measurements and optimization remain after functionality.

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

T013 owns the production interpreter/dispatcher that supplies the previously missing executor. It must bind a prepared primitive request to the selected live `FramedConnection.invoke`, admit the response at its fixed dependent role, retain it in the active transaction and continue the operational program. A generic handler taking an application-supplied executor is not completion of this task.

T019 provides projection and application of actual stored fields, compiled closures and native callable values. T020 provides actual owner-bound export invocation, including complete published/dependent context and fresh invocation-local capture frames. T021 validates complete replies/exports/captures and request-local disposal. T026 supplies actual exact-demand construction and realization selection, not merely profile parsing or a fixed-point calculation over a graph manufactured by a test. These functions are composed by T013; none is approved by supplying its missing production operation in a test callback.

Selection of a realization occurs after the mathematical question is fixed. Zero eligible realizations is the specified computational gap, one selects the actual call and multiple remain computational ambiguity. Retain exact primitive/generic/fused identities. Fixed finite demands use the declared grounded analysis; result-dependent demands remain closures until their actual arguments exist. No test-only closure, absent-as-unknown conversion or retry-until-success path supplies the result.

T022/T023 complete deferred requests and adaptive suspension in the same executor, using actual children, scoped captures, released permits, one-resume tokens and exact backward result associations. They depend on the working invocation path; they are not prerequisites to authoring the lowerer or connecting the immediate public path. The story and final kernel are not complete while an advertised generic protocol feature is missing.

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

US2–US6 use the shared production path developed with US1; this dependency is explicit, not a claim that a protocol-only phase is independently executable. Their generic capabilities use that interface in the fixed task order; the interface does not authorize separate active tasks. US7/US8 are real integration, not mock frontends or post-delivery polish.

## Implementation order and dependency correction

1. Retain adequate existing foundations and prepare the actual source/public driver interfaces. Do not reopen checked setup to produce new receipts. Missing mandatory source/contract inputs are identified precisely, not filled by downstream mathematics.
2. Implement T032 lowering and T013's concrete execution composition at their positions in the [task order](tasks.md#execution-order). Functional outputs needed by the executor are T017–T021/T026; source selection is T053–T056. These are parts of one functioning path, not preliminary standalone release projects.
3. Bind actual results and connect T038; remove transferred fallback paths. T041's real driver is prepared without T039 or broad mathematical coverage as a prerequisite. T027's shared outcome classification does not depend on completing suspension first.
4. Complete every required generic mechanism, protocol behavior, notebook and discovery/display function. No per-construct export freeze, preservation proof or early contributor trial gates this expansion. Full kernel readiness, not a first scalar or first RX-LIFT, enables substantial leaf work.
5. Separately situated leaf authors migrate retained implementations and supply remaining required established-engine glue using the actually built released contract. No kernel-informed formalization assignment is bundled into their work.
6. Complete independent assessment, source-to-machine/correctness arguments, original fixed and frozen-extension observations, coherent delivery and the final performance phase. Relevant corrections reexecute affected obligations on the new tuple without weakening them.

The former edges T041←T039, T030←T029, T038←the complete deferred/suspension chain, expansion←T079, and functional construction←self-consistency-only proof/audit tasks are removed in the actual task entries. Proof responsibilities formerly mixed into functional T016/T043/T044/T046/T053–T056/T061 are assigned to T014/T039/T052/T062/T070/T076/T096 as appropriate. Nothing is declared proved by that reassignment. Required source-law validation in an actual invocation remains functional and cannot be omitted.

## Validation and retained final obligations

Functional checks ask whether the actual public responsibility path exists and performs the claimed operation. If the same test could pass with the lowerer or concrete executor deleted because its fixture supplies that function, it is not a check of that story. Test-only providers may check protocol failure mechanics, but are not mathematical execution. Existing independent mathematical assertions remain the authority for their answers; no new easier specimen replaces them.

During functional work use the actual source, role and runtime checks needed to implement behavior, with sufficient resources. Do not select work from reading counts, repeated frozen exports, green internal audits or benchmark failures. Self-consistency-only evidence and general proof completion come after required functionality under C21. A red expensive aggregate does not prohibit implementation of other required functions.

The final denominator is unchanged: all 153 permanent readings; 134 positive extension questions in 14 files (105 original plus 29 completion); protected negative/environment controls; RX01–RX10 and complete RX-LIFT; at least four real-engine workflows across three areas with all 17 original connected assertions; all prescribed independent extensions and mechanism arguments. Full B0 K1–K14, all 26 K13 IDs and broad Sage parity remain separately assigned by #19.

Final performance retains the original 99-root 3×3 specimen, strict under-60-second total on the measured host and phase accounting, and full RX-LIFT with 22 prerequisites and the shared 200,000-heartbeat preparation/evaluation limit. Earlier higher-limit functional runs do not discharge those final budgets. Neither changing a required question nor calling a timeout an expected negative satisfies them.

Proof obligations retain their original quantifiers: semantic safety under arbitrary provider behavior; conditional preservation/progress under independently fixed primitive relations and stated operational hypotheses; actual complete execution/independent assessment of the designated delivery. Generic library laws, structural validation and arbitrary provider correctness are not interchangeable. Independently frozen trials keep contributor choice, permitted inputs, zero accommodation and affected repair/refreeze/rerun requirements, but no longer block implementing required kernel capabilities.

## Artifact and source map

The feature directory holds the artifacts: [specification][S1]/[requirements][S2], this plan, [research][F], [data model][D], [mathematical input][M], [runtime][R], [notebook][N], [validation][Q], and [tasks Part 1][T1]/[Part 2][T2]. The original [requirements checklist][CHK] remains reviewer-owned; this plan edit does not approve its markers.

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
[focused commands](../../CONTRIBUTING.md#focused-development) apply to that same implementation.
They specify boundaries for source preparation, actual request binding, generic execution and final assembly;
they do not authorize preserving reconstruction machinery behind those interfaces.
