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
| Language/runtime | Lean 4.33.0, ordinary checked Lean term formation, source-derived dependent programs, actual runtime value/owner/transaction state. Python supplies the released SDK and notebook client, not a second mathematical interpreter. |
| Mathematical authority | Independently accepted lean-categories declarations, actual structural/constructor actions, complete operation families and abstract computation interfaces. Kernel/leaf authors do not commission subject mathematics shaped to their implementation. |
| Operational substrate | Reuse CSLib `PFunctor.FreeM` at `3951377e5a3f5772737f11cd62bc5bb6a72f95d1` and PolyFun stateful handlers at `a5895e454254a400774fa396b64d5b968f0933df`, with compatible Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. These libraries provide sequencing, not a CAS lowerer or concrete executor. |
| Dependency policy | Actual compatible own-organization latest-main inputs at delivery; record exact diagnostic tuples without making every upstream change a new implementation phase. Do not change locks merely to revise this plan. |
| Existing work | Reuse adequate context/source intake, value/owner/transaction/scope machinery and structural route closure. The handoff explicitly says not to rebuild T005, T006, T008–T011, T018 or the existing T053/T054 closure merely to obtain fresh internal evidence. Inspect actual current source before relying on a historical completion statement. |
| Storage | Immutable committed Environment-backed program/value/observation data; active-transaction staging; nonrollbackable live owner/reservation/transport-ID metadata. No second completed-payload store. |
| External boundary | Data-only versioned framing, exact dependent roles and scoped references, existing engines, retained callable ownership, no automatic retry/replay or provider-priority fallback. All advertised deferred/suspended behavior needs a real kernel handler. |
| Platform | Existing authorized execution environment and actual CAS/notebook surface. No owner-machine access, new persistent environment or alternate frontend is a planning prerequisite. |
| Legacy bridge | T024/T025 are retired by the current owner order. Do not revive v1 bridge work as a prerequisite. Existing retained implementations move to v2 through their separate public-only owners after kernel readiness, under T104. Their original mathematics and acceptance questions remain unchanged. |
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
- C21: current fast development feedback comes first and remains active. Complete kernel functionality comes before substantial leaf work, self-consistency-only evidence, frozen trials, preservation/correctness proofs and final mathematical/runtime performance work. Actual type/domain/data/owner checks needed to perform a function remain part of that function; postponing proof documentation does not permit an unsound runtime shortcut.

The governing constitution is [v3.1.0](../../.specify/memory/constitution.md), amended on
2026-11-22 under the owner's direction to enshrine durable principles from both comparative
analyses. C0/C9/C21/C23/C24 now state source-derived complete category interfaces, separate
dependency relations, real locality, continuing feedback and full choice-sensitive assessment.
This compatible elaboration changes no original mathematical question, authority boundary or
final budget. Earlier constitution hashes remain historical input provenance.

Version 4.0.0 of 2026-11-25 records the [owner instructions of that date](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-7155201731).
A missing mathematical declaration is a task of lean-categories that the workstream does there (C21).
Kernel work is accepted on kernel behaviour and requires no computed mathematical result (C22).
Computational work has its own milestones, in the order of the structural scaffolding (C23).

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

## Completion milestones

These are complete delivery outcomes, not file/module counts or a second task queue.
[Tasks](tasks.md#execution-order) retain stable IDs, definitions and execution order.
[GitHub #10](https://github.com/dzackgarza/lean-cas-dsl/issues/10) owns the roadmap and evidence;
native milestones record each issue's full closure stage. A broad owner issue can contribute
functional work earlier while retaining its later proof and acceptance obligations.

| Milestone | Complete observable outcome | Owners and scope |
| --- | --- | --- |
| [M0 — Fast edit-to-result feedback](https://github.com/dzackgarza/lean-cas-dsl/milestone/1) | A substantive edit in the current owner rebuilds affected executable dependencies and runs the unchanged public consumer within the normal focused-loop bound. Current diagnostics, failures and timings are truthful. Retain this behavior throughout development. | #84, T114/US9; reuse T016's completed work without treating its historical timing as current readiness. |
| [M1 — Complete generic categorical kernel](https://github.com/dzackgarza/lean-cas-dsl/milestone/2) | F: all Part 1 functionality works through real public entrances, including complete constructions and later use, both functor actions, selected lifting/refinement/comparisons, higher/infinite interfaces, protocol, notebook/lifetime, discovery/display and both directions of growth. Its checks observe kernel behaviour and require no computed mathematical result (constitution C22). It has [checkpoints](#m1-checkpoints). | #92; #66/#69 and #82/#85/#91 supply their functional responsibilities; #86 closes here. The first complete construction is an internal step, not this milestone. |
| [M2 — V1 category implementations and delivery](https://github.com/dzackgarza/lean-cas-dsl/milestone/3) | The [computational milestones](#computational-milestones) deliver the category implementations in mathematical order. All required V1 category implementations supply actual computations, defining data and later uses through the released contract; publish and build one compatible mathematics/kernel/contract/leaf/notebook tuple. | #93, T104/T105; #90 supplies the research-image toolchain/Mathlib port. |
| [M3 — Independently accepted V1](https://github.com/dzackgarza/lean-cas-dsl/milestone/4) | All #24 A–F obligations, independent mathematical assessment, preservation arguments, frozen extension trials and original final budgets hold together on the delivered tuple. | #24 and full closure of #66/#69/#82/#85/#91; #97 records #10's unchanged V1 closure condition; the project root remains open through M4/M5. |
| [M4 — Full B0 and classified Sage coverage](https://github.com/dzackgarza/lean-cas-dsl/milestone/5) | Complete #19's K1–K14 computations and the separate versioned Sage coverage denominator, including required hypotheses, defining maps and continuations. | #19, #20, #21, #22, #23. Their bounded construction/input work can inform V1 before their later full closure. |
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

M1 closes on F. Before F, these checkpoints close one at a time, in this order. A checkpoint is one observation of kernel behaviour through the public session `CasRuntime.KernelSession`, on the original source inputs of its story, with a protocol peer or an empty manifest (constitution C22). It closes when the observation holds on the kernel branch. It claims only itself: it checks no task box, and the independent assessment of the same inputs stays in Part 2. The tasks keep their order and their complete definitions. Issue #92 holds the checklist of the checkpoints.

| Checkpoint | Observation | Reached after |
| --- | --- | --- |
| M1.1 — Typed carriers | No kernel source reads an occurrence or a selection from term metadata. Every test module that passed before the change passes after it (T116, T117). | T117 |
| M1.2 — Connected statement path | A source file runs through one session. Each statement is read, lowered and dispatched to a protocol peer at its registered address with its actual operands. The reply is admitted and retained, and a later statement uses that value with no second dispatch. | T038 |
| M1.3 — Public forms of connected calculation (US1) | Every statement of the permanent acceptance files reads to its registered meaning. With an empty manifest, each computational statement ends in no implementation at a registered address. No statement ends in an internal error or a reader gap. | T050 |
| M1.4 — Complete construction and later use (US2) | The original RX-LIFT source with its 22 bindings prepares each lift field, comparison and factor request at the selected lift, with the earlier outputs as operands. The returned object, maps and factor are the operands of the later requests. Two selected limits with one apex keep their own cones. | T049 |
| M1.5 — Selected structures (US3) | The inputs of RX05, RX06 and RX07 select their routes, cells, classifiers and reindexing before dispatch. A required omission is refused with no dispatch. A declared choice-producing operation binds the member that the peer returns (T115). | T061, T115 |
| M1.6 — Exact, infinite and qualified requests (US4) | The RX09 inputs prepare requests that keep the exact source, the tolerance and the full index family. A demand outside an earlier finite display reaches the same retained object. | T069 |
| M1.7 — Growth (US5) | A new accepted declaration reaches an unchanged consumer, and a new generic operation reaches an existing object, with no kernel edit. | T075 |
| M1.8 — Computational contract (US6) | A peer written from the published contract alone uses deferred and suspended service, and an unchanged consumer receives its output. The published interface of T028 matches the built kernel. | T028 |
| M1.9 — Notebook (US7) | The cells of `notebooks/kernel-v1.ipynb` run through the worker and one session: values retained across cells, inert queries, cancellation and owner rules. | T093 |
| M1.10 — Discovery and display (US8); old path removed | Discovery and inspection read retained data and execute nothing. No public entrance reaches `CasCatalogue/Language.lean` or `CasCatalogue/Realize.lean`. With every Part 1 box checked, this is F. | T101, T051, T064 |

### Computational milestones

Computational work is leaf work (constitution C22, C23). It has its own milestones, separate from M1, and its own task lists, written when each milestone starts. T104 and M2 own it. M2 closes when the milestones that V1 requires hold on one published tuple (T105).

**Order.** The implementation of a category follows the implementations of the categories that its structural functors and classifier forgets reach. The layers below are computed from the published catalogue of the contract package (`api/declared-ports.json`, mathematics revision `3f8aedf`): its structural functors and its classifier forgets, by the longest chain down to `cat.sets`. Compute them again from lean-categories `main` when a milestone starts.

| Layer | Categories |
| --- | --- |
| 0 | sets |
| 1 | magmas (sets with a binary operation), partial orders, additive monoids, finite sets, countable sets, enumerated sets, pointed sets, Boolean algebras |
| 2 | semigroups, linear orders, additive commutative monoids |
| 3 | monoids |
| 4 | groups, commutative monoids, semirings |
| 5 | additive groups |
| 6 | rings |
| 7 | commutative rings, division rings, modules over a ring |
| 8 and above | fields, algebras, bilinear and quadratic modules, lattices |

| Milestone | Category implementations | Attainment: holds as a computed result |
| --- | --- | --- |
| Leaves 0.1 — Sets | sets | Stated when the milestone starts, from the original workloads. |
| Leaves 0.2 — Algebra to rings | magmas, semigroups, monoids, semirings, additive monoids, additive commutative monoids, additive groups, rings: as much of each as the attainment needs | `2 * 3 = 6 in ℤ`. ℤ is read as a ring. Its multiplication is reached through a selected monoid structure of that ring (`rings → monoids → semigroups → magmas → sets`). Its numerals are images under the universal map. Its equality is a computed predicate. |
| Leaves 0.3 — Order structures | partial orders, linear orders | Stated when the milestone starts. |
| Later milestones | each further layer, in order | One stated result each, from the original workloads. |

Leaves 0.2 and 0.3 do not depend on each other. Each milestone is vertical: it implements enough of each category on its route for the attainment to hold, through the public interface of that category (constructors, operations, immediate functor actions).

**Questions for lean-categories that this reading raises.** Each becomes a lean-categories task under the rule of the [execution order](tasks.md#execution-order), after confirmation against `main`:

- Multiplication is registered three times: `op.monoids.mul`, `op.semirings.mul` and `op.rings.mul`. No multiplication is registered at magmas. A multiplication that rings own does not come from a monoid structure.
- `cat.rings` reaches `cat.monoids` by two structural routes (directly, and through semirings). The routes need an accepted comparison or a declared preference (constitution C6).
- `cat.partially_ordered_sets` and `cat.totally_ordered_sets` have no structural functor, beside `cat.partial_orders` and `cat.linear_orders`. No category of semilattices is registered.

**Each implementation** (constitution C23 and the established-implementations policy):

1. Survey the engines and libraries that can supply the operations of the category. The survey is open-ended. Candidates include Sage and passagemath, SymPy, Julia packages, GAP, Macaulay2 and Lean libraries.
2. Connect the chosen engine. Write no algorithm.
3. Move existing computation into the category implementation: the registrations of `lean-cas-dsl-leaves` (115 registrations in 11 backends at `49bdfcb`), and each kernel-side evaluation under "Kernel computation (C22)" in the task list.

The constitution's production-leaf sequencing policy places substantial leaf work after kernel readiness.

### Issue tree and task order

The native root is [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10), which stays open
through every retained phase. V1 completion is recorded by M3/#97 under the unchanged
#66/#69/#24 condition; it does not close the project root while M4/M5 remain.

| Direct-root milestone ledger | Ordered complete work owners |
| --- | --- |
| [#94 — M0](https://github.com/dzackgarza/lean-cas-dsl/issues/94) | #84 / T114 |
| [#95 — M1](https://github.com/dzackgarza/lean-cas-dsl/issues/95) | #92 / F, with the M1 checkpoint checklist in #92; #86 at T030 within F |
| [#96 — M2](https://github.com/dzackgarza/lean-cas-dsl/issues/96) | #93 / T104 through the computational milestones, then T105; #90 within T105 |
| [#97 — M3](https://github.com/dzackgarza/lean-cas-dsl/issues/97) | #24; full remaining obligations of #66, #69, #82, #85, #91 |
| [#19 — M4](https://github.com/dzackgarza/lean-cas-dsl/issues/19) | #22 / full B0 and classified Sage delivery; #20, #21, #23 supply full-parity inputs |
| [#98 — M5](https://github.com/dzackgarza/lean-cas-dsl/issues/98) | #68, #34, #3, #8, #13 |

`itree next` selects the completion owner; the unchecked task order selects the current work
within its scope. #84/T114 comes first. Close #84 only on its complete current loop evidence;
later tasks inherit the continuing C21/C24 obligation. Its former full-#85 blocker is obsolete.
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

## Implementation order and dependency correction

1. Complete T114's current changed-source/public-consumer feedback under #84, preserving it during the remaining work. Then retain adequate existing foundations and prepare the actual source/public driver interfaces. Do not reopen checked setup to produce new receipts. Missing mandatory source/contract inputs are identified precisely, not filled by downstream mathematics.
2. Implement T032 lowering and T013's concrete execution composition at their positions in the [task order](tasks.md#execution-order). Functional outputs needed by the executor are T017–T021/T026; source selection is T053–T056. These are parts of one functioning path, not preliminary standalone release projects.
3. Bind actual results and connect T038; remove transferred fallback paths. T041's real driver is prepared without T039 or broad mathematical coverage as a prerequisite. T027's shared outcome classification does not depend on completing suspension first.
4. Complete every required generic mechanism, protocol behavior, notebook and discovery/display function. No per-construct export freeze, preservation proof or early contributor trial gates this expansion. Full kernel readiness, not a first scalar or first RX-LIFT, enables substantial leaf work.
5. Separately situated leaf authors migrate retained implementations and supply remaining required established-engine glue using the actually built released contract. Integration then publishes T105's compatible tuple, including #90. No kernel-informed formalization assignment is bundled into leaf work.
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

Each is a delegated engineering choice (constitution C17). Those that change what a leaf sees must be published by T028.

1. **Arguments of a published operation** are the dependent invocation context of execution contract §4.1 (`kind`, `prepared_role`, `parameters`, `bindings`, `arguments`, `argument_layouts`, `result_layout`). A registered named constant is a descriptor `{"ctor": <catalogue id>, "args": [...]}`.
2. **Operation address**: the family id, with `#<field>` when the reached field is not the first computational field.
3. **Named elements**: a generator is the descriptor `<object id>#generator`, a subset literal the descriptor of its `SubsetLiteralEntry` id whose finite set is the array of its elements (each element a retained slot), an admitted element the data of the value it admits under its own role (an element of a subtype is the record whose one field is that value), a numeral the descriptor of its `NumeralEntry` id (`{"ctor": "num.rings", "args": [<ring>, k]}`), each at its explicit parameters. A comparison with a numeral decides the closed equality in Lean.
4. **Delayed families** are closures; realization is selected when an action reaches actual arguments.
5. **Input forms**: the complete-request form `<id>#input`, plus the exact form of each argument that is a registered named object.
6. **Retention**: a definition keeps a runtime value when its evaluation dispatched to a provider or its value holds a closure of a published family or provider-owned data (a delayed lift); other definitions, including lambdas and matrix literals the user wrote, are read from their definition.
7. **Questions**: a question about a retained value compares returned packets; a closed question is discharged in Lean through the registered literal evaluations (`CasCatalogue/Evaluation.lean`). `x ∈ Y` and `x in Y` for an object `Y` are settled by reading `x` in `Y`. This choice contravenes C22 where the session decides the equality of returned values itself; task T113 replaces it.
8. **Evaluation algebra**: `p(a)` for `a` in the coefficient ring uses `Under.mk (𝟙 R)` (lean-categories `Polynomials.evaluation_own`); otherwise the unique registered `R`-algebra on the argument's set.

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
[feedback loops](../../CONTRIBUTING.md#feedback-loops) apply to that same implementation.
They specify boundaries for source preparation, actual request binding, generic execution and final assembly;
they do not authorize preserving reconstruction machinery behind those interfaces.
