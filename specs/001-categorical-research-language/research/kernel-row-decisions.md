# Kernel row decisions: items A to F

Snapshot. Source revisions and capture date are below. This file is a research record, not a maintained document.

## Revisions, method, limits

| Item | Value |
| --- | --- |
| Capture date | 2026-11-25 |
| Kernel branch | `integration/kernel-v1-20261106` |
| Branch tip at the start of the reading | `447469b` |
| Branch tip at the time of writing (`git rev-parse --short`) | `fc7fdf8` |
| Difference `447469b..fc7fdf8` | Documentation only: `tasks.md` (8 lines), `contracts/computational-runtime.md` (2 lines) |
| Last commit that changes source | `7661292`. `git diff --stat 7661292 fc7fdf8 -- '*.lean' lakefile.lean '*.py' '*.sh' justfile` is empty |
| Governing documents | `main` at `45910a5`. They are identical on `main` and on the branch (`git diff --stat main <branch>` over `specs/001-…`, `.specify/memory`, `AGENTS.md`, `CONTRIBUTING.md` is empty) |
| Revision that the task rows state | `9165255` (2026-11-20), 111 commits before the tip |

All `file:line` references are to the committed content at `fc7fdf8`, read with `git show` and `git grep`. No working tree was read.

Method. No build and no test ran. "Reached" means: a module in the import closure of `CasDsl` or of `CasRuntime.Session`, other than a `*Tests.lean` module, names the declaration. The search is a text search by name over `*.lean`, `*.py`, `*.sh` and `justfile`. It is not a Lean reference analysis. Import closures come from the import lines of every `.lean` file at the tip.

Result that applies to every item: the rows describe `9165255`. The source changed in the places of items A, B, C and E. Part of each open alternative is settled by the source alone.

---

## A. "Unreached code", row T088, T089, T092

### Evidence

| Declaration | Definition | Production references | Test references |
| --- | --- | --- | --- |
| `FramedConnection.cancel` | `CasRuntime/Transport.lean:142-146` | none | `CasRuntime/TransportTests.lean:132` |
| `FramedConnection.isBusy` | `CasRuntime/Connection.lean:90-91` | none | none |
| `FramedConnection.hasOutstanding` | `CasRuntime/Connection.lean:93-98` | none | `TransportTests.lean:129`, `:131`, `:215`, `:217` |
| `FramedConnection.cleanupFailures` | `CasRuntime/Connection.lean:275-280` | none | `CasRuntime/SDKTests.lean:65`, `TransportTests.lean:198` |
| `CellTransaction.emit` | `CasRuntime/Transaction.lean:470-474` | `CasCatalogue/NotebookSession.lean:50` | `CompletionTests.lean:151`, `TransactionTests.lean:144`, `:176`, `:229` |
| `CompletionWaiter.detach` | `CasRuntime/Transaction.lean:406-407` | none | `CompletionWaiterTests.lean:63` |

`FramedConnection.cancel`. Its body checks that the reservation belongs to the transaction and to the connection, then calls `transaction.abort`. T088 requires the behaviour (cooperative cancellation at one commit/cancel gate). The production declaration that performs it is `CellTransaction.abort` (`Transaction.lean:720-721`, through `CellTransaction.fail`, `:708-717`: it abandons claims, retires reservations, cancels each lease and resolves the waiter signals). Production calls `abort` at `CasCatalogue/NotebookSession.lean:67` (the `cancel` hook of the notebook cell), `CasRuntime/Session.lean:830` and `Transaction.lean:742`. The notebook contract cancels an execute request, which is one cell transaction, not one reservation.

`FramedConnection.isBusy`. It reads whether the frame permit is held. Nothing reads it. T089 requires the report of a busy or draining connection. Production reports it from `FramedConnection.isDraining` (`Connection.lean:100-105`), read in `FramedConnection.before` (`Transport.lean:292-293`, `:301-302`, failure `busy_draining`), and from `CellTransaction.draining` (`Transaction.lean:734-737`), read at `NotebookSession.lean:70`.

`FramedConnection.hasOutstanding`. It reads whether a request of the connection has the status `sent` or `draining`. The four test references use it to wait until the frame is sent. Production reads the same statuses for one request in `RequestLease.draining` (`Connection.lean:217-225`) and for one cell in `CellTransaction.draining`. A sent lease is in the cell from `Transaction.lean:529-530`, so `CellTransaction.draining` gives the tests the same signal.

`FramedConnection.cleanupFailures`. It lists the requests whose cleanup failed (`discardFailed`). The record is written at `Connection.lean:181-183` (the `$cas.discard` exchange failed or its acknowledgement did not match) and at `:196-198`. No production declaration reads that record: `RequestLease.needsDrain` (`Connection.lean:217-221`) does not include `discardFailed`, so `CellTransaction.draining` does not count a lease whose cleanup the provider did not acknowledge. T089 requires the report of an unacknowledged drain. The cell hook that reports drain state is `NotebookSession.lean:67-70` (`cancel`, `force`, `draining`). The worker interface `Worker.Cell.Active` has the fields `prepare`, `commit`, `cancel`, `force`, `draining` and no field for this report (lean-jupyter-kernel at `fb03325`, the revision that `lake-manifest.json` of the branch pins, `worker/Worker/Cell.lean:62-67`; read with `git show` in a sibling checkout).

`CellTransaction.emit`. It appends an event to the active cell. Commit publishes the events as one `OutputBatch` (`Transaction.lean:775-776`). The notebook cell hook calls it for each output before commit (`NotebookSession.lean:50`). `CasCatalogue.lean:21` imports `NotebookSession`, and `CasDsl.lean:7` imports `CasCatalogue`. T092 requires this behaviour. `NotebookSession.lean` was added at `3a4736f` (2026-11-24), after the revision of the row.

`CompletionWaiter.detach`. It resolves the detach signal of one waiter; `CompletionWaiter.wait` then returns `detached` (`Transaction.lean:411-415`), and the executor maps that to `unavailable: waiter_detached` (`CasRuntime/Execute.lean:35`). T088 requires the behaviour. No other production declaration performs it. The only production holder of a waiter is `Execute.reuseResponse` (`Execute.lean:54-59`), which never detaches. Item F shows that no production consumer reaches that wait today.

### Decision

Decision: delete `FramedConnection.cancel`, `isBusy` and `hasOutstanding` (`CellTransaction.abort`, `FramedConnection.isDraining` and `CellTransaction.draining` perform their responsibilities); T089 connects `FramedConnection.cleanupFailures` to the drain report of the cell (`CellTransaction.draining`, read at `CasCatalogue/NotebookSession.lean:70`), because no production declaration reports an unacknowledged cleanup; T088 connects `CompletionWaiter.detach` for the consumer that waits in `Execute.reuseResponse` (`CasRuntime/Execute.lean:54-59`); `CellTransaction.emit` is reached from `CasCatalogue/NotebookSession.lean:50` (T092) and leaves this row.

### Governing passages

- T089 (`tasks.md:502`): "Retire the proper descendants/new leases, preserve prior owners/captures and report busy/unacknowledged drain without escalation or resend."
- T088 (`tasks.md:501`): "Distinguish detached waiters, queued/cooperative cancellation and already-committed outcomes".
- T092 (`tasks.md:505`): "Publish complete result/display/observation batches atomically through `Transaction.lean` and the worker at the final owner/cancel gate."
- Runtime contract, section 7: "A waiter may detach without cancelling others."

---

## B. "Unreached code", row T013

### What the production path uses

`CasRuntime.Kernel.execute` is `CasRuntime/Demand.lean:358-446`. It calls `Kernel.reach` (`Demand.lean:110-296`), which calls the `Kernel.invoke*` functions of `CasRuntime/Invocation.lean:53-273`. Each of them ends in `Kernel.invoke` (`Invocation.lean:25-48`).

| Responsibility | Production declaration | Call site |
| --- | --- | --- |
| Invoke a provider | `FramedConnection.invokeControlBefore` (`Transport.lean:307-311`) | `Invocation.lean:36-37` |
| Resume a suspended invocation | `FramedConnection.resumeControlBefore` (`Transport.lean:313-318`) | `Invocation.lean:310-311` |
| Encode the arguments of a published operation | `PreparedRequest.admitInputs`, `InputRoleMap.arguments`, then `ValueGraph.encodeInputs` (`Encode.lean:399-402`) | `Invocation.lean:59-69` |
| Encode the arguments of a retained export | the same two reads, then `ValueGraph.encodeExportInputs` (`Encode.lean:407-414`) | `Invocation.lean:262-267` |
| Form the invocation context | `dependentContext` (`Encode.lean:431-438`) | `Invocation.lean:79`, `:131`, `:273` |
| Bind input roles | `InputRoleMap.admit` (`RoleMap.lean:76-79`), read in source order by `InputRoleMap.arguments` (`:112-119`) and as a set by `InputRoleMap.references` (`:129-130`) | `PreparedRequest.lean:171-174`; `Transaction.lean:608` |
| Look up a result role | `ResultRoleMap.lookup` (`RoleMap.lean:183-193`) | `Transaction.lean:208` (`CompletionAssociation.select`) |
| Reuse a committed result | `CellTransaction.reuse` (`Transaction.lean:329-343`) | `Execute.lean:49` |

Both invocation functions run `FramedConnection.exchange` (`Transport.lean:153-267`) under the deadline wrapper `FramedConnection.before` (`:286-305`). They return an `InvocationReply`: immediate, deferred or suspended. The production path never reads an input by its role identity.

### Evidence for each declaration

| Declaration | Definition | Production references | Test references | Relation to the production path |
| --- | --- | --- | --- | --- |
| `FramedConnection.invoke` | `Transport.lean:332-335` | none | `TransportTests.lean:115`, `:126`, `:164`, `:212`, `:260` | Older, narrower version: `invokeControl` with no deadline, and `immediateOnly` refuses a deferred or suspended reply |
| `FramedConnection.invokeBefore` | `Transport.lean:337-341` | none | 24 call sites in 7 test modules | Older, narrower version of `invokeControlBefore`. `invokeBefore` is in `Transport.lean` from `c7621a2e` (2026-11-07); `invokeControlBefore` came with deferred groups at `8ed2a173` (2026-11-11) |
| `immediateOnly` | `Transport.lean:321-330` (private) | none | none | Helper of the two above |
| `PreparedRequest.encodeArguments` | `Encode.lean:450-467` | none | `ExportCaptureTests.lean:65`, `SDKTests.lean:131` | Duplicate of `Invocation.lean:262-267` (and of the argument part of `:59-69`) |
| `PreparedRequest.reference` | `PreparedRequest.lean:59-62` | `CasRuntime/Encode.lean:132` (`InputDescriptorView.namedMorphism?`, called at `CasCompiler/Lower.lean:1062`), `Encode.lean:164` (`InputDescriptorView.requireMorphism`, called at `CasRuntime/ChildCall.lean:90`) | `CasCompiler/OperationalTests.lean:28`, `:69`; `NativePointInvocationTests.lean:413`; `PropertyTests.lean:209`; `SelectedEndpointTests.lean:113` | Reached. The receiver at both sites is a `PreparedRequest` (`InputDescriptorView.family`, `Encode.lean:27`) |
| `PreparedRequest.universeArguments` | `PreparedRequest.lean:64-67` | `CasRuntime/Point.lean:122` | `CasCompiler/OperationalTests.lean:114` | Reached |
| `SessionSnapshot.reuse` | `Transaction.lean:214-218` | none | `CompletionTests.lean:167`, `:214`, `:221`; `InputResultTests.lean:75` | Duplicate of the first branch of `CellTransaction.reuse` (`Transaction.lean:334-335`): the same `CompletionAssociation.select` on the same receipt |
| `InputRoleMap.lookup` | `RoleMap.lean:106-109` | none | `CasCompiler/ApplicationArgumentTests.lean:113`, `:118`, `:231`, `:233`, `:239`, `:253`; `AdmissionInputTests.lean:351`; `SDKTests.lean:135` | Not a duplicate and not a missing mechanism: a read of one binding by role. Production does not need it |
| `KernelSession.value?` | `Session.lean:172-173` | `CasRuntime/Inspect.lean:384`, `:412` | 14 test modules | Reached. `Inspect.newBindings` is called at `CasCatalogue/TestSuite.lean:377`, `Inspect.prepare` at `NotebookSession.lean:44` |
| `RealizationProfile.id` | `Realization.lean:51` | `CasCatalogue/NotebookSession.lean:29` | `SessionLiftTests.lean:295` | Reached. The notebook contract requires it (`notebook-session.md:28`) |
| `RealizationProfile.normalized` | `Realization.lean:52` | none (the local value forms the hash at `Realization.lean:278-279`) | `RealizationProfileTests.lean:77`, `:81`, `:144`, `:196`, `:227`; `ObjectApplicationTests.lean:323`; `PresentationTests.lean:236` | Not a duplicate and not a missing mechanism: the frozen normalized document whose SHA-256 is `sha256` |

`CasRuntime/SDKTests.lean:120-150` shows why the first group matters. The test assembles the sequence of `Kernel.invokeExport` by hand: `reserveExport`, `encodeArguments`, `RequestScope.issue`, a hand-written `dependent` context, `invokeBefore`. The declarations `invoke`, `invokeBefore`, `encodeArguments` and `SessionSnapshot.reuse` are the steps of that second, test-assembled executor.

T013 names `FramedConnection.invoke` (`tasks.md:427`). At the tip that name is the immediate-only variant. The function that T013 describes is `FramedConnection.invokeControlBefore`.

`InputRoleMap.lookup`. The controls of `CasCompiler/ApplicationArgumentTests.lean` read the admitted map by role: a data role keeps its binding and its argument position, a proof role has no binding, two equal source terms keep distinct roles, and a role of another scope is refused. The task list keeps these controls ("Remainder of the T007 worktree", row T007, T009). The file at `337a6dc` has the same six calls.

### Decision

Decision: delete `FramedConnection.invoke`, `invokeBefore`, `immediateOnly`, `PreparedRequest.encodeArguments` and `SessionSnapshot.reuse`, and move their tests to `FramedConnection.invokeControlBefore`, `Kernel.invokeExport` and `CellTransaction.reuse`; `PreparedRequest.reference`, `PreparedRequest.universeArguments`, `KernelSession.value?` and `RealizationProfile.id` are reached (`CasRuntime/Encode.lean:132`, `CasRuntime/Point.lean:122`, `CasRuntime/Inspect.lean:384`, `CasCatalogue/NotebookSession.lean:29`) and leave this row; `InputRoleMap.lookup` stays as the read interface of the T007/T009 controls in `CasCompiler/ApplicationArgumentTests.lean`; T013 names `FramedConnection.invokeControlBefore`.

`RealizationProfile.normalized` is undetermined (see "Undetermined").

### Governing passages

- T013 (`tasks.md:427`): "Supplying an executor parameter from a test or leaving production primitive/application demands delegated to an unspecified callback does not complete this task."
- `tasks.md:47`: "No test may supply the production capability whose existence it claims to check."
- Runtime contract, section 3: "the **kernel must implement every advertised generic feature**" (an immediate-only invocation refuses `deferred/2` and `suspend-resume/2`).
- `tasks.md:290`: "Restate each test on the kernel branch with its assertions unchanged."

---

## C. Row T026, T032: the derivation plan

### Fact about the row

The row says that `SourceProgram.forTarget`, `withPrerequisites` and `PrerequisiteSlot` have no caller outside tests. At `fc7fdf8` this is not correct.

| Declaration | Definition | Production caller |
| --- | --- | --- |
| `SourceProgram.forTarget` | `CasCompiler/Program.lean:49-50` | `CasRuntime/Realization.lean:354` |
| `SourceProgram.withPrerequisites`, `PrerequisiteSlot` | `Program.lean:54-63`, `:29-32` | `SourceProgram.instantiate` (`Program.lean:68-74`) |
| `SourceProgram.instantiate` (added at `2bbfe32`, 2026-11-24) | `Program.lean:68-74` | `CasRuntime/Demand.lean:163`, `:205`, `:272`; `CasRuntime/RoutedMethod.lean:699` |
| `ProgramBoundary.target`, `ProgramBoundary.prerequisite` | `Program.lean:114-115` | none. Constructed only at `CasCompiler/OperationalTests.lean:24`, `:41`, `:49` |

### The compiler mechanism

- `SourceProgram.forTarget` consumes a published computation address (`ComputationRef`). It produces every checked derivation of that address (`CheckedComputationDerivation` of lean-categories: target, ordered prerequisites, template, plan, universe parameters, checked equality).
- `SourceProgram.withPrerequisites` consumes one derivation. It opens the prerequisite binders of the template as local variables. It produces one `PrerequisiteSlot` for each (ordinal, checked prerequisite with its address, declaration and family type, local variable) and the template body over those variables.
- `SourceProgram.instantiate` consumes one derivation and its universe arguments. It produces the template as a closed term in which each prerequisite variable is the registered family of that prerequisite. The address of the family travels as source-reference metadata (`selectedComputationFamily`, `Program.lean:36-43`). The lowerer decodes that metadata and prepares the prerequisite as an ordinary `ProgramBoundary.registered` request.
- `ProgramBoundary.target program` and `ProgramBoundary.prerequisite program index` are the typed boundaries of a derivation target and of its ordered slot (`reference`, `universeParams`, `familyIn` at `Program.lean:131-132`, `:138`, `:161-162`; observation at `CasRuntime/Observation.lean:89-91`). `PreparedRequest.forBoundary` accepts them. Production does not form them.

### The runtime mechanism

Selection: `RealizationProfile.select` (`Realization.lean:395-397`, through `selectBoundaries`, `:339-391`) builds the grounded realization graph from `SourceProgram.forTarget` and returns `Realization.derivation checked`.

Instantiation: four call sites take that derivation and build the application themselves.

| Call site | Boundary |
| --- | --- |
| `CasRuntime/Demand.lean:270-296` | A registered family or a record field |
| `CasRuntime/Demand.lean:160-186` | A categorical point (`.point`) |
| `CasRuntime/Demand.lean:202-208` | An object action (`.objectAction`) |
| `CasRuntime/RoutedMethod.lean:682-713` (`MaterializedMethodBoundary.derivation`) | A routed method |

Each site consumes the delayed family request: its formal parameter terms (`family.application`), its supplied runtime values (`family.origin.application`), the selected field path, and the argument terms and values of the action. Each site writes every runtime value back into its term (`markValue kernel.marks`, or `PreparedRequest.markedArguments`), applies the plan to the parameters (`betaRev`, `mkAppN`), projects the path (`projectTerm`) and applies the action arguments. Each site passes the resulting `Expr` to `evaluateSource` (the lowerer, `CasRuntime/Kernel.lean:15-52`) and completes the demand with `kernelCompletion`. The runtime thus builds the mathematical application of the derivation, and only the last step uses the lowerer.

### Decision

Decision: connect; the lowerer compiles the selected derivation: one compiler entry consumes the selected `SourceProgram`, its universe arguments, the typed operands of the family, the field path and the typed operands of the action, and forms the request `ProgramBoundary.target program` with one `ProgramBoundary.prerequisite program index` for each slot; `Kernel.reach` (`CasRuntime/Demand.lean:160-186`, `:202-208`, `:270-296`) and `MaterializedMethodBoundary.derivation` (`CasRuntime/RoutedMethod.lean:682-713`) keep selection, operand resolution, execution and completion, and their four term assemblies are deleted.

What the change requires:

1. Compiler. An exported entry in `CasCompiler` that forms the application of a selected derivation. It is the entry that the row T022, T023, T032 of the same table requires ("One compiler entry from a published address at typed operands to the selected application"). Production forms `ProgramBoundary.target` and `ProgramBoundary.prerequisite`.
2. Call sites to change. The four sites of the table above. Each passes its retained operands and runs the result.
3. Declarations to delete. The term assembly after `checked.instantiate` at each of the four sites. `selectedComputationFamily` (`Program.lean:36-43`) as the carrier of a prerequisite address (T117 deletes this term encoding). The search found no caller of `CategoricalPointFamily.realizedArrow` and `resultAt` (`CasCompiler/CategoricalPointFamily.lean:312`, `:336`) and of `SourceActionFamily.realized` (`:571`) other than these sites; they become internal to the compiler entry.
4. Not part of this row. `markValue` and `PreparedRequest.markedArguments` (`CasRuntime/ExecutionContext.lean:46`) have other callers; T116 owns them.

The signature of the compiler entry is not determined by the documents (plan: "Task locations are implementation responsibility").

### Governing passages

- Mathematical-input contract (`mathematical-input.md:27`): "The production lowerer compiles actual source statements and these computation templates into `OperationalProgram`." and "Prerequisites become parametric callables invoked at their actual reached arguments".
- Constitution C23: "Reusing only the final lowerer after independently rebuilding the selected application is insufficient."

---

## D. Row "Keep or move out of `CasCatalogue/`"

### Evidence that determines location

1. The plan gives `CasCatalogue` one production role (`plan.md:351`): public entrance.
2. The production gate audits three roots. `CasGates/KernelPurityRules.lean:27-28`: "The replacement production closure and its public leaf contract", `productionRoots := [CasCompiler, CasRuntime, CasContract]`. `violations` skips every declaration whose module root is not in the list (`KernelPurityRules.lean:169-173`). `CasGates/Production.lean:193` runs it with `productionRoots`.
3. The import closure of `CasRuntime.Session` holds ten modules outside those roots: `CasCatalogue.Admission`, `Codec`, `Decide`, `EquationData`, `Evaluation`, `GraphData`, `InterpretationFailure`, `Registry`, `Resolve`, and `CasTools.NativeExpression`. The production gate does not audit them. One of them holds the evidence runner that the gate names (`KernelPurityRules.lean:67`: `CasCatalogue.Evaluation.runProcedure`).

Consequence: a module that stays in the closure of `CasRuntime.Session` belongs under `CasCompiler/` or `CasRuntime/`. A module that is a public entrance stays in `CasCatalogue/`. A module whose only production consumer is a tool belongs with that tool.

### Evidence for each module

| Module | Defines | In the closure of `CasRuntime.Session` | In the closure of `CasDsl` | Direct importers |
| --- | --- | --- | --- | --- |
| `TestSuite` (393 lines) | The statement runner: `runFile`, `runSuite`, `withSession`, `runStatement`, `TestResult`, the commands `#cas_tests` and `#cas` (namespace `CasCatalogue.Language`) | no | yes | `CasCatalogue.lean:20`; `NotebookSession.lean:7`; tools `CasTools/Harness.lean:7`, `ExportFull.lean:9`; tests `CasRuntime/PropertyTests.lean:4`, `ScopedDeclarationTests.lean:3`, `UnpublishedOperationTests.lean:3`; `CasAcceptance/ReindexExecutionProbes.lean:3`; `benchmarks/question_identity.lean:7` |
| `Decide` (79 lines) | `kernelAccepts` (kernel check of a supplied proof), `kernelDecides`, `decideProp`, `decisionProof` (decision by `mkDecideProof` on a `Decidable` instance) | yes | yes | Kernel: `CasCompiler/ReadGraphRules.lean:4`, `SourceRing.lean:6`. Old path: `Codec.lean:7`, `ConstructionData.lean:5`, `EquationData.lean:5`, `FunctorActionData.lean:4`, `Semantic.lean:10`. Aggregate `CasCatalogue.lean:11` |
| `Evaluation` (277 lines) | `runProcedure` (`:35-61`), `evaluationsOf` (`:68-72`), `evaluatedDecides`, `decideEvaluated` (`:81-121`), `plumbingRoots` to `evidencePresentation` (`:127-275`) | yes | yes | Kernel: `CasRuntime/Session.lean:5`, `CasCompiler/SourceAdmission.lean:5`. Old path: `Language.lean:10`, `Realize.lean:10` |
| `InterpretationFailure` (51 lines) | Reader failure tags: `throwSemanticAmbiguity`, `keepTrialAmbiguity`, `throwUnsupportedSource`, `unknownSourceNameTag` and their tests | yes | yes | Kernel: `CasCompiler/Lower.lean:18`, `Surface.lean:8`, `CasRuntime/FixedInput.lean:4`. Old path: `Resolve.lean:9`, `Semantic.lean:8` |
| `Registry` (545 lines) | `RegistryEntry`, `RegistryState` (`SemanticState` with no added field), `registryState`, `registryRowsByModule`, and the registry manifest export (`RegistryManifest*`, `validateProjection`, `checkedRegistryManifest`) | yes, only through `Admission` → `Resolve` → `Registry` | yes | Old path: `Resolve.lean:7`. Tool: `CasTools/ExportJson.lean:7`. `CasAcceptance/Standard.lean:4`, `FibrationRegistryProbes.lean:9`. Aggregate `CasCatalogue.lean:16` |
| `QuestionIdentity` (215 lines) | The question serialization: `QuestionIdentity.encode`; `TermTable`, `TermRemap`, `termIdentity` (namespace `CasCatalogue.Realize`) | no | yes, through `TestSuite` → `CasTools.QuestionObservation` | Tool: `CasTools/QuestionObservation.lean:5`. Old path: `Realize.lean:16`. Probe: `TermGraphProbes.lean:4` |

`CasGates/KernelPurity.lean` imports all six (`:17`, `:22`, `:28`, `:35`, `:38`, `:49`); `CasGates/Production.lean:130` imports `Evaluation`.

Use of the two modules with C22 content in the new kernel:

| Use | Site | Row of "Kernel computation (C22)" |
| --- | --- | --- |
| `Decide.decideProp` decides the equality of two returned values | `CasRuntime/Session.lean:295` | T113, first row |
| `Evaluation.decideEvaluated` closes a question in Lean | `CasRuntime/Session.lean:201`; the closing step is `Evaluation.lean:92-102` (`Codec.conditionProof`, `mkDecideProof`) | T113, second row |
| `Decide.decisionProof` decides the obligations of a graph literal | `CasCompiler/ReadGraphRules.lean:69` | T035 |
| `Decide.decisionProof` decides the index bound of an indexed generator | `CasCompiler/SourceRing.lean:71` | none (see section G) |
| `Evaluation.evidencePresentation`, `normalizedValue` reduce the goal before the registered procedure | `CasCompiler/SourceAdmission.lean:85`, `:153` | T059 |
| `Evaluation.runProcedure` runs the registered evidence procedure | `CasCompiler/SourceAdmission.lean:87` | Permitted by C22 |

`kernelAccepts` (`Decide.lean:37-49`) type-checks a supplied proof in a bounded kernel call. It decides nothing. `Evaluation.lean:105` uses it.

Contravention of C22:

| Module | Contravenes C22 |
| --- | --- |
| `TestSuite` | No. It reports the outcome of the session |
| `Decide` | Yes: `kernelDecides`, `decideProp`, `decisionProof`. Not `kernelAccepts` |
| `Evaluation` | In part: the closing step `:92-102` (T113) and `:127-275` (T059). Not `runProcedure`, `evaluationsOf` |
| `InterpretationFailure` | No |
| `Registry` | No |
| `QuestionIdentity` | No. Its text states that it reduces nothing (`:97-99`) |

`Registry` in the new kernel: nine sites form `RegistryState` from `SemanticState` on the spot (`CasCompiler/PublishedSource.lean:193`, `:291`; `CasRuntime/ManifestAdmission.lean:58`, `:67`, `:79`; `Point.lean:90`, `:309`; `Presentation.lean:63`; `RoutedMethod.lean:387`). Each does it to call `RegistryState.form?`, `rejects` or `transport` of `CasCatalogue/Admission.lean` (`:178`, `:288`, `:265`).

### Decision

Decision: keep `TestSuite` in `CasCatalogue/` (it is the public entrance that T038 and T127 name); delete the decisions of `Decide` with their consumers (`decideProp` with T113; `decisionProof` with T035 at `ReadGraphRules.lean:69` and with T036 at `SourceRing.lean:71`; the module with removal steps 2, 4 and 5) and move `kernelAccepts` with the evidence runner; in `Evaluation`, T113 deletes the Lean closing step (`:92-102`) and the import of `CasCatalogue.Codec`, T059 deletes `:127-275`, and the remainder (`runProcedure`, `evaluationsOf`, the discharge by registered procedures) moves to `CasCompiler/`, with `CasGates/KernelPurityRules.lean:67` renamed; move `InterpretationFailure` to `CasCompiler/`; move `QuestionIdentity` to `CasTools/` (T029, T072), beside its consumer `CasTools/QuestionObservation.lean`; move `Registry` to `CasTools/`, beside the exporter `CasTools/ExportJson.lean`, when removal steps 4 and 6 have removed its importers `Admission` and `Resolve`.

Each move edits the import lists of `CasGates/KernelPurity.lean` and `CasGates/Production.lean`.

Strength of each part:

| Part | Basis | Strength |
| --- | --- | --- |
| `TestSuite` stays | T038, T127, `plan.md:351` | Determined |
| `Decide` decisions are deleted | C22; rows T113, T035 | Determined |
| `Evaluation` closing step and presentation code are deleted | C22; rows T113, T059 | Determined |
| The remainder of `Evaluation` and `InterpretationFailure` go to `CasCompiler/` | `productionRoots` (source) and `plan.md:351` | Determined by the source rule; the target file name is an implementation responsibility |
| `QuestionIdentity` and `Registry` go to `CasTools/` | Only consumer after the removal steps; `lakefile.lean:89` ("The registry exporter and the axiom audit") | Derived; no document states it |
| The task that performs each move | T113 and T059 edit `Evaluation`; T027 edits the tags of `InterpretationFailure` | Not stated by a document (see "Undetermined") |

### Governing passages

- `plan.md:351`: "Production locations remain `CasCompiler/{…}`, `CasRuntime/{…}`, actual `CasDsl`/`CasCatalogue` public entrances".
- Row T113 (`tasks.md:101`): "`mkDecideProof` evaluates a Mathlib `Decidable` instance by Lean reduction; C22 permits only a procedure registered in **M**."
- Constitution C18: "If a responsibility is removed or transferred, the implementation must actually perform that change rather than rename, centralize or retain the same responsibility behind a new interface."

---

## E. T007 state note, item (4): the selected limit

### Evidence

`CasCompiler/SourceLimit.lean` is 471 lines at the tip. It has not changed since `7661292`, the revision of the T007 state note.

Row T048, T007 ("the three formation functions").

- The judgement of a limit is `NativeSourceLimitSelection` (`CasCompiler/Elaborate.lean:74-88`). It has the fields `presentation` (`:81`), `diagram` (`:82`) and `interface : NativeLimitInterface` (`:83`).
- The binding is `SourceLimitSelection` (`Elaborate.lean:52-72`). It has `presentation` (`:59`), `diagram` (`:60`) and `interface` (`:61`).
- `LimitInterface` (`CasCompiler/LimitInterface.lean:18-22`) holds `presentation`, `diagram`, `standardization` and `dataConstructor`.
- The three formation functions fill these fields: `sourceBinaryLimit` (`SourceLimit.lean:119-122`), `sourceCreatedLimit?` with `creationSourceOwner` (`:229-236`, `:284-292`), `sourceNamedLimit` (`:351-355`). The interface comes from `preparedSourceLimit` (`:41-58`).
- `LimitEntry.dataConstructor` is consumed at `LimitInterface.lean:147` (`prepareDataConstructor`, `:54-86`) and at `CasCompiler/LimitFamily.lean:52`, `:114`, `:182`, `:276`. The data ports come from it in `ConstructorPorts.prepare` (`CasCompiler/ConstructorPorts.lean:34-50`).
- `LimitEntry.standardization` is consumed at `LimitInterface.lean:88-101` and at `CasCompiler/CreationFamily.lean:197-209` (`CreationFamily.diagramAt?`: "Read the diagram constructor from the accepted standardization's original target"), which `SourceLimit.lean:186` calls. Other uses: `CreationFamily.lean:247`, `:304`; `LimitFamily.lean:54`; `PreparedCreationFamily.lean:98`.

Row T048 (`SourceLimit.lean:239-258`). At the tip those lines are in `sourceCreatedLimit?`. `sourceLimitLeg?` is `SourceLimit.lean:433-469`.

- It takes the cone from the retained selection (`:436-437`).
- It forms the leg as `NatTrans.app (Cone.π cone)` or `NatTrans.app (Cocone.ι cone)` at the index (`:441-447`).
- It sets the apex end of the leg to the receiver occurrence (`:456-457`) and retains receiver and index with `retainLimitLeg` (`:459`).
- The function has no `cone.appArg!`, no list of candidates and no `isDefEq`.

What remains in the same function, under other rows:

- `sourceLimitLeg?` reads the presentation with `sourceApplication? selection.declaration cone` (`:438`), from metadata on the cone term. It does not read the field `selection.presentation`. This is the term encoding of T117.
- The ordinal selects the index by `constructionIndex` (`:403-424`): the `ordinal`-th constructor of an enumeration in Lean declaration order (`:421-424`, `constructionCases` `:360-396`). This is the row T048 of "Meaning or route selected by something other than the formal rule" (task T123).
- For an index type `Fin n`, the bound `ordinal < n` is decided by `mkDecideProof` (`:417-420`). No row lists this (section G).

### Fact

Fact: at `fc7fdf8` the judgement and the binding of a limit retain the presentation, the diagram and the interface with its `standardization` and `dataConstructor` (`CasCompiler/Elaborate.lean:52-88`), both registry fields are consumed (`CasCompiler/LimitInterface.lean:88-101`, `:147`; `ConstructorPorts.lean:34-50`; `CreationFamily.lean:197-209`), and `sourceLimitLeg?` (`CasCompiler/SourceLimit.lean:433-469`) takes the leg from the retained cone with no search for a definitionally equal candidate; the two rows T048, T007 and T048 of "Selected data recovered after the fact" do not hold and are removed.

Limit of this fact: it comes from reading. No test ran. The T007 state note records two failing modules at `7661292` (`CasRuntime.FixedInputResultTests`, `CasRuntime.ExecuteTests:741`). This reading did not examine whether either depends on the limit selection.

### Governing passage

- `tasks.md:67`: "The rows are kept current as work lands: a repaired row is removed".
- Constitution C23: "A chosen limit retains its diagram, cone and defining legs, with the specified universal operation".

---

## F. Row T010, T022: a demand that reaches its own occurrence

### Evidence

The wait is in `Execute.reuseResponse` (`CasRuntime/Execute.lean:45-59`). When `CellTransaction.reuse` answers `pending` or `running` for the occurrence of the request, the executor makes a waiter (`:54`) and blocks in `CompletionWaiter.wait` (`:57`). `executeDemand` reaches the same wait when `CellTransaction.claim` answers `waiter` (`:75-78`; `projectStored` `:116-119`). The wait ends when the producer completes the occurrence or the cell settles. A producer that waits on its own occurrence, on its own thread, never ends.

A self-wait needs a second demand for an occurrence that is claimed and not complete. Every path of a request into the executor at the tip:

| Path | Occurrence of the request |
| --- | --- |
| `demand` in the lowerer (`CasCompiler/Lower.lean:177-183`): one `PFunctor.FreeM.lift request`, run at once by `Execute.run` (`CasRuntime/Kernel.lean:49`) | Fresh. Each of the 17 call sites of `demand` prepares its request immediately before, with `frame.environment.ledger.allocate` (`Lower.lean:1271`, `:1287`, `:1471`, `:1574`, `:1602`, `:1688`, `:1718`, `:1752`, `:1774`, `:1798`, `:1828`, `:1870`, `:1882`, `:1897`, `:1940`, `:1955`, `:2064`) |
| `methodParameterAssembly` (`CasRuntime/RoutedMethod.lean:64-82`) | Fresh (`:65`). The allocator comes from the lowerer (`Lower.lean:1739`, `:1768`) or from `Kernel.child` (`ChildCall.lean:67`) |

No other non-test code lifts a request (`git grep` of `FreeM.lift`, `Execute.run` and `run :=` over `CasRuntime` and `CasCompiler`). `OccurrenceLedger.allocate` (`CasRuntime/Occurrence.lean:55-59`) returns a new identity at each call.

The operands of a request are value bindings that exist before the occurrence is allocated: the lowerer lowers the argument terms first and allocates after. The result of the occurrence has no value identity until the executor stages it.

A retained request is never lifted again. `ClosureCode.family`, `.retainedPoint` and `.constructionLeg` (`CasRuntime/Closure.lean:14-35`) keep a `PreparedRequest` as data. A later demand on such a closure has its own fresh occurrence, and the invocation reserves that occurrence (`Demand.lean:384-386`, `:420`; `Invocation.lean:72`). The retained request is read through `CellTransaction.completionFor?`, which does not wait (`Demand.lean:67`; `LimitUniversal.lean:24`, `:95`).

A lazy operand that the executor forces (`kernel.resolveFixedInput`, `InputResultPlan.resolve`) is lowered by `evaluateSource`. It gets fresh occurrences.

A call that a provider requests goes through `Kernel.child` (`CasRuntime/ChildCall.lean:36-123`): `PublishedSource.prepare`, then `evaluateSource` (`:121-123`). It gets a fresh occurrence too. A provider that answers each request with a deferred call of the same operation on the same input therefore recurses with a new occurrence and a new request at each level. No guard on that recursion is in `CasRuntime` (search for `cycle`, `recurs`, `depth`, `parent chain`).

The `waiter`, `pending` and `running` branches are reached only by tests that demand one occurrence from two tasks (`CompletionWaiterTests.lean:51-78`, `CompletionFailureTests.lean:46-70`).

Limit: `CasCompiler/Lower.lean` has 2130 lines. Lines 120-200 were read, and every `demand`, `allocate` and `PreparedRequest.for*` site was found by search. The rest of the file was not read.

### Fact

Fact: at `fc7fdf8` the lowerer cannot produce a demand for a running occurrence: each request that reaches the executor carries an occurrence allocated at its own call site (`CasCompiler/Lower.lean:177-183` with 17 preparation sites; `CasRuntime/RoutedMethod.lean:64-82`), is demanded once, and has operands that were staged before that allocation; the self-wait of `CasRuntime/Execute.lean:45-59` has no production caller, and the recursion that T022 and T023 must refuse is a chain of fresh occurrences that provider-requested calls make (`CasRuntime/ChildCall.lean:36-123`), which no code detects.

Consequence for the row: the required mechanism "Refuse such a demand as `unavailable`" cannot key on the occurrence. The recursion guard of T022, T023 needs the parent chain of the request (runtime contract, section 6, `SuspensionRecord`: "original request/parent chain").

### Governing passages

- Runtime contract, section 6: "Detect real pending-demand cycles; retries are not a solution."
- `tasks.md:351` (public-path test of T022, T023): "The recursion refusal is `unavailable`".

---

## G. Rows that do not match the source at the tip (found during this work)

These are outside the six items. Each is a fact from the same reading.

| Row or passage | Fact at `fc7fdf8` |
| --- | --- |
| "Removal of the old path", step 4: `Admission` blocked by `ImageFormProbes` | Eight production modules import `CasCatalogue.Admission`: `CasCompiler/CategoricalPointFamily.lean`, `PublishedPorts.lean`, `PublishedSource.lean`, `SourceMethod.lean`; `CasRuntime/ManifestAdmission.lean`, `Point.lean`, `Presentation.lean`, `RoutedMethod.lean`. `Admission` imports `CasCatalogue.Resolve` (step 6), and `RegistryState.rejects` (`Admission.lean:288`), which the kernel calls, uses the old resolver (`state.resolveMethod`, `:341`; `state.resolveProperty`, `:350`) |
| "Removal of the old path", table | `CasCatalogue/GraphData.lean` (imported by `CasRuntime/CallablePacket.lean`) and `CasCatalogue/NotebookSession.lean` are in no row |
| `tasks.md:200`: "`CasCatalogue/TestSuite.lean` imports only `CasRuntime.Session` and `CasCompiler.Parse`" | It also imports `CasRuntime.Inspect`, `CasTools.QuestionObservation`, `Worker.Cell`, `Worker.Output` (`TestSuite.lean:7-18`) |
| `tasks.md:268`: "`CasCatalogue/QuestionIdentity.lean` is present and the new kernel does not use it" | `CasTools/QuestionObservation.lean:100`, `:153` use its `TermTable` for the question export |
| "Kernel computation (C22)", table | Two kernel decisions have no row: `CasCompiler/SourceRing.lean:67-73` (`Decide.decisionProof` for the index of a generator) and `CasCompiler/SourceLimit.lean:415-420` (`mkDecideProof` for `ordinal < n`) |
| Row T022, T023, T032 (`CasRuntime/ChildCall.lean:49-125`) | `Kernel.child` now passes the frame to `PublishedSource.prepare` (`CasCompiler/PublishedSource.lean`) and then to the lowerer (`ChildCall.lean:121-123`). The row describes the earlier body. This file was not analysed against C23 |
| Row T038, T085 (`CasCatalogue/TestSuite.lean:216-222`, `:123-131`) | The lines moved. `#cas` is `TestSuite.lean:357-389`; it reads the session of the Environment (`:361`) and installs the session after the statement (`:375`). The described defect was not tested |
| Production purity gate | It audits the roots `CasCompiler`, `CasRuntime`, `CasContract` only (section D). Ten modules of the production closure are outside it |
| Diagnostic output | Committed `dbg_trace` calls in production modules: `CasRuntime/Execute.lean` (9), `PreparedRequest.lean` (15), `Environment.lean` (14), `Association.lean` (4), `CasCompiler/Lower.lean` (87) |

---

## Undetermined

| Item | What is not determined | What is missing |
| --- | --- | --- |
| B, `RealizationProfile.normalized` | Keep the field or delete it | Runtime contract section 5.3 and T026 require the frozen normalized sets and their hash. The private `rules` and `sha256` hold them. No document names a reader of the normalized document. SC-005 and T078 say "Record … profile" and do not say whether the record is the document or its identity (`id`, `sha256`). If the record is the document, T078 is the consumer and the field stays. If not, the field is deleted and `RealizationProfileTests` compare `sha256` with the hash of the expected document |
| A, `CompletionWaiter.detach` | The production party that detaches | T088 requires the behaviour. T085 says "internal consumers may join the same actual pending request" and names no consumer. Item F shows that none exists at the tip |
| A, `FramedConnection.cleanupFailures` | The shape of the report to the notebook worker | T089 requires the report. `Worker.Cell.Active` has no field for it at the pinned revision. The field belongs to the worker half of T088, T089 in lean-jupyter-kernel |
| C | The signature and the module of the compiler entry | The documents state the responsibility, not the interface (`plan.md:351`) |
| D, `QuestionIdentity`, `Registry` | The target directory `CasTools/` | It is derived from the single remaining consumer and from `lakefile.lean:89`. No governing document states a location for a module of `CasCatalogue/` that is neither a public entrance nor in the production closure |
| D | The task that performs each move | No document assigns the relocation of `Evaluation`, `InterpretationFailure`, `QuestionIdentity`, `Registry`. T113 and T059 edit `Evaluation`; T027 edits the tags of `InterpretationFailure`; T029, T072 own the question export; removal steps 4 and 6 free `Registry` |
| D, `Registry` | Whether `RegistryState` and `RegistryEntry` remain after the move | They add no field to `SemanticState`. 17 `CasAcceptance` probe files call `registryState` or `validateRegistryEntryDeclaration`. T064 says to adapt probes and does not address these wrappers |
| D, `Decide`, `SourceRing.lean:71` | The owner task of this decision | The location has no row in "Kernel computation (C22)". T036 owns indexed generators by capability |

---

## Files read

Governing documents, on `main`:

| Document | Extent |
| --- | --- |
| `specs/001-categorical-research-language/tasks.md` | Whole file (648 lines) at `a9f3790`; the 8 changed lines of `45910a5` |
| `specs/001-categorical-research-language/contracts/computational-runtime.md` | Whole file (284 lines) at `a9f3790`; the changed paragraph of section 6 at `45910a5` |
| `.specify/memory/constitution.md` | Sections C18, C22, C23 in full |
| `specs/001-categorical-research-language/plan.md` | Lines 300-380 (section "Source organization recorded at `e24045ca`" in full, and the artifact map) |
| `CONTRIBUTING.md` | Whole file |
| `contracts/notebook-session.md` | Lines 76-90 and 105-124, and a search for cancel, drain, waiter, profile |
| `data-model.md`, `contracts/mathematical-input.md` | `data-model.md:69`; `mathematical-input.md:25-29`; searches |

Source at `fc7fdf8`, read in full:

- `CasRuntime/`: `Connection`, `Transport`, `Transaction`, `Invocation`, `Execute`, `Kernel`, `KernelState`, `BackendConnections`, `Session`, `PreparedRequest`, `RoleMap`, `Realization`, `Demand`, `ChildCall`, `Occurrence`, `LimitUniversal`, `Closure`.
- `CasCompiler/`: `Program`, `SourceLimit`, `LimitSelection`, `LimitInterface`.
- `CasCatalogue/`: `TestSuite`, `Decide`, `Evaluation`, `InterpretationFailure`, `Registry`, `QuestionIdentity`, `NotebookSession`.
- `CasCatalogue.lean`, `CasDsl.lean`, `CasRuntime.lean`, `CasCompiler.lean`, `lakefile.lean`, `CasGates/KernelPurityRules.lean`, `CasTools/QuestionObservation.lean`.

Source read in part:

| File | Lines |
| --- | --- |
| `CasCompiler/Lower.lean` (2130 lines) | 120-200; every `demand`, `allocate`, `PreparedRequest.for*` site by search |
| `CasRuntime/Encode.lean` | 1-60, 380-469 |
| `CasRuntime/Inspect.lean` | 366-420; declaration list |
| `CasRuntime/RoutedMethod.lean` | 18-96, 676-715 |
| `CasRuntime/Point.lean` | 100-124 |
| `CasRuntime/Scope.lean` | Search hits only (`:89`, `:96`) |
| `CasCompiler/Elaborate.lean` | 44-144 |
| `CasCompiler/SourceRing.lean`, `ReadGraphRules.lean`, `SourceAdmission.lean` | 52-80; 55-75; 60-115 and 145-156 |
| `CasCompiler/ConstructorPorts.lean`, `LimitFamily.lean`, `CreationFamily.lean` | 24-50; four excerpts; 193-210 |
| `CasGates/KernelPurity.lean`, `Production.lean` | Import lists and the `run_cmd` blocks |
| `CasCatalogue/GraphData.lean`, `Admission.lean`, `Codec.lean` | 1-40; 1-60 and 286-330; import lines |
| `CasRuntime/ManifestAdmission.lean`, `Presentation.lean`, `CasCompiler/PublishedSource.lean` | The `RegistryState` sites only |
| Test modules | The excerpts that the sections cite |
