# Reuse record: `cc-realize-2cat`

## Queries
The corpus queries of [`cc-cells.md`](cc-cells.md) (same layer), 2026-09-29.
Additional searches on 2026-10-20: `presentation element structural encoding` and
`selected object computational form`. The returned algebraic-element storage and
unrelated implementation matches provide no owner for this kernel wire protocol.

## Owner
Mathlib: `Functor` for the catalogue's functors, `CatCommSq` and its pasting for commuting squares
between them, `Cat` as a strict bicategory. Presentation forms and what each denotes are
`lean-categories`'.

## New code: adaptation at the kernel boundary
The kernel's composition of a route's steps over the declared presentation forms. A leaf supplies
no category of handles, no denotation and no square: it registers opaque computations against
each step's declared type.

An element's computational form retains the entire form of its independently
selected object, including a registered functor or structural-edge image. Its
registration identity and category are those of that supplied form; no carrier
lookup selects a replacement named object. The element envelope carries the full
selected descriptor and retains its computational ownership. This is protocol
composition over the existing formal point and route, not new mathematics.

## Selected V1 implementation and reuse (2026-10-28)

**Decision:** adapt the existing selected-plan evaluator and its invocation owner. Adapt
PolyFun's caller/handler entry, suspension and return algorithm into that owner; keep the
existing mathematical plan builders, completion validators, lift fold and public dispatcher.
Use encapsulated checked records and opaque operand/output references to the complete selected
interfaces. The implementation removes the migrated construction's recursive scheduling,
expression/packet recovery and competing completion writes. It does not introduce another
program store, a new semantic calculus or a native-value foundation migration.

This settles the implementation choice left open by the
[#79 disposition](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6476550921)
and #80's reuse checklist. The first fixed mathematical computation validates the chosen
implementation; it is not another import-versus-rewrite survey. Mathematical acceptance,
independent public use and the complete V1 inventory remain #10/#66/#69/#24. The ordinary
categorical APIs named above do not replace the higher data required by #82/CC-HIGHER.

### Existing source to import, retain and adapt

The runtime source anchor is kernel candidate
[`d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b`](https://github.com/dzackgarza/lean-cas-dsl/tree/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b).
Later documentation changes are not a runtime result. These are existing kernel modules,
not proposed external package dependencies.

| Responsibility | Selected source and symbols | Import and adaptation placement |
| --- | --- | --- |
| Complete selected request and canonical result | [`Realize.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/Realize.lean#L401-L688): `SelectedCallableInvocation`, `SelectedStructuredInvocation`, `SelectedStructuredProjection`, `SelectedRecordProjection`, `SelectedRoutedInvocation`, `SelectedPrescribedInvocation`, `CapturedInvocationInterface`, `InvocationExecution` | Adapt these records and `Harness.invocations` inside `CasCatalogue.Realize`. Selected dependencies and output positions refer to the canonical owner. Encapsulate construction, completion and output access; a copied `Wire` cannot install different completion data. |
| Registration and completion | [`retainCapturedInvocation`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/Realize.lean#L2246-L2289) and [`observeCapturedInvocation`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/Realize.lean#L18045-L18101) | Preserve original-input, cycle, result-interface and owner checks. Adapt this owner into the demand/resume driver below. `Harness.invocations` remains the authority; `Harness.results` cannot select or replace operands/results for a migrated computation. No second execution store is added. |
| Field positions, intermediate stages and comparisons | [`RoutedResultPlan.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/RoutedResultPlan.lean): `Plan`, `IntermediateStage`, `Slot`, `ProjectionActionPlan`, `Plan.stage`, `Plan.projectionAction` | Keep `import CasCatalogue.RoutedResultPlan` in the execution implementation. Its selected positions and schemas supply suspended-frame dependencies; do not build another graph that restates them. |
| Formal construction and returned fields | [`StructuredResult.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/StructuredResult.lean): `DataPlan`, `dataPlan`, `Result`, `complete` | Keep `import CasCatalogue.StructuredResult`. Reuse its formal/computational distinction and field validation. It imports `Semantic`, `Admission` and `Codec`, not `Realize`. |
| Prepared public requests | [`ServiceRequest.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/ServiceRequest.lean#L137-L173): `Operand`, `Prepared`; [`UniversalServiceRequest.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/UniversalServiceRequest.lean#L273-L365): `materializedLimit`, `liftField`, `liftFactor` | Keep the existing service-module imports. Preserve their completion checks and staged preparation; constrain inconsistent result-kind combinations at checked construction. A later callable/service request fixes its interface at its own preparation boundary. |
| Selected lift and its four actual outputs | [`SelectedLift.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/SelectedLift.lean): `Plan`, `select`, `factors`; [`LiftStageExecution.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/LiftStageExecution.lean#L16-L132): `Input`, `Field`, `Result`, `fold` | Keep `import CasCatalogue.LiftStageExecution`, which already imports `LiftedSubobjectData` and `DataOwnership`. Use the existing field order and endpoint roles with retained operands. Do not port a second four-field loop. |
| Supplied construction in later factors | `Realize.selectedLiftExecution`, `retainedLiftStage`, `executeRetainedLiftFactor`; the routed-method helper `executePrescribedRetainedWith`; `UniversalServiceRequest.liftFactor` | Adapt the direct selected-lift/factor path first. The subsequent factor receives the actual selected stage, outputs, inclusion and comparisons through the canonical owner. Adapt the routed prescribed-method helper when covering that use; it is not the direct selected-lift entry point. Remove each migrated recovery branch rather than regenerate its construction. |
| Actual selected comparison components | [`CellAction.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/CellAction.lean): `assemble`, `select`, `component`, `componentIso`, `objects`, `maps` | Keep `import CasCatalogue.CellAction`, with its `DirectConstruction` and `CategoryContext` inputs. Consume the accepted upstream comparison declarations; no route quotient or order-based choice replaces their components. |
| Computational prerequisite closure | [`ComputationDerivation.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/ComputationDerivation.lean#L30-L47): `grounded`, `instantiate`, existing compiler and recursion guard | Keep `import CasCatalogue.ComputationDerivation` and its existing `LeanCategories.Catalogue.Registry.Computation` input. Preserve realized-form admission and failure distinctions; do not introduce a cost optimizer for this replacement. |
| Owners, framing and external effects | [`DataOwnership.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/DataOwnership.lean): `Data`, `validate`, `project`, `array`, `object`; `Realize.checkDataOwners`, [`sendData`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/Realize.lean#L2506-L2591); `CasContract.Port` | Keep the current kernel/contract imports. Backend invocation stays behind `sendData`; its received reply is untrusted until the prepared completion checks run. Preserve inline and opaque alternatives and positioned multi-owner data. |

The first fixed RX-LIFT computation enters through the
[direct `.selectedLift` branch](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/Realize.lean#L13370-L13376),
which calls `SelectedLift.select` and then `selectedLiftExecution`. This direct path is not
already one of the six `CapturedInvocationInterface` variants; `SelectedPrescribedInvocation`
is the routed-method protocol. Add a checked direct-lift case to the same invocation owner,
carrying the selected `SelectedLift.Plan` and operand references. Assemble its existing
`LiftStageExecution.Input` from those retained dependencies when they are available; preserve
the four-field fold and completion checks. This extends the selected owner, not its stores.

Implement the owner/driver adaptation in `Realize.lean` first, using its existing imports.
Moving a coherent group into a smaller module is ordinary packaging work, not a prerequisite
or another architectural decision. Such a split preserves the import direction: lower-level
plans and service preparers do not import the top-level evaluator. The source/input policy
for own-organization dependencies is unchanged; diagnostic source anchors are not permanent
delivery pins.

### Source adaptation: PolyFun's suspension and return algorithm

Use PolyFun commit
[`b13c074410a955407886cb3fe27e59130aeac090`](https://github.com/Verified-zkEVM/PolyFun/tree/b13c074410a955407886cb3fe27e59130aeac090),
[`PolyFun/PFunctor/Free/HandlerMachine.lean`](https://github.com/Verified-zkEVM/PolyFun/blob/b13c074410a955407886cb3fe27e59130aeac090/PolyFun/PFunctor/Free/HandlerMachine.lean#L38-L82):
`Phase` (39–42), `runPrefix` (67–77), `result` (80–82).

Adapt its three nonterminal transitions into the existing invocation owner:

1. A demand for a selected dependency suspends the caller with its exact next operand/output
   position and enters that dependency.
2. A validated dependency return fills that position and resumes the suspended selected plan.
3. An external request uses the existing prepared interface and `sendData`, retaining the
   suspended caller until the reply has passed completion validation.

The suspended frame retains the selected invocation, required operand/output references and
the next position of its existing plan. It is not a new `FreeM` tree or an arbitrary closure
that can rediscover the selected input. Keep the existing cycle and session checks. Completed
data are exposed only through canonical completion; an unvalidated handler return is not a
completed kernel result. Failure exits preserve the existing strata and never resume with
default data. Later public service requests still prepare at their appropriate stage.

Retain demand-driven execution. The dependencies are those of the selected realization;
an adequate fused realization remains permitted and does not invent primitive dispatches.
The adaptation does not copy PolyFun's counters, fuel interface or an additional program
store. Its original theorem about polynomial-program interpretation does not prove this
adaptation, the preservation of a selected mathematical construction, or a leaf's answers.
Retain source attribution when adapting the algorithm.

For the first fixed RX-LIFT computation, transfer the recursive operand demands in
[`selectedLiftExecution`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/Realize.lean#L17008-L17071)
and [`executeRetainedLiftFactor`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/Realize.lean#L17078-L17210)
from their `realizeEndpoint`/`realizeUnobserved` and observation callbacks to the common
demand/resume driver. Preserve the existing selected plan, retained endpoint checks,
`LiftStageExecution.fold` and prepared completion validation; remove this path's competing
operand recovery and completion writes. Calling its old recursive orchestration unchanged
under a new case does not implement the adaptation.

When extending coverage to the existing universal-limit construction, replace the recursive
`observeObject`/`observeMap` scheduling in
[`observeStructuredInvocationWith`](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/CasCatalogue/Realize.lean#L9901-L10032)
and its migrated parent/endpoint recovery through that same owner. This remains required
for universal-limit coverage; it is not a prerequisite to the first direct lift/factor trial.
Wrapping that observer unchanged likewise fails. Existing plan builders and validators
remain; dependency demand, result adoption and resumption have one common owner.

### External source dispositions

| Source and revision | V1 disposition | Responsibility and limit |
| --- | --- | --- |
| PolyFun `b13c0744`, `PolyFun/PFunctor/Free/HandlerMachine.lean`, `Phase/runPrefix/result` | **Adapt the transition algorithm locally; no package import.** | Use the three transitions above against the existing selected plans and invocation owner. This is the selected scheduling replacement, not a second evaluator representation. |
| Same PolyFun revision, [`PolyFun/PFunctor/Handler/Stateful.lean`](https://github.com/Verified-zkEVM/PolyFun/blob/b13c074410a955407886cb3fe27e59130aeac090/PolyFun/PFunctor/Handler/Stateful.lean#L55-L91), `Handler.Stateful.run/run_liftBind`; [`PolyFun/PFunctor/Free/Cursor/Occurrence.lean`](https://github.com/Verified-zkEVM/PolyFun/blob/b13c074410a955407886cb3fe27e59130aeac090/PolyFun/PFunctor/Free/Cursor/Occurrence.lean#L40-L49), `Occurrence/Completion/completeWith/complete`; [`PolyFun/IPFunctor/Free/Basic.lean`](https://github.com/Verified-zkEVM/PolyFun/blob/b13c074410a955407886cb3fe27e59130aeac090/PolyFun/IPFunctor/Free/Basic.lean#L11-L24), `IPFunctor.FreeM` | **Reference only; no additional V1 port.** | These are real stateful, retained-occurrence and indexed-computation mechanisms. The kernel already supplies its persistent owner and lift fold. Porting another storage/program layer would duplicate those responsibilities. |
| cslib `1e12b4a15de5a5ad9dfe271074872a2df4c1adbc`, [`Cslib/Foundations/Control/Monad/Free.lean`](https://github.com/leanprover/cslib/blob/1e12b4a15de5a5ad9dfe271074872a2df4c1adbc/Cslib/Foundations/Control/Monad/Free.lean), `Cslib.FreeM/liftM`; [`Cslib/Foundations/Data/PFunctor/Free.lean`](https://github.com/leanprover/cslib/blob/1e12b4a15de5a5ad9dfe271074872a2df4c1adbc/Cslib/Foundations/Data/PFunctor/Free.lean), `PFunctor.FreeM/liftM` | **Reference only; no package import or local free-monad port for V1.** | Reusable sequencing laws do not provide this kernel's complete selected interfaces, persistent result association or ownership validation. The selected-plan representation already exists. |
| CAP_project `fb48c41`, [`CAP/gap/MethodRecord.gi`](https://github.com/homalg-project/CAP_project/blob/fb48c41/CAP/gap/MethodRecord.gi#L285-L361), `KernelEmbeddingWithGivenKernelObject/KernelLiftWithGivenKernelObject`; [`CAP/gap/DerivedMethods.gi`](https://github.com/homalg-project/CAP_project/blob/fb48c41/CAP/gap/DerivedMethods.gi#L184-L193) | **Adapt the supplied-construction interface discipline; no GAP code imported into the kernel.** | Later factors consume the supplied construction and its associated inclusion. Apply this through the existing retained-stage and `UniversalServiceRequest.liftFactor` paths; do not reconstruct a fresh construction from its defining arrow. This does not assert a kernel universal property in a category where the accepted input supplies none. |
| Same CAP revision, [`CAP/gap/Derivations.gi`](https://github.com/homalg-project/CAP_project/blob/fb48c41/CAP/gap/Derivations.gi#L387-L453), `OperationWeightUsingDerivation/TryToTriggerDerivation` | **Reference only; defer cost optimization.** | Keep existing `ComputationDerivation.grounded` and realization selection. Do not port registration-position ties as mathematical coherence. CAP's [CanCompute-in-filter check](https://github.com/homalg-project/CAP_project/blob/fb48c41/CAP/gap/Derivations.gi#L53-L55) is a warning, not the kernel's semantic boundary. |
| Lean `v4.33.0`, [`src/Lean/LocalContext.lean`](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/LocalContext.lean), [`src/Lean/Meta/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Meta/Basic.lean#L1905-L1927), `withLetDecl/mkLetFVars` | **Use existing APIs for scoped elaboration in #66.** | Preserve or close the local context; `withLetDecl` restores it on return. An escaping `FVarId`, normalized RHS or ordinary lexical binding does not become persistent computational result identity or replace definition-at-use semantics. |
| GATlab/Catlab sources recorded in [cross-repository prior art](cross-repository-execution-prior-art.md) | **Reference only for this replacement.** | Keep the existing catalogue selection, `CategoryContext` and component machinery. No Julia dependency or second mathematical registry is introduced. |
| `lean4-itree`, `debruijn-ssa`, `lean-mlir` candidates in the [library survey](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6475309126) | **Defer dependencies and ports beyond this V1 work.** | Coinductive traces and a general SSA/compiler IR are not required to replace this selected construction's finite dependency scheduling and retained data. They are not unfinished prerequisites. |

The inspected cslib toolchain is `v4.36.0-rc1`; PolyFun's
[package configuration](https://github.com/Verified-zkEVM/PolyFun/blob/b13c074410a955407886cb3fe27e59130aeac090/lakefile.toml#L31-L40)
uses Mathlib and cslib `v4.35.0`, while this kernel source uses Lean `v4.33.0`. This kernel
replacement adds none of these packages and performs no toolchain upgrade for this adaptation. This is a settled
scope/dependency decision, not a claim that every historical version or bounded port is
incompatible. The concrete algorithm above is adapted at the current toolchain.

### Required deletions and evidence

For the first fixed #69 computation, the integrated replacement removes:

- Recursive dependency scheduling and competing recovery/completion in the direct
  `selectedLiftExecution`/`executeRetainedLiftFactor` path and its migrated projections.
  Preserve `LiftStageExecution.fold`; the common driver owns demand and resumption.
- Retrieval of already selected operands from unanchored expression keys in `realize`,
  `realizeUnobserved` and migrated observation branches, and selection of an owned result
  by JSON equality in `serviceRetained`. Keep genuinely admitted portable-value decoding
  and the exact public reference path.
- The migrated raw trace overwrite following produced-route preparation in
  `Language.typedParameter`; selected aliases retain the original producer association.
- Copied completion state and alternate writes for that construction, including recovery
  through the legacy `executePrescribedLift`/`legacyLiftRecovery` compatibility adapter.
  Its remaining unmigrated callers are not silently removed or treated as already covered.

The universal-limit extension subsequently removes its competing scheduling in
`observeStructuredInvocationWith` through the same driver. That later deletion is required
for that construction, not an additional prerequisite to the first lift/factor result.

The current `observeCapturedInvocation` and `LiftStageExecution.fold` are reused because
they already carry the exact validation and ordered-output responsibilities. The removed
paths are what allowed those facts to be recovered or copied differently elsewhere. This
is the expected saving; no runtime speedup, day estimate or passing build is inferred from
source inspection. Preserve hostile controls at the surviving boundary rather than retaining
an obsolete helper solely for its probe.

Record the implemented adaptation, actual import list, removed responsibilities and focused
build/execution results here. Keep the fixed first-stage RX-LIFT questions, comparison and
factor use, compositional argument and independent public-only trial in #69; complete #24's
unchanged inventories afterwards. A renamed observer, another store or a scalar answer
without the defining maps fails the existing trial. No compilation, compatibility or
mathematical acceptance is claimed by this planning record.

### Implemented source and preservation argument (2026-10-28)

This section records the working source adaptation and its source-level invariant
argument. Focused compilation and the unchanged first RX-LIFT computation remain
separate evidence gates; this review records no runtime pass, mathematical
acceptance, or completion of the full V1 inventory.

The adaptation is in [`Realize.lean`](../../CasCatalogue/Realize.lean). Its import
list remains unchanged: the implementation reuses `LiftStageExecution`,
`LiftedSubobjectData` (and its `SelectedLift` input), `StructuredResult`,
`RoutedResultPlan`, `CellAction`, `DataOwnership`, the three existing service
preparers, `ComputationDerivation`, and `CasContract.Port`. It adds no PolyFun,
cslib, or other package import. The PolyFun transition attribution remains beside
`demandCapturedInvocation`; the local invariant below is not an imported theorem.

| Implemented responsibility | Existing owner and adaptation |
| --- | --- |
| Direct lift, ordinary lift field, and later factor preparation | `captureDirectLiftInvocation`, `captureLiftField`, and `captureLiftFactor` extend `CapturedInvocationInterface` with `directLift`, `liftField`, and `liftFactor`. Complete plans, parents, ordered operand Wires, roles, and expected types are retained before execution. |
| Entry, suspension, and return | `InvocationFrame` is a local stack frame over `Harness.invocations`. `capturedInvocationFrame` authenticates the original input and unique occurrence. `demandCapturedInvocation` fills the next fixed operand slot and enters a staged child when required. |
| Resumption and completion | `resumeCapturedInvocation` consumes the returned operand vector. Direct lifts reuse `LiftStageExecution.fold`; fields use their parent's retained stage; factors use the supplied construction and maps. `completeCapturedInvocation` performs the sole canonical invocation-result write, shared with the older protocols. |
| Exact nested service inputs | `Wire.serviceInputPaths`, `ServiceRequest.Prepared.inputPaths`, and public `inputRef` bind declared request positions to the existing retained operands. Preparers assign positions after normalization. `resultRef` remains the separate local completed-result reference. |

The positioned-input helpers reuse `DataOwnership.Path`, `Data.project`,
`renderCapturedActionData`, and `retainServiceOperands`. Corpus searches for
`JSON path occurrence binding` and `ActionDataTemplate DataOwnership InterfaceScope`
provided an unrelated manifest match and no matching owner, respectively. There
is no second semantic or execution store. `some #[]` explicitly disables legacy
packet recovery even when a request has no retained inputs. A whole supplied
factor map remains at its exact request position with its original envelope and
ownership; decoding its public interface does not reconstruct its packet.

#### Compositional invariant

The source argument is induction over the driver's entry/return transitions,
with the existing four-field fold supplying the inner induction for a lift.

1. **Fixed selection at entry.** A frame names one canonical invocation record.
   The incoming Wire must match that record's original complete typed input;
   the stored interface supplies the executable plan. Neither copied metadata
   nor a returned packet chooses a different producer or mathematical request.
2. **Ordered dependency prefix.** `returned` is a prefix of the selected operand
   vector. Only its next ordinal can enter a child. A return is checked against
   that operand's fixed formal value, expected type, declared role, full category
   context, and live suppliers before the prefix grows. The suspended parent
   retains its next ordinal while the child runs; equal terms or bytes never
   select the receiving parent slot.
3. **Field and factor association.** Resumption requires the complete operand
   vector. The shared lift fold passes each actual preceding output into the
   next fixed field request; the backward comparison retains the forward
   comparison's actual endpoints. Field projection checks the parent's selected
   plans and output ordinal. A factor receives that parent's retained stage,
   all four outputs, actual inclusion/comparisons, and its original base and cone.
4. **Single completion.** The result must preserve the canonical formal result
   and full output interface, and every supplier must remain live. Completion
   rechecks the original table entry and refuses a second result installation.
   Dependency cycles and failed requests exit without filling a parent slot with
   default data. The caller receives the checked result of that exact occurrence.
5. **Inert prospective inspection.** `prospectiveDirectLift` uses the same input
   assembler and field fold in the private inspection harness. Its future slots
   remain recipes, and inspection cannot install live invocation completions.
   Original endpoint roles and typed field positions are therefore shared by
   admission and execution without treating a future slot as received data.

These checks preserve selected types, contexts, positions, and computational
provenance. They do not prove that a returned map obeys its defining equation,
that comparisons are inverse, or that a factor satisfies a universal property.
A well-framed wrong answer still requires the unchanged mathematical comparison
and factor observations. A typed framing proof establishes this preservation
property only; it is not a proof of the leaf computation.

#### Mathematical inputs of the first fixed slice

The diagnostic consumes the independently authored mathematical declarations at
[`3bd4d3d9695f288749c860368174462c4d689b7c`](https://github.com/dzackgarza/lean-categories/tree/3bd4d3d9695f288749c860368174462c4d689b7c).
This identifies the source actually loaded; it does not assert independent
acceptance or latest-main delivery. The relevant source owners are
[`MonoLift`](https://github.com/dzackgarza/lean-categories/blob/3bd4d3d9695f288749c860368174462c4d689b7c/LeanCategories/Catalogue/Lift.lean),
[`DegeneratePlaneLifts`](https://github.com/dzackgarza/lean-categories/blob/3bd4d3d9695f288749c860368174462c4d689b7c/LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/DegeneratePlaneLifts.lean),
and [`DegeneratePlaneFactorization`](https://github.com/dzackgarza/lean-categories/blob/3bd4d3d9695f288749c860368174462c4d689b7c/LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/DegeneratePlaneFactorization.lean).

Write `C = BilinModuleCat ℚ ℚ`, `D = ModuleCat ℚ`, and `U = forget ℚ ℚ`.
The selected source is the formed plane `source`; the selected base object is
the scalar module and its inclusion is `kernelInclusion`. The latter's module
kernel property is `kernel_universal` in `D`. The construction in `C` uses
`Kernels.forgetMonoLift ℚ ℚ`, a specified cartesian lift of that monomorphism.
It does not acquire a kernel universal property in `C` from the module result.

| Selected mathematical data or law | Association retained by the implementation |
| --- | --- |
| Complete scalar/value modules, source, inclusion and `kernelInclusion_mono` | `SelectedLift.select` checks the full evidence signature and functor, fixes the actual source and inclusion, checks monicity on the formal side, and closes the complete application. `SelectedLift.context` obtains both category bundles from that selected functor. `DirectConstruction` retains the explicit telescope; a carrier alone cannot supply these parameters. |
| `A = L.obj X i`, `j = L.hom X i`, `α = L.computation.forward X i`, `β = L.computation.backward X i` | The four selected ports stay in that declaration order. `LiftStageExecution.fold` uses the actual object output as the defining map's source, and the actual forward comparison's endpoints in reverse order for the backward comparison. Each field request carries its exact preceding output occurrences. |
| `U.map j = α ≫ i`, from `MonoLift.computation_fac` and `first_factorization` | The original inclusion, actual source image, actual lifted object and selected comparison remain distinct inputs. `directLiftInputs`, the field fold, and retained stage handles keep their positions and category dictionaries; no equality of data packets supplies the equation. |
| `α ≫ β = 𝟙 (U.obj A)` and `β ≫ α = 𝟙 K`, from the two computation inverse laws and the corresponding `first_inverse_*` theorems | Forward and backward observations retain their full, different domains and codomains. The selected `α` is not replaced by an identity map: `alpha_value` records its actual scaled coordinate. The unchanged whole-map assertions still judge returned computations. |
| The actual formed pairing, from `source_pairing` and `first_pairing` | The object result retains its full formed-module context and subsequent operation input. Preserving the carrier or one point would not preserve this field or discharge its existing full-pairing assertion. |
| Supplied `f : Y ⟶ X`, `g : U.obj Y ⟶ K`, and `U.map f = g ≫ i`, specialized by `cone_base_factorization` | `SelectedLift.factor` obtains the original `Y` from the complete cone and checks the compatibility proof. `captureLiftFactor` retains the existing construction, base map and cone as ordered operands. `completeRetainedLiftFactor` consumes those returned operands and the same parent's four actual fields. |
| `h ≫ j = f` and `U.map h ≫ α = g`, from `MonoLift.factor_hom` and `factor_map`, specialized by `formedMediator_factorization` and `formedMediator_comparison` | The returned factor's complete endpoints and its supplied construction are preserved for later composition/application. The applicable comparison square is exactly the supplied cartesian factor equation. No unprovided global natural isomorphism is inferred from a single comparison component. |
| Uniqueness, from `MonoLift.factor_unique` and `formedMediator_unique` | This remains a formal property of the selected construction. The computational factor port returns a map, not a proof, and the acceptance suite retains its independent factor observations. |

The object and map actions belong to the selected `Functor`; its identity and
composition laws belong to the formal input. The kernel keeps that same action,
the full source/target dictionaries and the declared map order through
`CategoryContext`, `SelectedLift`, retained callable endpoints and the positioned
service preparers. The common invocation driver adds no semantic action or
coherence law. Reusing a selected returned result is distinct from executing an
equal mathematical expression again, and equality of its representation is
distinct from equality of its denotation. The cache and producer controls test
that association, while the permanent mathematical assertions test the answers.

Successive lifts additionally require the original second-stage continuation
and the existing `MonoLift.factor_comp`/`computation_comp_*` laws with its changed
cone source. That later computation, other variance, and any additional higher
data are not established by the single-stage source argument or its build.

#### Remaining scope and evidence

The staged producer nodes bypass `Harness.results` through
`preparedLiftReference?`; this does not remove that cache from unmigrated readers
and observers. Universal constructions still schedule through
`observeStructuredInvocationWith`. Callable, structured-projection,
record-projection, routed, and prescribed protocols share canonical completion
but retain their existing dependency observers. The explicit `composed` lift
adapter still gathers recorded segments through `composedLiftExecution` and
`retainedLiftExecution`. `cacheLiftFields` remains on the prescribed path, and
`legacyLiftRecovery`/`executePrescribedLift` remain compatibility entry points.
None is counted as a completed scheduling migration by this direct lift change.

The first unchanged RX-LIFT computation, its comparisons and later factor use,
focused hostile controls, preservation review, and independent public-only trial
must be recorded with their actual results. Complete #24 inventories and the
remaining #66/#69 requirements still govern wider coverage. Source inspection,
private prospective data, and a successful build alone do not satisfy these gates.

<details>
<summary>Dated implementation notes preserved from the candidate branch</summary>

These notes describe the source and checks at their stated dates. Their present-tense
implementation descriptions are historical; the selected replacement above governs current work.

## V1 generic computational composition (2026-10-23)

Direct source searches for `ComputationPacket`, `dataProjection`,
`ComputationalValue.decode`, `PointInvocation`, `Functor.map`, and
`Cone.postcompose` locate the existing owners in the public contract,
`StructuredResult`, and Mathlib. The kernel reuses these declarations and the
registered `LimitEntry.dataConstructor`/`standardization` interfaces. It does
not select a mathematical shape or prove a leaf result's universal property.

New code composes retained input/output data, preserves live opaque ownership,
and interprets defining-map projections in the existing constructor schema.
Actual diagram inputs are retained before reducing categorical identities.
The public result envelope is unwrapped before complete construction validation
and projection; required cone fields remain visible. Presentation application
frames ordinary closed generators at its independently selected source and
forwards computed data with its original ownership.

### Composition invariants

`Wire.value` fixes the mathematical request. Its separate payload retains ordinary
input data, actual returned computational data, or a complete construction packet.
A computational result is cached under the exact closed expression that requested
it. A later occurrence reuses that payload; it does not evaluate the formal result
to manufacture an answer. Stopping the harness clears the cache and closes its
sessions, so an opaque token cannot survive as an ownerless value.

`forwardPayload` preserves computational status and ownership through a projection.
`combinedPayload` merges every operand and parameter dependency, including selected
endpoints. A composite with any computed dependency remains computed; two different
owning sessions cannot be silently combined. Applying these two rules inductively
covers nested point invocations, presentation changes, declared functor actions,
and defining-map compositions. These rules retain data dependencies; they do not
assert that the represented mathematical values are correct.

A callable invocation carries its exact registered declaration, ordered explicit
parameters, generalized domain, selected source and target, and argument data.
`realizeEndpoint` describes an input type without executing a construction merely
to name that type. A computed endpoint keeps its actual result payload. For an
ordinary product endpoint, the existing `objectProduct` descriptor preserves its
two independently declared factors. An explicit nonidentity action remains an
action in subsequent requests: extracting an inner named apex is permitted only
for the complete construction wrappers and their actual stored fields.

The source of a result projection is the accepted constructor schema. Original
constructor binder indices distinguish the returned apex, diagram objects, and
map endpoints before formal unification can make their expressions coincide.
`StructuredResult.DataProjection` is closed under field selection, retained input,
identity, composition, and registered map action. Its encoder substitutes actual
returned fields at those slots. Structural induction on that expression shows
that a projected composite consumes the same actual fields and input arrows as
its defining schema, including when two formal endpoints happen to be equal.
No shape-name dispatch or reconstructed canonical answer supplies a missing field.

A prescribed lift fixes all formal component signatures before execution. In
reverse route order, each four-field request prefix contains the actual preceding
outputs. `nextBase` forms the next step from the completed inclusion's actual
source, target, and callable. The packet validator checks the same recurrence and
retains every component and both comparison directions. Thus the induction step
uses the previous computed base, while the fixed formal plan independently
determines its type. A missing field is malformed; a missing registered component
is an implementation gap; a well-framed wrong component remains available for
independent mathematical comparison. The preferred complete `arrow` spelling and
legacy `subobject` spelling have the same fields at this fixed refined type.

Observation uses returned data. Plain closed values are decoded at their fixed
target and compared through the existing structural codec and kernel-checked
conditions. Ordinary point descriptors are decoded and evaluated at the registered
global point first. Computed values never substitute their retained formal terms
for returned data. Other equality observations select the uniquely applicable
registered equality characteristic map by its complete typed signature; absent
or competing declarations remain distinct failures. These source arguments need
the corresponding end-to-end execution and frozen independent extension trials;
they are not acceptance of a leaf or a mathematical release.

### Complete diagram callable context

The public `typedMap(source,target,callable)` form owns callable endpoint framing.
The existing limit execution already realizes both source endpoints and their
selected images under a creation functor for result validation. Retain those same
fields in every arrow of both the source diagram and the dispatched mapped
diagram, and include their data in ownership composition. Bare graph images do
not determine their codomain or its selected structure. No mathematical object,
comparison, graph algorithm, or shape-specific reconstruction is introduced.

### Reconstructed object and whole-morphism presentations (2026-10-24)

This source reconstructs mechanisms described in the conversation record; the
original commit bytes were unavailable. Direct source inspection located
`ObjectEntry.functorPresentation`, `ObjectFunctorPresentation.argument`, `.route`
and `.identification`, the existing object inclusion and power-object membership
families, and Mathlib's `Iso.hom`, `Iso.inv`, `Iso.symm`, `Iso.trans` and
`Functor.mapIso`. They own all mathematical objects and comparisons used here.
`ObjectPresentation` only instantiates and checks those accepted families at
their complete parameters. It introduces no semantic row or mathematical fact.

The recorded change does not establish that ordinary named objects were eagerly
executed. The reconstruction therefore keeps their declared descriptor dispatch
and consumes a functor presentation when its parameters contain actual computed
data. The selected functor result and every structural action survive; the named
semantic object remains independently fixed. The accepted comparison is retained
in both directions as `objectField` data at the original complete parameters.
Those selectors have the same owner in execution, typed framing and ordinary
decoding. Inclusions and membership reuse the actual parameter payloads, including
parameters already cached without a separate reader trace.

Whole-morphism composition uses the inverse domain comparison, the original
actual callable, and the forward codomain comparison, in that order. The middle
data are neither evaluated from the formal arrow nor restricted to a finite
graph. Comparisons whose endpoints happen to be definitionally equal remain
explicit. Endpoint, callable and selected action parameter dependencies are
combined with their exact occurrence scopes; distinct live opaque sessions
remain separate until a consuming operation requires a compatible implementation.
The internal framing marker prevents nested composition
from applying the same endpoint comparisons twice. Structural actions map both
comparison directions, and proof-refinement snapshots preserve them.

An unnamed endpoint of a complete callable uses the existing contract's
`morphismEndpoint` projection. This extracts its declared endpoint as data and
does not recover a carrier or law from an opaque answer. A complete returned
construction apex may similarly use an unnamed object descriptor, including a
product with an actual point inventory different from the formal universal
object. Framing checks its declared object type and defining-map interfaces;
it does not equate the returned representation with that formal object. The
category-wide receiver retains portable computational status or its live owner.
For a creation wrapper, its declared accepted lift supplies the action that fixes
the base-category parameters before this framing check. This uses only the
formal action's type; the returned anonymous apex remains the actual data and is
never replaced with that action's formal object.

The new engineering fixtures are in `CasAcceptance/Kernel`: they consume the
accepted units presentation and its inclusion/membership, both directions of the
accepted nonidentity polynomial comparison with opaque callable data, and an
anonymous wrong-sized but complete computational apex. They check protocol and
data flow, never a leaf's mathematical correctness. No permanent acceptance
assertion is changed.

### Generalized operation observation

Registry `validateOperation` fixes the owning object at the declaration's last
object argument before its declared numeral parameters. Whole-callable observation
uses that exact actual argument and its accepted complete category to select the
computational registration. The operation's result carrier does not replace that
owner: a ring or module operation has an underlying map of sets. Original parameter
data, generalized domain, input pairing and target remain the complete existing
`PointInvocation`, with all actual dependencies retained. The default engineering
probe uses an infinite-domain map and a real opaque process reply, so a finite
graph fallback or formal recipe alone cannot satisfy materialization.

`prepareOperationObservation` retains the original complete result's external
domain and target presentations. Stripping administrative wrappers identifies the
accepted operation declaration and its internal signature; an endpoint from that
signature can be definitionally equal to the original endpoint while lacking its
selected named or computed descriptor. The original generalized argument supplies
the domain data, the original complete result supplies the target data, and the
stripped declaration supplies the internal operation source. Full signature,
parameter and composition checks remain in place. Argument framing and reply
validation use the retained external endpoints, with every actual owner combined
through the existing dependency operation.

The 2026-10-25 diagnostic of the unchanged `WholeOperationObservationProbes`
isolated a target-presentation mismatch: the operation and domain matched, but a
selected endpoint became a `morphismEndpoint` of the stripped declaration. A
bounded check of the exact repaired helper passed every original control through
the existing dispatcher and result cache, with no imported artifact changes.
That copied-helper check does not test the integrated automatic dispatch path;
the unchanged production consumer remains the coordinated build check.

An owner can occur only as a parameter of that operation, without a standalone
trace node. The shared parameter encoder retains its actual registered object
action and ordered composition. Its source and each action parameter pass through
the same computed-data lookup before formal descriptor encoding. This supplies
the owner request without demanding a separate observation of the functor image,
and preserves live ownership contributed by an actual computed source. The
engineering control separately checks that an untraced action contains its cached
source data and owner instead of reconstructing the source's formal descriptor.

</details>

## Selected Hom contexts and captured forms (2026-10-29)

The inclusion endpoints belong to the complete context selected by the original
lift action. `liftOperand`, `retainedLiftStage` and `captureDirectLiftInvocation`
therefore use the existing `contextualMorphismEndpoints` reader, whose full
`CategoryContext.checkMorphism` validation remains in place. No reduced carrier
category or replacement inclusion supplies an endpoint.

Prospective and actual field/factor returns preserve the form of their canonical
invocation input; the prospective reader receives that authenticated stored wire.
An ordinary captured action likewise retains its original wire form after every
prospective branch and after actual completion. Building the same object's data
with a fresh action template does not choose another public operation address.
The existing action, category, formal-value, ownership and input-address guards
remain unchanged. New action construction continues to use its own template.
The action guard reports closure and typing failures separately to diagnose the
remaining failure without accepting any open or ill-typed selected application.

These corrections are reconstructed source after the local workspace restart.
At published kernel `695210`, the focused production build passes on the current
main dependencies. All ten unchanged first-stage RX-LIFT questions run, with no
passing result: six scalar-descriptor rejections, one unsupported negation request
and three budget timeouts. This source argument supplies no computational acceptance.

### Complete record projections and selected functor actions

`recordCompleteUniversalObject` projects a candidate's cone/cocone and apex through
Lean's public `Meta.mkProjection`, as `StructuredResult.dataPlan` already does.
`Lean/Meta/AppBuilder.lean` constructs this projection from the actual record's
type, universes and full parameters. Fresh `mkAppM` instance synthesis would ask
for `Category ?J` before the generic set-diagram candidate has been matched. The
original full-type/apex comparison still fixes the candidate, and all subsequent
closure, category, accepted-presentation, kernel and ambiguity checks remain.
No unmatched candidate is suppressed by exception handling or an exclusion list.

The ordinary functor consumer takes the literal whole action already retained in
the reader's object projection. `Semantic.objOf` embeds that completed action,
including its implicit dictionaries, and `FunctorActionData.objectAction?` reads
its two existing public projection forms. Execution checks the exact original
receiver occurrence and all ordered declaration parameters through the strict
whole-action validator. It keeps the extracted action itself: a registered
declaration presentation that validates a whole composite cannot replace that
composite's selected occurrence. Original image, endpoint type, target context,
capture and execution guards remain. Fresh elaboration from explicit parameters
alone is removed from this path; it discarded already selected implicit data.

Bounded diagnostics on the original first question confirm these source defects
and the preserved fields. They create no new mathematical input, leaf or acceptance
assertion; integrated execution still determines whether the first slice works.

The retained-parameter candidate path now uses the same literal-action rule. A
fresh category-morphism declaration and its original public functor projection
previously entered the exact candidate set as different expression arrays, despite
coming from the same source occurrence and route. The original recorded projection
already supplies the whole action. Its receiver, registered edge and explicit
parameter occurrences are checked before retaining that action; neither a fresh
declaration nor the validator's presentation replaces it. The existing complete
prefix/result checks, kernel checks, exact duplicate handling and ambiguity remain.
This removes a reconstruction-induced distinction rather than identifying arbitrary
actions by their values or by definitional equality. Missing literal source data
remains an error at its producer boundary.

Preservation is literal at the changed boundary: the original receiver must occur
inside the parameter and equal the object projection's receiver; the complete
registered edge and ordered explicit arguments must equal the trace selections;
the candidate stores the original action, not `RegisteredAction.application`.
The unchanged exact receiver/route/application-array comparison therefore still
distinguishes identity from identity composed with identity, even when whole-action
validation accepts both. Existing complete-prefix, original-result and kernel
checks still reject an unrelated image. The current service projection controls
exercise distinct occurrences and explicit references, full endpoint roles, and
wrong-row/changed-diagram refusal; the complete universal-object controls exercise
the full structure and owner boundary. Both targets pass on `695210`. Their scope
is engineering preservation, not universality or correctness of a leaf's answers.

The missing-node literal-action path already retains the selected component applications
in `transportImage`. Its descriptor callbacks now pass that same complete application to
`realizedEdgeData` / `capturedEdgeData`, as their strict whole-action checks require. The
literal declaration application remains the independently checked source of ordered parameters;
it is not substituted for the functor at the checker boundary. This corrects a raw `Cat.Hom`
versus projected `Functor` argument mismatch without changing selected actions, receivers,
routes, parameter-consistency checks or ambiguity. The existing nested/composed source-owner
control remains unchanged and is the direct regression for this path.

At published `e03ad05e`, the focused production build and the full existing
`ReducedParameterActionProbes` target pass. The two adapted fixture setups retain exact source
data/owner and wrong-dictionary checks; the nested/composed control itself is unchanged.
The original ten-question runtime against independently authored public-contract adapter
`d4a92aa8` still has no passing assertion. Four questions now receive multiplication data and
then fail the intrinsic callable's exact complete-endpoint check; the nonidentity coordinate
has an unavailable negation implementation, three later evaluations exhaust their budgets,
and both factor samples exhaust preparation. A successful backend reply is not a completed
kernel result. The complete occurrence/presentation check stays at its current boundary;
the next diagnosis must identify differing retained fields before changing their producer.

The bounded first-question diagnostic on `0996bc04` identifies a `typedMap` around an intrinsic
`powerObjectMap`. Its source advances through its original classifier-forget action to a private
prospective reference, while the bare field callable retains the old source recipe. Full formal
value, form/category, owner table and observation flags agree; the packet and producer payload
differ. The reference is still a private unsupplied recipe, so this does not show it crossing an
execution boundary. The `powerObjectMap` branch had rendered parameters without retaining their
typed producer template or the callable's own endpoint relation.

That branch now checks its already selected field declaration and complete original application,
including ordered typed parameters, and retains those parameters through
`capturedCallableParameters`. It renders the same public descriptor and captures the original
complete endpoints at this initial producer boundary. Its intrinsic assembly subsequently observes
both the parameter slots and those exact endpoint actions; no changed cache or equal packet supplies
a replacement. The original complete Hom check, object endpoint demand and outer exact occurrence
guard remain. Power fields acquire no new operation address or mathematical implementation.
