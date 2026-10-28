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
