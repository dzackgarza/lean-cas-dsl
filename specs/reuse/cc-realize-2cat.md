# Reuse record: `cc-realize-2cat`

## Engineering notes for the work issues

The current architectural direction is recorded in
[#85](https://github.com/dzackgarza/lean-cas-dsl/issues/85). Interpretation work is in
[#66](https://github.com/dzackgarza/lean-cas-dsl/issues/66), execution work in
[#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69), and the delivery sequence and
acceptance obligations in [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10).
This file records technical analysis and reuse evidence for those issues, alongside
[`cc-dsl-language`](cc-dsl-language.md). It does not set a separate work order or change
their instructions.

The boundary described in #85 preserves a selected construction, its typed dependencies,
actual returned data and later use together. A canonical execution store alone would leave
the reconstruction pipeline intact if its reader, lowering or completion paths continued
to infer omitted mathematical structure.

## Owner

`lean-categories` owns the selected mathematical constructions, presentation denotations,
functors, comparisons, lifts and their ordinary or higher laws. Mathlib supplies ordinary
categorical APIs, including `Functor`, commuting squares and their pasting, and `Cat` as a
strict bicategory. These do not replace higher data required by CC-HIGHER or justify an
otherwise unsupported strict reduction.

The kernel owns computational lowering, request/reply interfaces, dependency execution and
validation of untrusted returned data. A leaf supplies an opaque computation for an already
declared operation and form. It supplies no mathematical denotation, universal property,
comparison proof or evidence of its own correctness. Independent permanent acceptance
judges its answers.

## Queries

The September 29 queries in [`cc-cells.md`](cc-cells.md) and October 20 searches for
`presentation element structural encoding` and `selected object computational form`
are preserved in the
[immutable pre-replacement record](https://github.com/dzackgarza/lean-cas-dsl/blob/0cee529c343fbe1c5f7a5f1326d4b805cc8fed44/specs/reuse/cc-realize-2cat.md).
The recorded results did not supply this kernel's wire protocol. They do not justify
retaining a protocol that needs to infer omitted mathematical structure.
The [PR #67 execution record](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/specs/reuse/cc-realize-2cat.md)
preserves subsequent investigations, controls and recorded engineering evidence.

The broader sources are the
[#79 library survey](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6475309126),
[cross-repository source research](cross-repository-execution-prior-art.md), and
[#85 prior-art assessment](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6570686947).
These contain historical implementation assessments as well as source findings. Their
candidate mechanisms are examined below for fit to the boundary in #85, without assuming
the old invocation owner or a package disposition.

## New code: execution of a complete dependent computation

This engineering analysis develops the boundary in #85 and the dependent computation and
result-use obligations in #66/#69.

The replacement carries the formal selected application and its executable description
together. Ordinary term formation uses Lean elaboration as recorded in
[`cc-dsl-language`](cc-dsl-language.md). Mathematical route, structure, comparison, admission
and lifting choices remain explicit inputs. Dependency scheduling cannot choose or repair
those choices.

A completed description fixes each operand occurrence, dependency, dependent result field,
and required operation on that field. For a construction returning an apex and inclusion,
the inclusion's source is the same returned apex, and a later factor lands in that apex.
Those bindings are prescribed before the answer exists. Completion validates and binds the
actual supplied fields in those positions; it does not infer a selected construction from
their encodings. The associated accepted formal cone and its laws remain distinct from
the untrusted computational packet.

Composition must preserve this association through projection, substitution, comparison,
reindexing, lifting and later public calls. Reusing a result, evaluating a definition at its
use and deliberately executing a new occurrence are distinct. Equal Lean expressions or
equal JSON are not sufficient to identify actual producers. Administrative allocation
differences must not alter the mathematical question. A new execution supplies its own
dependent maps, or an accepted comparison and actual transport connect the results.

The 2026-11-02 source research resolves the representation/import decision in [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69#complete-typed-computation-resolved-implementation-decision): cslib `PFunctor.FreeM` and compatible PolyFun `Handler.Stateful`/`Cursor`, instantiated by complete prepared request and dependent response families. The ordinary response family can bind an actual apex and maps over it; a new static changing-world calculus is not required merely because a result is dependent. Existing invocation/plan records are not mandatory survivors. Combined import/build, unchanged RX-LIFT execution and independent public use are still unperformed integration evidence.

Lazy demand, adequate fused realizations, admitted portable/opaque presentations and actual
supplier/session checks are compatible with this boundary. A fused realization need not dispatch every formal
primitive. Formal functoriality does not prove arbitrary backend calls pure, repeatable or
correct. An opaque reference obtains callable behavior only through the declared public
operation or admitted bridge; a label change supplies no morphism action.

### Existing implementation evidence and reusable responsibilities

The candidate source anchor is
[`b35ab54`](https://github.com/dzackgarza/lean-cas-dsl/tree/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1).
It supplies evidence and possible reusable components, not an accepted architecture.

| Responsibility | Existing source | Preservation property and reuse limit |
| --- | --- | --- |
| Formal construction versus computational answer | [`StructuredResult.Result`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/StructuredResult.lean#L92-L118) | Preserve the independent formal construction and the untrusted packet. The reply does not supply universality or an identification with the formal apex. The record layout may change. |
| Dependent field positions and input roles | [`StructuredResult.DataPlan`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/StructuredResult.lean#L128-L162) and [`validatePlannedData`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/StructuredResult.lean#L329-L349) | Preserve dependent constructor roles before formal equality can merge distinct inputs and returned fields. Reuse validation against a fixed schema where it fits; current reflective preparation and callers are subject to replacement. |
| Routed fields, selected lift and ordered outputs | [`RoutedResultPlan`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/RoutedResultPlan.lean), [`SelectedLift`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/SelectedLift.lean), [`LiftStageExecution`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/LiftStageExecution.lean) | Preserve the complete chosen lift, field dependencies, comparisons and factor use. Assess each operation against direct result references; do not retain the current plan representation or fold merely because it exists. |
| Explicit comparison action | [`CellAction`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/CellAction.lean) | Preserve actual components, orientation, endpoints and required compatibility. A route quotient, carrier equality or order-based representative cannot replace the supplied action. |
| Public and derived requests | [`ServiceRequest`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/ServiceRequest.lean), [`UniversalServiceRequest`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/UniversalServiceRequest.lean), [`ComputationDerivation.compileAt`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/ComputationDerivation.lean#L307) | Transfer these entrances to the same complete lowering boundary. Preserve their public meaning, admission and failure behavior. A prepared service or instruction that calls legacy recognition is not the replacement. |
| External data, owners and lifetime | [`DataOwnership`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/DataOwnership.lean), [`StagedNumeralDataProbes`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasAcceptance/Kernel/StagedNumeralDataProbes.lean#L59-L126), [`ContextualHomFramingProbes`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasAcceptance/Kernel/ContextualHomFramingProbes.lean) | Preserve validation at actual receive/capture and use boundaries, positioned multi-owner data, exact endpoints and rejection in foreign or expired sessions. Do not replace those controls with fabricated ownership metadata. |
| Distinct occurrences and stable question meaning | [`ProducerOccurrenceProbes`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/ProducerOccurrenceProbes.lean#L29-L179) | Preserve selected producer/operand distinctions and independence from anonymous allocation history. Migrate the controls to replacement references; producer wrappers inside Lean expressions are not a required representation. |

### Source decisions resolved on 2026-11-02

The [positive specification](https://github.com/dzackgarza/lean-cas-dsl/issues/10#specification-and-fundamental-invariants) determines the required behavior. [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69) records the implementation decision and exact first-construction/wire/lifecycle mapping. This table records the inspected technical basis and limits; it is not a second work order.

| Source | Inspected API and selected use | Limit |
| --- | --- | --- |
| [cslib v4.33.0, 3951377e5a3f5772737f11cd62bc5bb6a72f95d1](https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean) | Import `PFunctor.FreeM`, dependent `P.B request` continuations and `liftM`; its polynomial interface avoids the unnecessary existential-universe bump of `Cslib.FreeM` for this already declared signature. | Sequencing laws supply neither mathematical selection nor interface/owner validation or backend correctness. |
| [PolyFun v4.33.0, a5895e454254a400774fa396b64d5b968f0933df](https://github.com/Verified-zkEVM/PolyFun/tree/a5895e454254a400774fa396b64d5b968f0933df) | Import [`Handler.Stateful`](https://github.com/Verified-zkEVM/PolyFun/blob/a5895e454254a400774fa396b64d5b968f0933df/PolyFun/PFunctor/Handler/Stateful.lean): a transparent StateT handler with run/reindex and fusion law over cslib's program. [`Cursor`](https://github.com/Verified-zkEVM/PolyFun/blob/a5895e454254a400774fa396b64d5b968f0933df/PolyFun/PFunctor/Free/Cursor.lean) retains a typed prefix/residual where suspension is needed. | Cursor constructors are structural evidence, not real receipt, live ownership or exactly-once I/O. The newer HandlerMachine.Phase/runPrefix/result is absent from this release and is not a required port. |
| PolyFun [indexed free family](https://github.com/Verified-zkEVM/PolyFun/blob/a5895e454254a400774fa396b64d5b968f0933df/PolyFun/IPFunctor/Free/Family.lean) | Researched and not needed for the present contract: it changes a static state index after responses. | Actual dependent fields are already expressed by ordinary response families; runtime session validity is still checked. |
| [Lean ordinary term/context APIs](cc-dsl-language.md) | Complete selected application, dependent binding and closure in Lean before executable lowering. | An expression or escaping local identifier is not an actual result occurrence. |
| [CAP supplied-object/factor API](https://github.com/homalg-project/CAP_project/blob/fb48c41c311723abe12f24ef67c814f12d000322/CAP/gap/MethodRecord.gi#L285-L361) and [derivations](https://github.com/homalg-project/CAP_project/blob/fb48c41c311723abe12f24ef67c814f12d000322/CAP/gap/DerivedMethods.gi#L184-L193) | Apply its discipline that later defining maps/factors consume the supplied actual apex; appropriate algorithms remain leaf-only. | No GAP kernel dependency, mathematical route selection by cost/order, or unsupported universal property. |
| [GATlab explicit models/indices](https://github.com/AlgebraicJulia/GATlab.jl/blob/0944af7765b404c97f92b9909a56bb2535146caf/src/stdlib/models/finsets.jl), [Aldor dependent result contexts](https://www.aldor.org/docs/HTML/chap7.html), [ConCat host-program translation](https://conal.net/papers/compiling-to-categories/) | Design evidence for explicit selected inputs, dependent returned context and lowering after host typing. | No second mathematical registry, external language runtime, or general compiler project; their source theories do not prove this dependent/higher untrusted-backend boundary. |
| [ITree](https://github.com/mit-plv/lean4-itree/blob/main/ITree/Basic.lean), [Lean IR](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Compiler/IR/Basic.lean), [Lean-MLIR](https://github.com/opencompl/lean-mlir/blob/b8c4a771319a044854a4bbb49b8821381ef86ff8/LeanMLIR/LeanMLIR/Framework/Basic.lean) | No import/adaptation selected for this responsibility: whole-service coinduction is unnecessary; erased IR loses mathematical indices; the inspected dialect signatures are not value-dependent result telescopes. Normal Lean compilation remains available. | These are responsibility-based dispositions, not blanket rejection based on a latest toolchain version. |

Both selected releases declare Lean/mathlib v4.33.0, and PolyFun requires cslib v4.33.0. The earlier inspection of newer v4.35/v4.36 sources did not establish absence of a compatible release. This resolves the source-selection question while leaving the actual combined dependency closure/build and original mathematical result as implementation evidence. The prior mandatory local adaptation/no-package direction is superseded by the owning issues.

The project-specific residue is the prepared computational interface, public wire lowering and actual receive/use lifecycle. #69 specifies a native checked view whose maps depend on the actual returned object and image references, not only on an opaque request label. Formal closed terms remain distinct from untrusted computational data. Only the receive boundary creates ready views after checking the fixed framing, roles, dependency positions, endpoints, owner coverage and supplying session. A private constructor or a schema tag alone proves none of the mathematical answer.

For the unchanged first RX-LIFT, actual X1 crosses to hom; X1 and its inclusion cross to forward; the retained prefix and actual comparison image cross to backward; factor receives all four outputs and typed g/f with their owners. Forward can supply its image endpoint and comparison together, so the plan introduces no unnecessary primitive image requirement. Legacy missing-image recipe framing does not serve the migrated path.

The runtime handler consumes prepared dependencies, dispatches, receives/validates and publishes actual bindings, and preserves the existing failure distinctions. Its executable dependencies exclude semantic reconstruction callbacks, including service/derived entrances. Lazy demand, adequate fused realization, fresh evaluation and declared restoration remain separate. Public later-use sessions retain their owners across calls; the old one-shot #cas harness, stopped per command, cannot implement that lifetime. #68 specifies the actual public-session adapter, and #24 retains independent completion.

### Native notebook inspection and recovery

[#69's source-verified notebook boundary](https://github.com/dzackgarza/lean-cas-dsl/issues/69#native-notebook-query-and-recovery-boundary) resolves an additional effect entrance: current worker inspection elaborates whole cells, and the frontend can initialize/replay a worker or missing prefix. The selected bounded change is a proposed explicit session policy for CAS kernels plus environment-only mode on the existing inspect operation. It reuses the worker's committed-environment Query.inspect, checks protocol compatibility before sending source, and performs no CAS execution or recovery while answering queries. Native CAS execution uses non-ledgered calls and explicit fresh/restored state; missing predecessor state is unavailable until explicit reexecution or valid complete restoration. The current replay behavior remains available for separately configured notebooks with pure definitions.

[#68](https://github.com/dzackgarza/lean-cas-dsl/issues/68) separately specifies the public facade's open/use/close adapter, one Environment-backed result authority, resource-only liveness/reservations, snapshot-fork freshness and stale-owner checks. Its current WorkerClient execution/lifecycle APIs suffice; the new native inspection mode and frontend configuration are not claimed present. [#24](https://github.com/dzackgarza/lean-cas-dsl/issues/24) retains real notebook verification of these boundaries with the unchanged mathematical workflows. This source research does not claim a live reproduction or runtime acceptance.

### Fixed-interface validation and reconstruction

Untrusted answers still require decoding and checks for shape, complete dependent fields,
declared endpoints, resource/lifetime restrictions, owners and session compatibility.
Validation consumes the already selected schema and bindings. It does not choose the
mathematical result from registry candidates or treat decoding as proof of the answer,
universality or a comparison. Invalid input, ambiguity, missing implementation, unavailable
execution, malformed data, wrong answer and internal failure have distinct meanings;
timeout is not a semantic rejection.

The current
[`realizeFreshWith` recovery branches](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/Realize/RuntimeSupport.lean#L14620-L14679)
and [`recordCompleteUniversalObject`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/Realize/RuntimeSupport.lean#L3648-L3705)
show the boundary to remove: execution searches expressions and registry entries to restore
a selected action or construction, then checks its reconstruction. Retaining these behind
a canonical store, renamed instruction or wrapped callback fails the replacement.

Recovery of selected inputs or results by unanchored expression/packet matching, alternate
completion paths and copied contexts used to repair a missing interface are further forms
of that mechanism. Keeping them as fallbacks would leave the boundary incomplete. Necessary
validation has a different input: the already fixed interface and its dependent bindings.
A genuinely staged new public request may elaborate at its own complete preparation
boundary; it does not need to repair an incomplete existing request during execution.
The same distinction applies at notebook/DSL, public-service and derived-computation entrances.

### Evidence linked from the work issues

Implementation evidence for [#66](https://github.com/dzackgarza/lean-cas-dsl/issues/66) and
[#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69) can identify the actual typed
interface, reuse and dependency decisions, removed recovery paths, validation boundary,
and preservation of supplied results through later use. Execution results and their
acceptance scope belong with those work issues and
[#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10). Historical source records remain
available through the links above; neither they nor this analysis establish a current
compilation, performance or acceptance verdict.
