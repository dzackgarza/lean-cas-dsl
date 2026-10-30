/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for repeated actual observation of an original
intrinsic producer. The existing regular-module constructor retains its exact
ring parameter, whose existing registered action returns arbitrary owned data.
These checks concern producer identity, input retention and session lifecycle;
the protocol witness supplies no mathematical answer. -/

open Lean Meta Elab Term
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.IntrinsicObservationReuseProbes
meta section

private def unavailable (action : TermElabM α) : TermElabM Bool := do
  try
    discard action
    return false
  catch error => return Exception.stratum? error == some .unavailable

private def exactResult (first second : Wire) : Bool :=
  sameCompleteWireContext first second && first.serviceHandles == second.serviceHandles

run_elab do
  let state ← registryState
  let some sourceRow := state.objects.find? (·.id.raw == "obj.commutative_rings.rationals")
    | throwError "the intrinsic reuse control lost its accepted source object"
  let some action := state.functors.find? (·.id.raw == "fun.commutative_rings.ring")
    | throwError "the intrinsic reuse control lost its accepted parameter action"
  let some regular := state.objects.find? (·.id.raw == "obj.modules.regular")
    | throwError "the intrinsic reuse control lost its accepted constructor"
  let trace ← Trace.new
  let source ← Semantic.object sourceRow #[] (some trace)
  let (ring, _) ← Semantic.applyRegisteredFunctor action source #[] (some trace)
  let formal ← ObjectPresentation.applyParameters regular.declaration #[ring]
  let node : Node := .object regular.id #[ring]
  let firstProducer ← Trace.recordProduced (some trace) formal node
  let secondProducer ← Trace.recordProduced (some trace) formal node
  Trace.checkProducerRecord firstProducer node
  Trace.checkProducerRecord secondProducer node
  unless firstProducer != secondProducer &&
      Trace.unanchor firstProducer == Trace.unanchor secondProducer do
    throwError "the intrinsic reuse control did not retain distinct equal-formal producers"
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "intrinsic-reuse-probe", command := "python3",
      args := #["probe_functor_execution.py", "action", action.id.raw, "--opaque-objects"] }]
    registrations := #[{
      operation := action.id.raw, input := action.inputAddress, backend := "intrinsic-reuse-probe" }] }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  let harness := { harness with dispatches := some calls }
  unless harness.rejected.isEmpty && harness.admitted.size == 1 do
    throwError "the existing intrinsic parameter action was not admitted"
  try
    let first ← realizeUnobserved harness trace "the original intrinsic object" firstProducer
    let second ← realizeUnobserved harness trace "the distinct intrinsic object" secondProducer
    let some assembly ← retainedIntrinsicAssembly? first .object
      | throwError "the ordinary constructor lost its original typed parameter assembly"
    unless !first.actualData && (← calls.get).isEmpty do
      throwError "capturing the original intrinsic object executed its parameter action"

    -- Private admission sees the same selected producer but cannot install an
    -- actual completion or allocate operands in the live execution owner.
    let beforeInvocations ← harness.invocations.get
    let beforeOperands ← harness.serviceOperands.get
    let inspect ← Harness.empty
    inspect.connections.set (← harness.connections.get)
    inspect.results.set (← harness.results.get)
    inspect.serviceOperands.set beforeOperands
    let privateTrace ← IO.mkRef (← trace.get)
    discard <| prospectiveOwnerData harness inspect privateTrace first
    unless (← harness.invocations.get).size == beforeInvocations.size &&
        (← harness.serviceOperands.get).size == beforeOperands.size &&
        (← harness.actions.get).isEmpty && (← harness.replies.get).isEmpty &&
        (← calls.get).isEmpty do
      throwError "private intrinsic inspection populated a live execution owner"

    -- Restricted observation cannot supply an unrestricted canonical receipt.
    -- Nested children may complete, but the outer selected producer has not
    -- undergone the unrestricted observation policy.
    let restricted ← observeIntrinsicAssembly harness trace first assembly true
    unless !(← harness.invocations.get).any (·.input.value == firstProducer) do
      throwError "restricted intrinsic observation installed an unrestricted producer receipt"
    let observed ← realizeObjectObservation harness trace first
    let receiptCount := (← harness.invocations.get).size
    let reused ← realizeObjectObservation harness trace first
    unless observed.fragment == restricted.fragment && exactResult observed reused &&
        !observed.serviceHandles.isEmpty && !observed.ownership.isEmpty &&
        (← calls.get).size == 1 && (← harness.invocations.get).size == receiptCount do
      throwError "re-reading one original intrinsic producer replaced its actual result or retained handles"

    -- The owner reference reuses the same completion without accepting another
    -- supplied body. A different preparation table cannot borrow that reference,
    -- even while all of its actual suppliers remain live.
    let some prepared ← currentIntrinsicInvocationReference? harness trace first
      | throwError "the original intrinsic producer lost its canonical preparation"
    unless exactResult observed (← observePreparedInvocation harness trace prepared) &&
        (← calls.get).size == 1 && (← harness.invocations.get).size == receiptCount do
      throwError "the canonical reference replaced its result or repeated its computation"
    let foreign ← Harness.empty
    foreign.connections.set (← harness.connections.get)
    foreign.serviceOperands.set (← harness.serviceOperands.get)
    try
      unless ← unavailable (observePreparedInvocation foreign trace prepared) do
        throwError "another harness borrowed a canonical preparation from its live owner"
      unless (← foreign.invocations.get).isEmpty && (← calls.get).size == 1 do
        throwError "foreign canonical observation installed a preparation or dispatched computation"
    finally foreign.connections.set {}

    -- A real returned action packet remains completed data even if a caller
    -- attaches an intrinsic description and requests another preparation.
    let some actionResult := (← harness.actions.get).find? (·.operation == action.id.raw)
      | throwError "the intrinsic parameter lost its actual action completion"
    let completed := { actionResult.result with capturedInvocation := none }
    unless completed.completedData do
      throwError "the completed-input control did not use an actual returned packet"
    let some completedContext := completed.categoryContext
      | throwError "the actual returned object lost its complete category"
    let completed ← retainIntrinsicAssembly completed .object completedContext
      (.literal completed.fragment)
    let some completedAssembly ← currentIntrinsicAssembly? completed
      | throwError "the completed-input control lost its checked description"
    let replay ← captureInvocation harness completed (.intrinsic completedAssembly)
    unless ← unavailable (observePreparedInvocation harness trace replay) do
      throwError "a canonical reference replayed actual received data as a pending computation"
    let replayRecords := (← harness.invocations.get).filter (·.prepared.same replay)
    unless replayRecords.size == 1 && replayRecords.all (·.result.isNone) &&
        (← calls.get).size == 1 do
      throwError "completed-input rejection installed a completion or dispatched computation"

    let separate ← realizeObjectObservation harness trace second
    unless separate.fragment == observed.fragment &&
        separate.serviceHandles != observed.serviceHandles &&
        (← calls.get).size == 1 do
      throwError "distinct intrinsic producers merged through equal formal values or portable data"

    -- Equal payloads and formal values do not authorize replacing a captured
    -- child occurrence. The same outer anchor with different retained input
    -- handles must not borrow the earlier complete observation.
    let changedTemplate ← mapActionTemplateWires (fun _ child => do
      let handles ← retainServiceOperands harness #[child]
      pure { child with serviceHandles := child.serviceHandles ++ handles }) assembly.template
    let changed ← retainIntrinsicResultAssembly first assembly.result changedTemplate
      assembly.maps assembly.equalObjects assembly.endpointRoles
    let some changedAssembly ← retainedIntrinsicAssembly? changed .object
      | throwError "the changed-input control lost its complete intrinsic assembly"
    let beforeMismatch ← harness.invocations.get
    unless ← unavailable (observeIntrinsicAssembly harness trace first changedAssembly) do
      throwError "an intrinsic observation accepted another supplied assembly's child occurrences"
    unless (← harness.invocations.get).size == beforeMismatch.size && (← calls.get).size == 1 do
      throwError "a mismatched intrinsic assembly allocated an invocation or dispatched computation"
    unless ← unavailable (captureInvocation harness first (.intrinsic changedAssembly)) do
      throwError "generic capture accepted another intrinsic assembly's retained child occurrences"
    unless (← harness.invocations.get).size == beforeMismatch.size && (← calls.get).size == 1 do
      throwError "mismatched intrinsic capture allocated an invocation or dispatched computation"
    let changedResult ← realizeObjectObservation harness trace changed
    unless changedResult.fragment == observed.fragment &&
        changedResult.serviceHandles != observed.serviceHandles &&
        (← calls.get).size == 1 do
      throwError "intrinsic reuse ignored a changed retained child occurrence"
    unless exactResult observed (← realizeObjectObservation harness trace first) do
      throwError "another intrinsic preparation replaced the original completed receipt"

    -- A completed observation remains owned by its actual live supplier even
    -- when reuse would otherwise avoid every computational dispatch.
    let connections ← harness.connections.get
    harness.connections.set {}
    try
      unless ← unavailable (realizeObjectObservation harness trace first) do
        throwError "an intrinsic observation receipt revived an unavailable owner"
      unless (← calls.get).size == 1 do
        throwError "expired intrinsic data were dispatched before owner rejection"
    finally harness.connections.set connections
    harness.stop
    unless (← harness.invocations.get).isEmpty do
      throwError "stopping the harness retained an intrinsic observation receipt"
    unless ← unavailable (observePreparedInvocation harness trace prepared) do
      throwError "a canonical reference revived a stopped preparation scope"
    unless (← harness.invocations.get).isEmpty && (← calls.get).size == 1 do
      throwError "a stopped canonical reference installed a receipt or dispatched computation"
    logInfo "PASS: original intrinsic observations retain one actual result and preserve occurrence, phase and ownership boundaries"
  finally harness.stop

end
end CasCatalogue.IntrinsicObservationReuseProbes
