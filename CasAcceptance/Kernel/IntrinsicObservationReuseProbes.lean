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
    logInfo "PASS: original intrinsic observations retain one actual result and preserve occurrence, phase and ownership boundaries"
  finally harness.stop

end
end CasCatalogue.IntrinsicObservationReuseProbes
