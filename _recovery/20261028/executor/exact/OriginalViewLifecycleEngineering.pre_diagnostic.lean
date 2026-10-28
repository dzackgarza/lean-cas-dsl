/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering control for explicit views of one selected producer. The
existing complete Fin callable and protocol-only session fixture fix the formal
interface and provide arbitrary opaque tokens. No token is a mathematical
answer or evidence about the selected map. The checks concern occurrence
sharing, public data projections, dispatch count and supplying-session lifetime.
No semantic registration or protected mathematical assertion is changed. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

namespace CasCatalogue.OriginalViewLifecycleEngineering
meta section

private def unavailable (label : String) (action : TermElabM Wire) : TermElabM Unit := do
  let rejected ← try
    discard action
    pure false
  catch error =>
    if Exception.stratum? error == some .unavailable then pure true else throw error
  unless rejected do
    throwError m!"the {label} view reused an expired supplying session"

private def invalid (label : String) (action : TermElabM Wire) : TermElabM Unit := do
  let rejected ← try
    discard action
    pure false
  catch error =>
    if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do
    throwError m!"the {label} view changed its independently fixed declaration interface"

/-- Either released whole-callable framing retains the same actual body. This
reader opens only public transparent and typedMap envelopes, including their
positioned ownership. It never decodes or evaluates the opaque function. -/
private partial def callableBody (data : DataOwnership.Data) : TermElabM DataOwnership.Data := do
  let some payload := ComputationalData.recordPayload? data
    | throwError "the view control lost its transparent data envelope"
  if let .ok ("typedMap", #[_, _, _]) := ComputationalData.envelope payload.json then
    return ← callableBody (← checkedFragment
      (payload.project #[.field "args", .index 2]))
  return payload

run_elab do
  let state ← registryState
  let some row := state.morphisms.find? (·.id.raw == "mor.sets.fin_rev")
    | throwError "the view control lost its existing complete callable"
  let some sets := state.categories.find? (·.id == row.category)
    | throwError "the view control lost the callable's declared category"
  let trace ← Trace.new
  let raw ← elabTermAndSynthesize (← `($(mkCIdent row.declaration) 4)) none
  let formal ← Semantic.namedMorphismProduced row raw (some trace)
  let independent ← Semantic.namedMorphismProduced row raw (some trace)
  unless formal != independent && (← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType formal) (← inferType independent) <&&>
        isDefEq formal independent)) do
    throwError "the control requires two separate producers of the same full callable"
  let some (source, target) := homEnds? (← inferType formal)
    | throwError "the view control lost its independently fixed whole Hom"
  discard <| Semantic.recordNamedObject source (some trace)
  discard <| Semantic.recordNamedObject target (some trace)
  let context ← CategoryContext.ofNamed sets source
  CategoryContext.checkMorphism context formal source target

  let sameValue ← mkAppM ``id #[formal]
  let firstView ← Trace.aliasProduced (some trace) formal sameValue
  let secondView ← Trace.aliasProduced (some trace) formal sameValue
  unless firstView != secondView &&
      (← trace.node? firstView) == some (.valueView formal) &&
      (← trace.node? secondView) == some (.valueView formal) do
    throwError "the control's distinct views lost their one exact original producer"

  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "session-probe", command := "python3",
      args := #["probe_owned_callable.py", "--materialize-invocation", row.id.raw] }]
    registrations := #[{
      operation := row.id.raw, input := row.id.raw, backend := "session-probe" }] }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  let harness := { harness with dispatches := some calls }
  unless harness.rejected.isEmpty && harness.admitted.size == 1 do
    throwError "the view control changed the existing complete-callable registration"
  try
    -- Prepare both views before the original or either result is demanded.
    let first ← realizeUnobserved harness trace "the first view" firstView
    let second ← realizeUnobserved harness trace "the second view" secondView
    let original ← realizeUnobserved harness trace "the original selected callable" formal
    let separate ← realizeUnobserved harness trace "the independent selected callable" independent
    let some firstCapture ← retainedCapturedInvocation? first
      | throwError "the first view lost the original pending invocation"
    let some secondCapture ← retainedCapturedInvocation? second
      | throwError "the second view lost the original pending invocation"
    let some originalCapture ← retainedCapturedInvocation? original
      | throwError "the original callable lost its prepared invocation"
    let some separateCapture ← retainedCapturedInvocation? separate
      | throwError "the independent callable lost its prepared invocation"
    unless first.value == firstView && second.value == secondView &&
        firstCapture.occurrence == originalCapture.occurrence &&
        secondCapture.occurrence == originalCapture.occurrence &&
        separateCapture.occurrence != originalCapture.occurrence do
      throwError "views duplicated their producer or merged an independent equal producer"
    unless (← calls.get).isEmpty do
      throwError "preparing a retained view dispatched a computation"

    -- The demanded function type independently fixes the one-data-field path.
    -- Capture it while its original whole callable is still pending.
    let expected ← mkArrow source target
    let some projections ← DeclaredAdmission.projectionPath? (← inferType firstView) expected true
      | throwError "the Sets Hom lost its declared function-valued data projection"
    unless !projections.isEmpty do
      throwError "the control no longer exercises a change of complete result type"
    let projected := projections.foldl (fun value projection =>
      mkProj projection.structureName projection.field value) firstView
    let valueView ← Trace.recordProduced (some trace) projected
      (.dataFieldView firstView expected (projections.map fun projection =>
        (projection.structureName, projection.field)))
    let parameter ← realizeUnobserved harness trace "the pending function-valued projection" valueView
    let some (.value selectedType) ← retainedValueResultInterface? parameter
      | throwError "the function projection lost its independently fixed value role"
    unless ← withoutModifyingState (withTransparency .all <| isDefEq selectedType expected) do
      throwError "the function projection changed its complete demanded type"
    unless parameter.categoryContext.isNone && parameter.callableEndpoints.isNone &&
        !parameter.completedData && (← calls.get).isEmpty do
      throwError "capturing a data projection copied a map role or executed its original"

    let fields := projections.map fun projection => (projection.structureName, projection.field)
    let wrongFields := fields.mapIdx fun index (name, field) =>
      (name, if index == 0 then field + 1 else field)
    let wrongPath ← Trace.recordProduced (some trace) projected
      (.dataFieldView firstView expected wrongFields)
    invalid "changed record path"
      (realizeUnobserved harness trace "the changed record path" wrongPath)
    let wrongType ← Trace.recordProduced (some trace) projected
      (.dataFieldView firstView (mkConst ``Nat) fields)
    invalid "changed demanded type"
      (realizeUnobserved harness trace "the changed demanded type" wrongType)
    unless (← calls.get).isEmpty do
      throwError "a malformed formal data projection dispatched its original callable"

    let actualFirst ← realizeArrowObservation harness trace first
    let actualSecond ← realizeArrowObservation harness trace second
    let actualOriginal ← realizeArrowObservation harness trace original
    let some owner := actualFirst.owner?
      | throwError "the actual callable lost its supplying session"
    unless actualFirst.value == firstView && actualSecond.value == secondView &&
        actualOriginal.value == formal && actualFirst.completedData &&
        actualFirst.fragment == actualSecond.fragment &&
        actualFirst.fragment == actualOriginal.fragment && (← calls.get).size == 1 do
      throwError "observing two views replayed or replaced their original computation"
    unless DataOwnership.owners actualFirst.ownership == #[owner] do
      throwError "the original callable lost its exact actual supplier"

    let actualParameter ← realizeValueObservation harness trace parameter
    unless actualParameter.value == valueView && actualParameter.actualData &&
        actualParameter.categoryContext.isNone && actualParameter.callableEndpoints.isNone &&
        DataOwnership.owners actualParameter.ownership == #[owner] &&
        (← calls.get).size == 1 do
      throwError "the function projection did not reuse its complete actual callable and owner"
    unless (← callableBody actualParameter.fragment) == (← callableBody actualFirst.fragment) do
      throwError "the function projection replaced the original opaque callable body"
    let reused ← observeActionDataWire { harness with demandObjectActions := true }
      trace .parameter actualParameter
    unless reused.fragment == actualParameter.fragment && (← calls.get).size == 1 do
      throwError "reusing the function-valued parameter repeated its original computation"

    -- The independent producer may return different data at the same formal
    -- callable. Its fresh protocol token must not be replaced by the first one.
    let actualSeparate ← realizeArrowObservation harness trace separate
    unless actualSeparate.value == independent && actualSeparate.owner? == some owner &&
        actualSeparate.fragment != actualFirst.fragment && (← calls.get).size == 2 do
      throwError "an independent equal producer was coalesced into the viewed occurrence"
    harness.stop
    unavailable "first whole callable" (realizeArrowObservation harness trace actualFirst)
    unavailable "second whole callable" (realizeArrowObservation harness trace actualSecond)
    unavailable "function-valued parameter" (realizeValueObservation harness trace actualParameter)
    unavailable "independent whole callable" (realizeArrowObservation harness trace actualSeparate)
    unless (← calls.get).size == 2 do
      throwError "an expired view dispatched before rejecting its original supplier"
  finally harness.stop

end
end CasCatalogue.OriginalViewLifecycleEngineering
