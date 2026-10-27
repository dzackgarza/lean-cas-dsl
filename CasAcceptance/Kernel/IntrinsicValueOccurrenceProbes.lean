/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering control for a pending whole map reified as a point, used as a
scalar parameter, and subsequently reused as a complete point map. Existing
registered actions fix all mathematical types. Arbitrary protocol packets test
occurrence retention and execution order; they are not mathematical answers. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.IntrinsicValueOccurrenceProbes
meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the intrinsic value control lost its accepted action"
  let some row := state.objects.find? (·.id.raw == "obj.linear_orders.naturals")
    | throwError "the intrinsic value control lost its original source"
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the intrinsic value control lost its original category"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the intrinsic value control lost its target category"
  let trace ← Trace.new
  let source ← Semantic.object row #[] (some trace)
  let sourceContext ← CategoryContext.ofNamed category source
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  let formal ← Semantic.mapOf action identity
  let image ← Semantic.objOf action source
  let context ← CategoryContext.ofNamed sets image
  Trace.record (some trace) formal
    (.morphismTransport category.id sets.id #[.functor entry.id] identity)
  let supplied := node "obj.linear_orders.integers" #[]
  let replacement := node "obj.linear_orders.naturals" #[]
  let mapData := fun endpoint => Backend.TypedMap.encode {
    source := endpoint, target := endpoint,
    callable := node "identity" #[endpoint, endpoint] }
  let originalObject : Wire := {
    form := .object row, payload := .computed source (.inline supplied),
    categoryContext := some sourceContext }
  let originalMap : Wire := {
    form := .canonicalMorphism category,
    payload := .computed identity (.inline (mapData supplied)),
    categoryContext := some sourceContext, callableObserved := true }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "intrinsic-value-probe", command := "python3",
      args := #["probe_functor_execution.py", "action", entry.id.raw, "--bare-maps"] }]
    registrations := #[
      { operation := entry.id.raw, input := entry.inputAddress, backend := "intrinsic-value-probe" },
      { operation := entry.mapAddress, input := entry.inputAddress, backend := "intrinsic-value-probe" }] }
  let calls ← IO.mkRef #[]
  let h ← Harness.ofManifest root manifest
  let h := { h with dispatches := some calls }
  unless h.rejected.isEmpty && h.admitted.size == 2 && !h.demandObjectActions do
    throwError "the intrinsic value control changed its selected primitive interfaces"
  try
    h.results.modify (·.insert source originalObject |>.insert identity originalMap)
    let pending ← realizeUnobserved h trace "the original deferred whole map" formal
    let owner ← wholeCallableObject formal image image context
    let one ← Language.globalPointSource.run {}
    let point ← wholeCallablePoint h trace pending image image one context owner
    unless point.pointDataInterface.isSome && !point.completedData do
      throwError "a pending whole-callable point was marked completed by its point interface"
    let pointContext ← CategoryContext.ofNamed sets one
    let complete ← captureCompleteCallable h trace point pointContext
    unless !complete.completedData && complete.pointDataInterface.isNone &&
        complete.intrinsicAssembly.isSome do
      throwError "a pending point-to-callable conversion discarded its executable original point"
    let selected : Language.Value := .object owner.application.value sets none none none
    let scalar ← (Language.typedParameter owner.application.value (.element point.value selected)).run
      { trace := some trace }
    let some (.elementValue retainedPoint _ _) ← trace.node? scalar
      | throwError "the intrinsic value control lost its scalar producer"
    let point ← forwardRetainedValue point retainedPoint
    h.results.modify (·.insert retainedPoint point)
    let parameter ← realizeUnobserved h trace "the original scalar callable parameter" scalar
    let some assembly ← retainedIntrinsicValueAssembly? parameter
      | throwError "the scalar parameter did not retain its independently fixed value interface"
    if let .value expected := assembly.result then
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq expected (← inferType scalar)) do
        throwError "the scalar parameter changed its complete expected type"
    else throwError "the scalar parameter acquired an object or map result role"
    unless (← calls.get).isEmpty do
      throwError "capturing a scalar or point conversion executed an unselected action"

    -- These equal-formal cache entries are different computational occurrences.
    -- The point and scalar must continue to use their original captured map.
    let otherMap := mapData (node "obj.sets.naturals" #[])
    h.results.modify (·.insert source { originalObject with
      payload := .computed source (.inline replacement) } |>.insert identity { originalMap with
      payload := .computed identity (.inline (mapData replacement)) } |>.insert formal {
      form := .canonicalMorphism sets, payload := .computed formal (.inline otherMap),
      categoryContext := some context, callableObserved := true } |>.insert retainedPoint {
      point with payload := .computed retainedPoint (.inline otherMap), callableObserved := true })
    let actual ← observeActionDataWire { h with demandObjectActions := true } trace .parameter parameter
    let events ← calls.get
    unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
        #[some entry.id.raw, some entry.mapAddress] do
      throwError "the scalar parameter did not execute its retained object and whole-map actions"
    let .ok request := events[0]!.getObjVal? "request"
      | throwError "the scalar parameter lost its actual endpoint request"
    unless (request.getObjVal? "receiver").toOption == some supplied do
      throwError "the scalar parameter replaced its original source occurrence from the cache"
    let receipts ← h.actions.get
    let #[_, mapReceipt] := receipts
      | throwError "the scalar parameter lost its whole-map execution receipt"
    let child ← checkedFragment
      (actual.fragment.project #[.field "args", .index 1, .field "args", .index 0])
    unless child == mapReceipt.result.fragment && child.ownership == mapReceipt.result.ownership &&
        !child.ownership.isEmpty do
      throwError "the scalar value lost its actual opaque callable or supplying session"
    unless actual.value == scalar && actual.categoryContext.isNone do
      throwError "the scalar result changed its formal value or invented a category context"

    let mappedPoint ← realizeArrowObservation h trace complete
    let .ok outer := Backend.TypedMap.decode mappedPoint.json
      | throwError "the reused point lost its complete map frame"
    let .ok ("finiteGraph", #[_, rows]) := ComputationalData.envelope outer.callable
      | throwError "the point conversion lost its supplied singleton-domain encoding"
    let .arr #[.arr #[_, actualValue]] := rows
      | throwError "the point conversion did not retain exactly one complete callable value"
    unless actualValue == mapReceipt.result.json &&
        DataOwnership.owners mappedPoint.ownership == DataOwnership.owners mapReceipt.result.ownership &&
        (← calls.get).size == 2 do
      throwError "the point conversion replayed a primitive or discarded its actual whole callable"
    let reused ← observeActionDataWire { h with demandObjectActions := true } trace .parameter actual
    unless reused.fragment == actual.fragment && (← calls.get).size == 2 do
      throwError "reusing the scalar value changed an occurrence or repeated computation"
  finally h.stop

end
end CasCatalogue.IntrinsicValueOccurrenceProbes
