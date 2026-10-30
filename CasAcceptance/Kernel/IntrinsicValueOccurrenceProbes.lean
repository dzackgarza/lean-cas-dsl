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

private partial def containsData (data expected : Json) : Bool :=
  data == expected || match data with
    | .arr children => children.any (containsData · expected)
    | .obj fields => fields.any fun _ child => containsData child expected
    | _ => false

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
  let (action, _, context) ←
    (Language.selectedEdgeAction {} (.functor entry.id) #[] sourceContext).run
      { trace := some trace }
  let formal ← Semantic.mapOf action identity
  let image ← Semantic.objOf action source
  Trace.record (some trace) formal
    (.contextualRoute sourceContext context #[.functor entry.id] #[action] identity true)
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

-- The extracted value itself can inhabit a complete structured Hom. This is
-- distinct from using the outer point as a map out of the global-point source.
-- The registered module-map owner fixes the full scalar/module dictionaries;
-- the arbitrary portable packet supplies no mathematical answer.
run_elab do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the extracted-Hom control lost the published ring category"
  let some modules := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the extracted-Hom control lost the published module category"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the extracted-Hom control lost the published set category"
  let trace ← Trace.new
  let ringValue ← (Language.object state "ℤ" #[] (some rings)).run { trace := some trace }
  let moduleValue ← (Language.object state "RegularModule" #[ringValue] (some modules)).run
    { trace := some trace }
  let module ← (Language.semanticObject moduleValue).run {}
  let context ← CategoryContext.ofNamed modules module
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[module]
  Trace.record (some trace) identity (.contextualIdentity context module)
  discard <| Semantic.recordNamedObject module (some trace)
  let owner ← wholeCallableObject identity module module context
  let expected ← context.hom module module
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq owner.application.value expected) do
    throwError "the extracted-Hom control erased its full module Hom to a function"
  let some comparison := state.presentations.find? (·.id.raw == "cmp.sets.singleton_terminal")
    | throwError "the extracted-Hom control lost its accepted singleton comparison"
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "intrinsic-hom-comparison-probe", command := "python3",
      args := #["probe_complete_callable.py", "--bare-reply", comparison.id.raw] }]
    registrations := #[{
      operation := comparison.id.raw, input := comparison.id.raw,
      backend := "intrinsic-hom-comparison-probe" }] }
  let h ← Harness.ofManifest root manifest
  let calls ← IO.mkRef #[]
  let h := { h with dispatches := some calls }
  unless h.rejected.isEmpty && h.admitted.size == 1 do
    throwError "the accepted singleton comparison was not admitted by its original interface"
  try
    let endpoint ← realizeEndpoint h trace "the original complete module endpoint" module
    let token := node "identity" #[endpoint.json, endpoint.json]
    let replacement := node "zero" #[endpoint.json, endpoint.json]
    let original : Wire := {
      form := .canonicalMorphism modules,
      payload := .computed identity (.inline token), categoryContext := some context,
      callableObserved := true }
    let original ← retainCallableEndpoints original endpoint endpoint context
    let one ← Language.globalPointSource.run {}
    let terminal ← elabTermAndSynthesize (← `(PUnit.{1})) none
    let restaged ← wholeCallablePoint h trace original module module terminal context owner
    let some forward ← (Language.operationPointComparison terminal).run { trace := some trace }
      | throwError "the full-Hom control lost its complete forward singleton comparison"
    h.results.modify (·.insert restaged.value restaged)
    let composed ← mkAppM ``CategoryTheory.CategoryStruct.comp #[forward, restaged.value]
    Trace.record (some trace) composed
      (.morphismComposition sets.id forward restaged.value one terminal owner.application.value)
    let point ← realizeUnobserved h trace "the complete compared full-Hom point" composed
    unless point.pointDataInterface.isNone && !point.completedData &&
        (← retainedIntrinsicAssembly? point .map).isSome do
      throwError "the full-Hom control bypassed its retained closed-point composition"
    let selected : Language.Value := .object owner.application.value sets none none none
    let scalar ← (Language.typedParameter owner.application.value (.element point.value selected)).run
      { trace := some trace }
    let some (.elementValue retainedPoint _ _) ← trace.node? scalar
      | throwError "the full Hom extraction did not retain its original point"
    let point ← forwardRetainedValue point retainedPoint
    h.results.modify (·.insert retainedPoint point)
    let value ← realizeUnobserved h trace "the extracted complete module Hom" scalar
    let some assembly ← retainedIntrinsicValueAssembly? value
      | throwError "the extracted full Hom lost its independent value result role"
    let .value retainedType := assembly.result
      | throwError "extracting a full Hom prematurely assigned a map result role"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq retainedType expected <&&> isDefEq (← inferType scalar) expected) do
      throwError "the extracted value changed its full module Hom type"
    unless value.categoryContext.isNone && value.pointDataInterface.isNone &&
        !value.completedData do
      throwError "the extracted value borrowed the outer point's computational role"
    let complete ← captureCompleteCallable h trace value context
    let some (source, target) ← retainedCallableEndpoints? complete context
      | throwError "the complete extracted Hom lost its original endpoint occurrences"
    unless (← calls.get).isEmpty do
      throwError "capturing the full Hom executed an unselected point comparison"
    h.results.modify (·.insert module { endpoint with
      payload := .computed module (.inline replacement) } |>.insert identity { original with
      payload := .computed identity (.inline replacement) } |>.insert scalar { value with
      payload := .computed scalar (.inline replacement) } |>.insert retainedPoint { point with
      payload := .computed retainedPoint (.inline replacement), callableObserved := true })
    let actual ← realizeArrowObservation h trace complete
    let some (actualSource, actualTarget) ← retainedCallableEndpoints? actual context
      | throwError "observing the extracted Hom lost its complete endpoint receipt"
    CategoryContext.checkMorphism context actual.value module module
    let events ← calls.get
    unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
        #[some comparison.id.raw, some comparison.id.raw] do
      throwError "the extracted value bypassed a retained closed-point comparison"
    let .ok connection ← h.connection "intrinsic-hom-comparison-probe"
      | throwError "the full-Hom control lost its actual comparison supplier"
    unless actual.value == scalar && actualSource.fragment == source.fragment &&
        actualTarget.fragment == target.fragment && containsData actual.json token &&
        !containsData actual.json replacement &&
        (DataOwnership.owners actual.ownership).contains
          ("intrinsic-hom-comparison-probe", connection.identity) do
      throwError "the extracted Hom replaced a retained occurrence or invented a computation"
    let objects : ComputationalData.InterfaceObjects :=
      #[(actualSource.json, actualSource.value), (actualTarget.json, actualTarget.value)]
    let scope ← wireValidationScope .map actual (some context)
    if let .error message ← ComputationalData.validateCallableAt objects expected actual.json
        (some scope) then
      throwError "the extracted Hom has no valid complete callable interface: {message}"
    let .error _ ← ComputationalData.validateCallableAt objects expected actual.json
      | throwError "unpositioned scalar bytes acquired a complete callable interface"
    let .ok _ := Backend.TypedMap.decode actual.json
      | throwError "the extracted Hom lost its public complete callable frame"
    let other ← elabTermAndSynthesize (← `(ModuleCat.of ℤ (ℤ × ℤ))) none
    if ← withoutModifyingState (withTransparency .all <| isDefEq module other) then
      throwError "the full-Hom negative control did not change its module endpoint"
    for changed in #[← context.hom other module, ← context.hom module other] do
      let .error _ ← ComputationalData.validateCallableAt objects changed actual.json (some scope)
        | throwError "the extracted Hom accepted a different complete endpoint"
    let again ← realizeArrowObservation h trace actual
    unless sameCompleteWireContext again actual && (← calls.get).size == 2 &&
        value.categoryContext.isNone && (← retainedIntrinsicValueAssembly? value).isSome do
      throwError "complete callable reuse changed the independent original value occurrence"
    logInfo "PASS: an extracted full Hom retains its original callable and endpoints through reuse"
  finally h.stop

end
end CasCatalogue.IntrinsicValueOccurrenceProbes
