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
    let some actualAssembly ← retainedIntrinsicValueAssembly? actual
      | throwError "the observed scalar lost its value producer"
    let .ctor "element" #[.wire .retained _, .ctor "point" #[.wire .map actualPoint]] :=
      actualAssembly.template
      | throwError "the observed scalar changed its original point extraction"
    let (_, actualPointTarget) ← capturedMapEndpoints h trace actualPoint pointContext true
    let descriptor ← checkedFragment (actual.fragment.project #[.field "args", .index 0])
    unless descriptor == actualPointTarget.fragment do
      throwError "the scalar descriptor differs from its original point's actual complete target"

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

-- An unnamed endpoint can be retained only as a reference to its original
-- pending callable. It has no standalone object action to observe. Exercise
-- the intrinsic boundary with an independently supplied complete callable,
-- including a transparent wrapper and distinct exact endpoint suppliers.
run_elab do
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the reference extraction control lost its data category"
  let trace ← Trace.new
  let h ← Harness.empty
  let one ← Language.globalPointSource.run {}
  let target ← elabTermAndSynthesize (← `(ℕ)) none
  let context ← CategoryContext.ofNamed sets one
  let formal ← Semantic.hom
    (← `(TypeCat.ofHom (fun (_ : $(← exprToSyntax one)) => (0 : ℕ)))) one target
  let pendingData : DataOwnership.Data := {
    json := node "opaqueData" #[toJson "pending original point"]
    ownership := DataOwnership.capture
      (node "opaqueData" #[toJson "pending original point"]) ("reference-original", 61) }
  let pending : Wire := {
    form := .canonicalMorphism sets, payload := (← recipePayload formal pendingData),
    categoryContext := some context }
  let source ← callableEndpointReference pending one true (some context)
  let endpoint ← callableEndpointReference pending target false (some context)
  unless endpoint.intrinsicAssembly.isNone && endpoint.actionRecipe.isNone &&
      (Backend.MorphismEndpoint.decode endpoint.json).isOk do
    throwError "the reference extraction control gained an independent object producer"
  let pending ← retainCallableEndpoints pending source endpoint context
  let selected : Language.Value := .object target sets none none none
  let scalar ← (Language.typedParameter target (.element formal selected)).run { trace := some trace }
  let some (.elementValue retainedPoint _ _) ← trace.node? scalar
    | throwError "the reference extraction control lost its original scalar producer"
  let pending ← forwardRetainedValue pending retainedPoint
  h.results.modify (·.insert retainedPoint pending)
  let value ← realizeUnobserved h trace "the reference-origin scalar" scalar
  let some originalAssembly ← retainedIntrinsicValueAssembly? value
    | throwError "the reference-origin scalar lost its complete value interface"
  let actualSource : Wire := {
    form := .diagrams sets, payload := .computed one
      (.owned "reference-source" 62 (node "opaqueData" #[toJson "actual source"])),
    categoryContext := some context, objectObserved := true }
  let actualTarget : Wire := {
    form := .diagrams sets, payload := .computed target
      (.owned "reference-target" 63 (node "opaqueData" #[toJson "actual target"])),
    categoryContext := some context, objectObserved := true }
  let callableData : DataOwnership.Data := {
    json := node "opaqueData" #[toJson "actual point"]
    ownership := DataOwnership.capture
      (node "opaqueData" #[toJson "actual point"]) ("reference-callable", 64) }
  let supplied ← scopedNode "typedMap" #[actualSource.fragment, actualTarget.fragment, callableData]
  let supplied ← scopedNode "valueData" #[supplied]
  let actualPoint : Wire := {
    form := .canonicalMorphism sets, payload := (← scopedPayload retainedPoint supplied),
    categoryContext := some context, callableObserved := true }
  let targetAlias ← elabTermAndSynthesize (← `(id (ℕ : Type))) none
  let aliasTarget ← forwardRetainedValue actualTarget targetAlias
  let poisoned := { actualTarget with
    payload := .computed target (.owned "different-target" 65 actualTarget.json) }
  let poisonedPoint := { actualPoint with payload := (← recipePayload retainedPoint pendingData) }
  h.results.modify (·.insert target poisoned |>.insert retainedPoint poisonedPoint)
  for hasReceipt in #[false, true] do
    let actualPoint ← if hasReceipt then
      retainCallableEndpoints actualPoint actualSource aliasTarget context
      else pure actualPoint
    let observations ← IO.mkRef (0 : Nat)
    let observe := fun (role : ActionDataRole) (input : Wire) => do
      match role with
      | .retained => pure input
      | .map =>
          if input.completedData then pure input else do
            unless sameCompleteWireContext input pending do
              throwError "the extraction observed a different pending point occurrence"
            observations.modify (· + 1)
            pure actualPoint
      | _ => throwError "the extraction independently observed an endpoint-reference object"
    let read := fun (input : Wire) (selected : CategoryContext) =>
      capturedMapEndpoints h trace input selected true
    let actual ← observeCurrentIntrinsicAssemblyWith observe read h value
    let descriptor ← checkedFragment (actual.fragment.project #[.field "args", .index 0])
    let pointData ← checkedFragment
      (actual.fragment.project #[.field "args", .index 1, .field "args", .index 0])
    unless descriptor == actualTarget.fragment && pointData == actualPoint.fragment &&
        (← observations.get) == 1 && actual.categoryContext.isNone &&
        !actual.completedData && actual.value == scalar do
      throwError "the extraction lost its current target, exact point, suppliers or value role"
    let again ← observeCurrentIntrinsicAssemblyWith observe read h actual
    unless sameCompleteWireContext again actual && (← observations.get) == 1 do
      throwError "the reference-origin extraction did not reuse its exact current point interface"
    let #[fields] := originalAssembly.maps
      | throwError "the reference-origin producer lost its exact endpoint relationship"
    let movedData : DataOwnership.Data := {
      json := fields.target.json
      ownership := DataOwnership.capture fields.target.json ("different-original-target", 66) }
    let wrongEndpoint := { fields.target with
      payload := (← recipePayload fields.target.value movedData) }
    unless wrongEndpoint.json == fields.target.json &&
        wrongEndpoint.completedData == fields.target.completedData &&
        wrongEndpoint.ownership != fields.target.ownership do
      throwError "the changed-supplier control altered data or completion instead of only ownership"
    let changed := { value with
      intrinsicAssembly := some { originalAssembly with
        maps := #[{ fields with target := wrongEndpoint }] } }
    let rejected ← try
      discard <| observeCurrentIntrinsicAssemblyWith observe read h changed
      pure false
    catch error =>
      if CasCatalogue.Exception.stratum? error != some .unavailable then throw error
      pure true
    unless rejected && (← observations.get) == 1 do
      throwError "the extraction accepted a moved supplier or observed its invalid original relation"
  -- Captured pending producers without a receipt retain their immutable input
  -- below the extraction's transparent view. Check the ordinary canonical
  -- invocation entry rather than accepting a copied invocation identifier.
  let aliasHarness ← Harness.empty
  let bare := { pending with callableEndpoints := none, intrinsicAssembly := none }
  let bare ← retainIntrinsicAssembly bare .map context (.literal bare.fragment)
  let some bareAssembly ← retainedIntrinsicAssembly? bare .map
    | throwError "the pending invocation control lost its own producer"
  let captured ← retainCapturedInvocation aliasHarness bare (.intrinsic bareAssembly)
  aliasHarness.results.modify (·.insert retainedPoint captured)
  let aliasValue ← realizeUnobserved aliasHarness trace "the scalar of a pending invocation" scalar
  let some aliasAssembly ← retainedIntrinsicValueAssembly? aliasValue
    | throwError "the pending invocation extraction lost its value interface"
  let .ctor "element" #[_, .ctor "point" #[.wire .map endpointView]] := aliasAssembly.template
    | throwError "the pending invocation extraction lost its original point"
  let some viewAssembly ← retainedIntrinsicAssembly? endpointView .map
    | throwError "the missing endpoint receipt was added to the canonical invocation"
  let .wire .map child := viewAssembly.template
    | throwError "the missing endpoint receipt did not retain the original complete child"
  unless sameCompleteWireContext child captured && endpointView.fragment == captured.fragment &&
      endpointView.capturedInvocation.isNone && (← retainedCallableEndpoints? endpointView context).isSome &&
      child.callableEndpoints.isNone do
    throwError "the endpoint view changed its pending producer or failed to retain its own receipt"
  let some invocation ← retainedCapturedInvocation? child
    | throwError "the transparent endpoint view lost its child's pending owner"
  discard <| capturedInvocationFrame aliasHarness child invocation

-- A separately selected structure on the scalar carrier retains its own
-- descriptor. A point endpoint reference cannot stand in for that structure.
run_elab do
  let .ok ring := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "the structured extraction control ring did not parse"
  let .ok literal := Parser.runParserCategory (← getEnv) `cas_term "1 in R"
    | throwError "the structured extraction control point did not parse"
  let scope : Language.Scope := ({} : Language.Scope).insert `R ring
  let trace ← Trace.new
  let original ← (Language.eval scope literal).run { trace := some trace }
  let expected ← elabTermAndSynthesize (← `(ℤ)) none
  let scalar ← (Language.typedParameter expected original).run { trace := some trace }
  let some (.elementValue point target selected) ← trace.node? scalar
    | throwError "the structured extraction lost its selected object"
  if ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType selected) (← inferType target)) then
    throwError "the structured extraction control has only a carrier selection"
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the structured extraction control lost its data category"
  let packet := node "opaqueData" #[toJson "selected ring point"]
  let supplied : Wire := {
    form := .canonicalMorphism sets,
    payload := .computed point (.owned "structured-extraction" 67 packet) }
  let h ← Harness.empty
  h.results.modify (·.insert point supplied)
  let value ← realizeUnobserved h trace "the structured scalar" scalar
  let selectedWire ← realizeUnobserved h trace "the independently selected structure" selected
  let actual ← observeCurrentIntrinsicAssemblyWith
    (fun role input => do
      unless role == .retained || role == .map do
        throwError "the structured extraction observed an independent carrier descriptor"
      pure input)
    (fun _ _ => throwError "the structured extraction requested a replacement carrier endpoint") h value
  let descriptor ← checkedFragment (actual.fragment.project #[.field "args", .index 0])
  let pointData ← checkedFragment
    (actual.fragment.project #[.field "args", .index 1, .field "args", .index 0])
  unless descriptor == selectedWire.fragment && pointData == supplied.fragment &&
      actual.value == scalar && actual.categoryContext.isNone do
    throwError "the scalar extraction replaced its selected structure with a carrier endpoint"

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
