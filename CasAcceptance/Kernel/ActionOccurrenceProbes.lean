/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for deferred action occurrences. The complete formal
action is fixed before an unrelated cache entry changes. Its original input and
parameter packets must remain the selected inputs. Arbitrary protocol witnesses
test data flow; they do not provide or establish mathematical answers. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.ActionOccurrenceProbes
meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def harnessFor (entry : FunctorEntry) (options : Array String := #[]) :
    TermElabM (Harness × IO.Ref (Array Json)) := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "action-occurrence-probe", command := "python3",
      args := #["probe_functor_execution.py", "action", entry.id.raw, "--bare-maps"] ++ options }]
    registrations := #[
      { operation := entry.id.raw, input := entry.inputAddress,
        backend := "action-occurrence-probe" },
      { operation := entry.mapAddress, input := entry.inputAddress,
        backend := "action-occurrence-probe" }] }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == 2 do
    throwError "the occurrence control lost its accepted primitive interfaces"
  return ({ harness with dispatches := some calls, demandObjectActions := true }, calls)

private def retainReport (name : String) (formal : Expr) (calls : Array Json) :
    TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_ACTION_OCCURRENCE_REPORT" then
    IO.FS.withFile path .append fun output => output.putStrLn (Json.mkObj [
      ("case", toJson name), ("formal", toJson (reprStr formal)),
      ("purpose", "Deferred action occurrence engineering control; no mathematical verdict"),
      ("dispatches", Json.arr calls)]).compress

-- An action formed from one actual source cannot later acquire another packet
-- merely because that packet has the same formal cache key.
run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the existing structural action is absent"
  let some row := state.objects.find? (·.id.raw == "obj.linear_orders.naturals")
    | throwError "the original source is absent"
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the original source category is absent"
  let trace ← Trace.new
  let source ← Semantic.object row #[] (some trace)
  let context ← CategoryContext.ofNamed category source
  let (formal, _) ← Semantic.applyRegisteredFunctor entry source #[] (some trace)
  let supplied := node "obj.linear_orders.integers" #[]
  let original : Wire := {
    form := .object row, payload := .computed source (.inline supplied),
    categoryContext := some context }
  let replacement : Wire := { original with
    payload := .computed source (.inline (node "obj.linear_orders.naturals" #[])) }
  let (harness, calls) ← harnessFor entry
  try
    harness.results.modify (·.insert source original)
    let pending ← realizeUnobserved harness trace "the selected original object action" formal
    unless (← calls.get).isEmpty do
      throwError "capturing an object action executed it during preparation"
    harness.results.modify (·.insert source replacement)
    let actual ← realizeObjectObservation harness trace pending
    let events ← calls.get
    retainReport "original-object-occurrence" formal events
    unless events.size == 1 do
      throwError "the selected object action did not execute exactly once"
    let .ok request := events[0]!.getObjVal? "request"
      | throwError "the object action lost its public request"
    unless (request.getObjVal? "receiver").toOption == some supplied do
      throwError "a deferred object action replaced its captured source occurrence from the cache"
    let receipts ← harness.actions.get
    unless receipts.size == 1 && sameActionOperand receipts[0]!.input original do
      throwError "the object action receipt replaced its exact original input"
    let reused ← realizeObjectObservation harness trace actual
    unless reused.fragment == actual.fragment && (← calls.get).size == 1 do
      throwError "reusing an actual object image replayed its recipe"
  finally harness.stop

-- A retained route keeps its addressed result before and after observation.
-- Equal mathematical sources have independent producer occurrences; repeating
-- one pending selection must not capture a later ambient source replacement.
run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the retained-route control lost its existing list action"
  let some row := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the retained-route control lost its existing finite-object declaration"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the retained-route control lost its complete set category"
  let trace ← Trace.new
  let edge := EdgeRef.functor entry.id
  let action ← Semantic.edgeFunctor state edge
  let (harness, calls) ← harnessFor entry #["--opaque-objects"]
  let preparing := { harness with demandObjectActions := false }
  try
    let sources ← #[(), ()].mapM fun _ => do
      Semantic.object row #[← `(2)] (some trace)
    let selections ← sources.mapM fun source => do
      let original ← realizeUnobserved preparing trace "the retained route's original source" source
      let image ← Semantic.objOf action source
      let (formal, applications) ← (Language.checkedRouteAction state sets.id sets.id
        #[edge] source (← inferType image)).run { trace := some trace }
      let some (.retainedRoute sourceCategory targetCategory route retained receiver) ← trace.node? formal
        | throwError "the route control did not select the retained-route evaluator"
      unless sourceCategory == sets.id && targetCategory == sets.id && route == #[edge] &&
          retained == applications && receiver == source && (Trace.producerAnchor? formal).isSome do
        throwError "the retained route changed its exact selected construction"
      let pending ← realizeUnobserved preparing trace "the addressed pending route" formal
      let .ordinary .. := pending.payload
        | throwError "the route control did not exercise an ordinary pending interpretation"
      unless pending.value == formal && !pending.completedData && pending.actionRecipe.isSome do
        throwError "the pending retained route lost its exact producer anchor or pending role"
      return (formal, original, pending)
    let #[(firstFormal, firstSource, firstPending), (secondFormal, secondSource, secondPending)] := selections
      | throwError "the route control lost its two selected occurrences"
    unless firstFormal != secondFormal && firstSource.value != secondSource.value &&
        firstSource.fragment == secondSource.fragment &&
        (← withoutModifyingState (withTransparency .all <| isDefEq firstFormal secondFormal)) &&
        (← calls.get).isEmpty do
      throwError "the route control did not retain distinct equal-mathematical pending producers"
    let replacement := { firstSource with
      payload := .computed firstSource.value (.inline (node row.id.raw #[toJson (3 : Nat)])) }
    harness.results.modify (·.insert firstSource.value replacement)
    let repeated ← realize preparing trace "the same pending route" firstFormal
    let unobserved ← realizeUnobserved preparing trace "the same unobserved route" firstFormal
    for selected in #[repeated, unobserved] do
      let some recipe := selected.actionRecipe
        | throwError "reusing a pending route discarded its selected action"
      unless sameCompleteWireContext selected firstPending &&
          sameRetainedServiceHandles selected firstPending && !selected.completedData &&
          recipe.original.value == firstSource.value &&
          recipe.original.fragment == firstSource.fragment && (← calls.get).isEmpty do
        throwError "a repeated pending route selected the ambient replacement or executed an action"
    let first ← realizeObjectObservation harness trace firstPending
    let second ← realizeObjectObservation harness trace secondPending
    let #[firstReceipt, secondReceipt] ← harness.actions.get
      | throwError "the two retained routes lost their independent action receipts"
    let some (.ok session) := (← harness.connections.get)["action-occurrence-probe"]?
      | throwError "the retained routes lost their actual supplying session"
    for (formal, original, actual, receipt) in #[
        (firstFormal, firstSource, first, firstReceipt),
        (secondFormal, secondSource, second, secondReceipt)] do
      unless actual.value == formal && actual.actualData && actual.objectObserved &&
          receipt.input.value == original.value && receipt.input.fragment == original.fragment &&
          actual.fragment == receipt.result.fragment &&
          actual.owner? == some ("action-occurrence-probe", session.identity) do
        throwError "a retained route changed its addressed result, original input, or actual suppliers"
      let reused ← realize harness trace "the same completed addressed route" formal
      unless sameCompleteWireContext reused actual && sameRetainedServiceHandles reused actual do
        throwError "an exact producer lookup changed its completed route occurrence"
    unless first.fragment != second.fragment && (← calls.get).size == 2 do
      throwError "distinct retained routes merged their outputs or repeated an action"
    let some before := (← harness.results.get)[firstFormal]?
      | throwError "the completed retained route lost its exact result entry"
    let fresh ← realizeFresh preparing trace "an explicit fresh route preparation" firstFormal
    let some after := (← harness.results.get)[firstFormal]?
      | throwError "explicit fresh preparation removed an earlier actual result"
    unless fresh.value == firstFormal && !fresh.completedData &&
        sameCompleteWireContext before first && sameCompleteWireContext after before &&
        sameRetainedServiceHandles after before && (← calls.get).size == 2 do
      throwError "explicit fresh preparation overwrote an actual route or executed its pending action"
    retainReport "addressed-retained-route-reuse" firstFormal (← calls.get)
  finally harness.stop

-- A retained map has its own complete callable and endpoint fields. Replacing
-- both formal cache keys must not change those fields or the primitive request.
run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the existing map action is absent"
  let some row := state.objects.find? (·.id.raw == "obj.linear_orders.naturals")
    | throwError "the original map source is absent"
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the source category is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the target category is absent"
  let trace ← Trace.new
  let source ← Semantic.object row #[] (some trace)
  let context ← CategoryContext.ofNamed category source
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  let formal ← Semantic.mapOf action identity
  Trace.record (some trace) formal
    (.morphismTransport category.id sets.id #[.functor entry.id] identity)
  let supplied := node "obj.linear_orders.integers" #[]
  let foreign := node "obj.linear_orders.naturals" #[]
  let mapData := fun endpoint => Backend.TypedMap.encode {
    source := endpoint, target := endpoint,
    callable := node "identity" #[endpoint, endpoint] }
  let originalObject : Wire := {
    form := .object row, payload := .computed source (.inline supplied),
    categoryContext := some context }
  let originalMap : Wire := {
    form := .canonicalMorphism category,
    payload := .computed identity (.inline (mapData supplied)),
    categoryContext := some context, callableObserved := true }
  let (harness, calls) ← harnessFor entry
  try
    harness.results.modify (·.insert source originalObject |>.insert identity originalMap)
    let pending ← realizeUnobserved harness trace "the selected original map action" formal
    unless (← calls.get).isEmpty do
      throwError "capturing a map action executed it during preparation"
    harness.results.modify (·.insert source { originalObject with
      payload := .computed source (.inline foreign) } |>.insert identity { originalMap with
      payload := .computed identity (.inline (mapData foreign)) })
    let actual ← realizeArrowObservation harness trace pending
    let events ← calls.get
    retainReport "original-map-occurrence" formal events
    unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
        #[some entry.id.raw, some entry.mapAddress] do
      throwError "the selected map did not execute its complete object and map actions"
    let .ok objectRequest := events[0]!.getObjVal? "request"
      | throwError "the map's endpoint action lost its request"
    let .ok mapRequest := events[1]!.getObjVal? "request"
      | throwError "the map action lost its request"
    let .ok invocation := Backend.PointInvocation.decode mapRequest
      | throwError "the map action lost its complete invocation"
    let .ok ("map", #[_, retained]) := ComputationalData.envelope invocation.arrow
      | throwError "the map action lost its original callable"
    unless (objectRequest.getObjVal? "receiver").toOption == some supplied &&
        retained == mapData supplied do
      throwError "a deferred map action replaced its captured callable or endpoint occurrence from the cache"
    let receipts ← harness.actions.get
    unless receipts.size == 2 && actual.owner? == receipts[1]!.result.owner? &&
        actual.owner?.isSome do
      throwError "the actual whole map lost its original supplying session"
    let reused ← realizeArrowObservation harness trace actual
    unless reused.fragment == actual.fragment && (← calls.get).size == 2 do
      throwError "reusing an actual mapped callable replayed a primitive"
  finally harness.stop

-- Complete functor parameters are original runtime occurrences too. Their
-- formal declaration application remains the same when a cache entry changes.
run_elab do
  let state ← registryState
  let some entry := state.functor? FunctorId.modulesFibreInclusion
    | throwError "the existing parameterized action is absent"
  let some ringRow := state.objects.find? (·.id.raw == "obj.rings.integers")
    | throwError "the scalar object is absent"
  let some moduleRow := state.objects.find? (·.id.raw == "obj.modules.vectors")
    | throwError "the selected module family is absent"
  let trace ← Trace.new
  let ring ← Semantic.object ringRow #[] (some trace)
  let source ← Semantic.object moduleRow #[← exprToSyntax ring, ← `(1)] (some trace)
  let action ← ObjectPresentation.applyParameters entry.declaration #[ring]
  let formal ← Semantic.objOf action source
  let action ← instantiateMVars action
  let (sourceBundle, targetBundle) ← functorCategoryBundles action
  let sourceContext : CategoryContext := { expression := entry.source, bundle := sourceBundle }
  let targetContext : CategoryContext := { expression := entry.target, bundle := targetBundle }
  Trace.record (some trace) formal
    (.contextualRoute sourceContext targetContext #[.functor entry.id] #[action] source false)
  let empty ← Harness.empty
  let sourceWire ← realize empty trace "the original parameterized source" source
  let scalarWire ← realize empty trace "the original scalar parameter" ring
  let originalScalar : Wire := { scalarWire with
    payload := .computed ring (.inline scalarWire.json) }
  let replacement : Wire := { scalarWire with
    payload := .computed ring (.inline (node "obj.rings.integers_mod" #[toJson (7 : Nat)])) }
  let (harness, calls) ← harnessFor entry #["--opaque-objects"]
  try
    harness.results.modify (·.insert source sourceWire |>.insert ring originalScalar)
    let pending ← realizeUnobserved harness trace "the complete selected parameterized action" formal
    unless (← calls.get).isEmpty do
      throwError "capturing an action parameter executed the action during preparation"
    harness.results.modify (·.insert ring replacement)
    discard <| realizeObjectObservation harness trace pending
    let events ← calls.get
    retainReport "original-parameter-occurrence" formal events
    unless events.size == 1 do
      throwError "the selected parameterized object action did not execute exactly once"
    let .ok request := events[0]!.getObjVal? "request"
      | throwError "the parameterized action lost its request"
    unless (request.getObjVal? "args").toOption == some (Json.arr #[originalScalar.json]) do
      throwError "a deferred action replaced its captured complete parameter occurrence from the cache"
    let receipts ← harness.actions.get
    unless receipts.size == 1 && receipts[0]!.parameterInputs.any
        (fun parameter => sameActionOperand parameter originalScalar) do
      throwError "the parameterized action receipt lost its exact original scalar occurrence"
  finally harness.stop

end
end CasCatalogue.ActionOccurrenceProbes
