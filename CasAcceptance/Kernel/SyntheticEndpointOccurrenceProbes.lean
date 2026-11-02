/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for a mapped callable's endpoint origin. A pending
map supplies the corresponding captured object action without computing its
map port. Completed map-shaped data supplies an intrinsic endpoint reference,
even when its bytes resemble a pending recipe. Existing declarations and the
existing arbitrary protocol process are the only mathematical/port fixtures. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.SyntheticEndpointOccurrenceProbes
meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def harnessFor (entry : FunctorEntry) (mapAvailable : Bool) :
    TermElabM (Harness × IO.Ref (Array Json)) := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "synthetic-endpoint-probe", command := "python3",
      args := #["probe_functor_execution.py", "action", entry.id.raw, "--bare-maps"] }]
    registrations := #[{
      operation := entry.id.raw, input := entry.inputAddress, backend := "synthetic-endpoint-probe" }] ++
      (if mapAvailable then #[{
        operation := entry.mapAddress, input := entry.inputAddress,
        backend := "synthetic-endpoint-probe" }] else #[]) }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == (if mapAvailable then 2 else 1) do
    throwError "the endpoint occurrence control lost its existing accepted interfaces"
  return ({ harness with dispatches := some calls, demandObjectActions := true }, calls)

private def report (label status : String) (formal : Expr) (calls : Array Json) :
    TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_SYNTHETIC_ENDPOINT_REPORT" then
    IO.FS.withFile path .append fun output => output.putStrLn (Json.mkObj [
      ("case", toJson label), ("status", toJson status),
      ("formal", toJson (reprStr formal)),
      ("purpose", "Typed endpoint occurrence engineering control; no mathematical verdict"),
      ("dispatches", Json.arr calls)]).compress

-- This harness deliberately has no map registration. An endpoint of the
-- already selected mapped identity needs only the existing object action.
run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the existing forgetful action is absent"
  let some row := state.objects.find? (·.id.raw == "obj.linear_orders.naturals")
    | throwError "the original source declaration is absent"
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the complete source category is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the complete target category is absent"
  let trace ← Trace.new
  let source ← Semantic.object row #[] (some trace)
  let context ← CategoryContext.ofNamed category source
  let identity ← instantiateMVars (← mkAppM ``CategoryTheory.CategoryStruct.id #[source])
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  let formal ← instantiateMVars (← Semantic.mapOf action identity)
  let image ← instantiateMVars (← Semantic.objOf action source)
  let targetContext ← CategoryContext.ofNamed sets image
  Trace.record (some trace) formal
    (.morphismTransport category.id sets.id #[.functor entry.id] identity)
  let supplied := node row.id.raw #[]
  let replacement := node "valueData" #[supplied]
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
  let (harness, calls) ← harnessFor entry false
  try
    let checked : Except Exception Unit ← try
      harness.results.modify (·.insert source originalObject |>.insert identity originalMap)
      let pending ← realizeUnobserved harness trace "the pending mapped callable" formal
      unless (← calls.get).isEmpty do
        throwError "preparing the mapped endpoint executed an action"
      report "pending-map-endpoint" "prepared-before-cache-replacement" formal (← calls.get)
      harness.results.modify (·.insert source { originalObject with
          payload := .computed source (.inline replacement) }
        |>.insert identity { originalMap with
          payload := .computed identity (.inline (mapData replacement)) })
      let endpoint ← actionMapEndpoint harness trace pending (some targetContext) image true
      unless (← calls.get).isEmpty do
        throwError "projecting a pending map endpoint executed its whole map"
      let actual ← realizeObjectObservation harness trace endpoint
      let events ← calls.get
      unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
          #[some entry.id.raw] do
        throwError "the pending endpoint did not execute only its selected object action"
      let .ok request := events[0]!.getObjVal? "request"
        | throwError "the endpoint object action lost its public request"
      unless (request.getObjVal? "receiver").toOption == some supplied do
        throwError "the pending endpoint replaced its captured original source from the cache"
      let receipts ← harness.actions.get
      unless receipts.size == 1 && receipts[0]!.input.fragment == originalObject.fragment &&
          actual.fragment == receipts[0]!.result.fragment do
        throwError "the pending endpoint lost its captured input or actual object result"
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType actual.value) (← inferType image) <&&>
            isDefEq actual.value image) do
        throwError "the endpoint action changed its complete selected mathematical object"
      let reused ← realizeObjectObservation harness trace actual
      unless reused.fragment == actual.fragment && (← calls.get).size == 1 do
        throwError "reusing an actual map endpoint replayed its object action"
      pure (.ok ())
    catch error => pure (.error error)
    let status ← match checked with
      | .ok () => pure "passed"
      | .error error => error.toMessageData.toString
    report "pending-map-endpoint" status formal (← calls.get)
    if let .error error := checked then throw error
  finally harness.stop

-- Use an actually returned owned child to install a completed map-shaped
-- packet at its typed result interface. This isolates producer provenance;
-- it makes no claim that the arbitrary protocol witness proves a map law.
run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the existing endofunctor is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set category is absent"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the existing finite object is absent"
  let trace ← Trace.new
  let source ← Semantic.object finite #[← `(2)] (some trace)
  let context ← CategoryContext.ofNamed sets source
  let sourceData := node finite.id.raw #[toJson (2 : Nat)]
  let identity ← instantiateMVars (← mkAppM ``CategoryTheory.CategoryStruct.id #[source])
  let original : Wire := {
    form := .canonicalMorphism sets,
    payload := .computed identity (.inline (Backend.TypedMap.encode {
      source := sourceData, target := sourceData,
      callable := node "identity" #[sourceData, sourceData] })),
    categoryContext := some context, callableObserved := true }
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  let (harness, calls) ← harnessFor entry true
  let formal ← instantiateMVars (← Semantic.mapOf action (← Semantic.mapOf action identity))
  try
    let checked : Except Exception Unit ← try
      let owned ← executeMapRoute harness trace original #[.functor entry.id] #[action]
      unless owned.owner?.isSome && (← calls.get).map
          (fun event => (event.getObjValAs? String "operation").toOption) ==
            #[some entry.id.raw, some entry.mapAddress] do
        throwError "the completed-data control lost its actual owned child"
      let packet ← scopedNode "map" #[{ json := node entry.id.raw #[] }, owned.fragment]
      if let .error message ← ComputationalData.validatePort formal (← inferType formal) packet.json then
        throwError "the completed-data control is outside its existing complete callable interface: {message}"
      let completed : Wire := {
        form := .canonicalMorphism sets,
        payload := (← scopedPayload formal packet), categoryContext := some context,
        callableObserved := true, morphismFramed := true }
      let (endpointValue, _) ← contextualMorphismEndpoints context formal
      report "completed-map-shaped-endpoint" "prepared-before-cache-replacement" formal (← calls.get)
      let foreign : Wire := {
        form := .diagrams sets,
        payload := .ordinary endpointValue (node finite.id.raw #[toJson (999 : Nat)]),
        categoryContext := some context }
      harness.results.modify (·.insert endpointValue foreign
        |>.insert formal { completed with payload := .computed formal (.inline (Json.arr #[])) })
      let endpoint ← actionMapEndpoint harness trace completed (some context) endpointValue true
      let expected := Backend.MorphismEndpoint.encode { callable := completed.json, source := true }
      unless endpoint.json == expected && endpoint.owner? == completed.owner? &&
          endpoint.owner?.isSome && endpoint.objectObserved && (← calls.get).size == 2 do
        throwError "a completed map-shaped packet became a new endpoint action or lost its supplying session"
      unless endpoint.ownership == DataOwnership.prefix #[.field "args", .index 0] completed.ownership do
        throwError "the completed endpoint reference changed a positioned callable supplier"
      let reused ← realizeObjectObservation harness trace endpoint
      unless reused.fragment == endpoint.fragment && (← calls.get).size == 2 do
        throwError "reusing completed map-shaped endpoint data replayed an action"
      pure (.ok ())
    catch error => pure (.error error)
    let status ← match checked with
      | .ok () => pure "passed"
      | .error error => error.toMessageData.toString
    report "completed-map-shaped-endpoint" status formal (← calls.get)
    if let .error error := checked then throw error
  finally harness.stop

end
end CasCatalogue.SyntheticEndpointOccurrenceProbes
