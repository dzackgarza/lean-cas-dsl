/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering control for computational endpoint comparisons. The accepted
product-swap Iso fixes a non-definitional presentation. The existing list-action
protocol fixture supplies opaque object and map results. This checks occurrence
and session plumbing, not a mathematical answer or new registration. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.EndpointComparisonOccurrenceProbes
meta section

private def swapGraph (source : DataOwnership.Data) : TermElabM Json := do
  let .ok (some keys) ← ComputationalData.endpointKeys source.json
    | throwError "the comparison control lost its public finite inventory"
  let rows ← keys.mapM fun key => do
    let .ok fields := key.getArr?
      | throwError "the comparison control lost an ordered product key"
    unless fields.size == 2 do
      throwError "the comparison control changed a complete product key"
    return Json.arr #[key, Json.arr #[fields[1]!, fields[0]!]]
  return Json.mkObj [("ctor", "finiteGraph"), ("args", Json.arr #[Json.arr keys, Json.arr rows])]

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted set category is absent"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the accepted finite-object declaration is absent"
  let some entry := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the accepted list action is absent"
  let trace ← Trace.new
  let empty ← Harness.empty
  let X ← Semantic.object finite #[← `(2)] (some trace)
  let Y ← Semantic.object finite #[← `(3)] (some trace)
  let semantic ← mkAppM ``Prod #[X, Y]
  let actual ← mkAppM ``Prod #[Y, X]
  let context ← CategoryContext.ofNamed sets semantic
  let semanticWire ← realizeEndpoint empty trace "the original comparison endpoint" semantic
  let actualWire ← realizeEndpoint empty trace "the selected comparison endpoint" actual
  let comparison ← mkAppM ``Equiv.toIso #[← mkAppM ``Equiv.prodComm #[X, Y]]
  let makeMap := fun (formal : Expr) (source target : Wire) => do
    let data ← scopedNode "typedMap"
      #[source.fragment, target.fragment, { json := ← swapGraph source.fragment }]
    let wire : Wire := {
      form := .canonicalMorphism sets,
      payload := (← scopedPayload formal data), categoryContext := some context,
      callableObserved := true, morphismFramed := true }
    retainCallableEndpoints wire source target context
  let forward ← makeMap (← mkAppM ``CategoryTheory.Iso.hom #[comparison]) semanticWire actualWire
  let backward ← makeMap (← mkAppM ``CategoryTheory.Iso.inv #[comparison]) actualWire semanticWire
  let source : Wire := {
    form := .diagrams sets, payload := (← scopedPayload semantic actualWire.fragment),
    categoryContext := some context, objectObserved := true }
  let source ← retainEndpointPresentationMaps source context comparison forward backward
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  let formal ← Semantic.objOf action semantic
  let targetContext ← CategoryContext.ofNamed sets formal
  let descriptor : ActionDataTemplate := .ctor entry.id.raw #[]
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "endpoint-comparison-probe", command := "python3",
      args := #["probe_functor_execution.py", "action", entry.id.raw,
        "--opaque-objects", "--bare-maps"] }]
    registrations := #[
      { operation := entry.id.raw, input := entry.inputAddress, backend := "endpoint-comparison-probe" },
      { operation := entry.mapAddress, input := entry.inputAddress, backend := "endpoint-comparison-probe" }] }
  let harness ← Harness.ofManifest root manifest
  let calls ← IO.mkRef #[]
  let harness := { harness with dispatches := some calls, demandObjectActions := true }
  unless harness.rejected.isEmpty && harness.admitted.size == 2 do
    throwError "the comparison control lost its accepted primitive interfaces"
  try
    let pending ← captureRegisteredObjectAction (.edge (.functor entry.id)) action source
      formal (imageForm state (.functor entry.id) sets) targetContext descriptor
    unless (← calls.get).isEmpty do
      throwError "capturing a comparison continuation executed an action"
    -- The retained comparison and endpoint Wires own their exact packets;
    -- an equal formal key subsequently bound to another packet selects nothing.
    harness.results.modify (·.insert semantic semanticWire)
    let endpoint ← realizeObjectObservation harness trace pending
    let firstEvents ← calls.get
    unless firstEvents.size == 1 && endpoint.owner?.isSome do
      throwError "the selected endpoint action did not retain its opaque result owner"
    let identity ← identityAtContext targetContext formal
    let rawData ← scopedNode "identity" #[endpoint.fragment, endpoint.fragment]
    let raw : Wire := {
      form := .canonicalMorphism sets, payload := (← scopedPayload identity rawData),
      categoryContext := some targetContext }
    let framed ← frameObservedMorphism harness trace raw endpoint endpoint (some targetContext)
    let events ← calls.get
    unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
        #[some entry.id.raw, some entry.id.raw, some entry.mapAddress, some entry.mapAddress] do
      throwError "framing did not execute the exact retained comparison directions"
    let .ok inverseRequest := events[2]!.getObjVal? "request"
      | throwError "the inverse comparison lost its public request"
    let .ok forwardRequest := events[3]!.getObjVal? "request"
      | throwError "the forward comparison lost its public request"
    let .ok inverseInvocation := Backend.PointInvocation.decode inverseRequest
      | throwError "the inverse comparison lost its complete map invocation"
    let .ok forwardInvocation := Backend.PointInvocation.decode forwardRequest
      | throwError "the forward comparison lost its complete map invocation"
    unless inverseInvocation.source == endpoint.json && forwardInvocation.target == endpoint.json &&
        inverseInvocation.target == forwardInvocation.source &&
        inverseInvocation.target != endpoint.json do
      throwError "a comparison recomputed or replaced the endpoint's actual opaque image occurrence"
    let some frame := framed.morphismFraming
      | throwError "the executed frame lost its exact producer inputs"
    unless sameCompleteWireContext frame.source endpoint && sameCompleteWireContext frame.target endpoint do
      throwError "comparison execution replaced an original endpoint occurrence"
    let some (some inverse, some forward) := frame.comparisons
      | throwError "the executed frame lost one selected comparison result"
    unless inverse.completedData && forward.completedData &&
        inverse.owner? == endpoint.owner? && forward.owner? == endpoint.owner? do
      throwError "the complete comparison results lost their actual supplying session"
    let reused ← realizeArrowObservation harness trace framed
    unless reused.fragment == framed.fragment && (← calls.get).size == 4 do
      throwError "reusing a completed comparison frame replayed its actions"
    if let some path ← IO.getEnv "CAS_ENDPOINT_COMPARISON_REPORT" then
      IO.FS.withFile path .append fun output => output.putStrLn (Json.mkObj [
        ("case", "mapped-nonidentity-comparison-occurrences"),
        ("purpose", "Typed occurrence and ownership control; no mathematical verdict"),
        ("dispatches", Json.arr events)]).compress
  finally harness.stop

end
end CasCatalogue.EndpointComparisonOccurrenceProbes
