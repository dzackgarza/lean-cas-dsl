/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! An Arrow object's defining map is a complete typed input occurrence. These
engineering controls use the existing arbitrary action process and accepted
forgetful functor. They establish no mathematical answer and introduce no leaf
implementation or mathematical declaration. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.NestedArrowActionProbes
meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def harnessFor (entry : FunctorEntry) (mapAvailable : Bool) :
    TermElabM (Harness × IO.Ref (Array Json)) := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "nested-arrow-probe", command := "python3",
      args := #["probe_functor_execution.py", "action", entry.id.raw] }]
    registrations := #[{
      operation := entry.id.raw, input := entry.inputAddress, backend := "nested-arrow-probe" }] ++
      (if mapAvailable then #[{
        operation := entry.mapAddress, input := entry.inputAddress,
        backend := "nested-arrow-probe" }] else #[]) }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == (if mapAvailable then 2 else 1) do
    throwError "the nested Arrow lost its existing accepted action interfaces"
  return ({ harness with dispatches := some calls, demandObjectActions := true }, calls)

run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the existing structural action control is absent"
  let some sourceRow := state.objects.find? (·.id.raw == "obj.linear_orders.naturals")
    | throwError "the existing structured source is absent"
  let some sourceCategory := state.categories.find? (·.id == sourceRow.category)
    | throwError "the source category is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the target category is absent"
  let trace ← Trace.new
  let source ← Semantic.object sourceRow #[] (some trace)
  let context ← CategoryContext.ofNamed sourceCategory source
  let (image, _) ← Semantic.applyRegisteredFunctor entry source #[] (some trace)
  let targetContext ← CategoryContext.ofNamed sets image
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  let mapped ← Semantic.mapOf action identity
  Trace.record (some trace) mapped
    (.morphismTransport sourceCategory.id sets.id #[.functor entry.id] identity)
  let arrow ← instantiateMVars (← mkAppOptM ``CategoryTheory.Arrow.mk
    #[some (← CategoryContext.carrier targetContext),
      some (← CategoryContext.dictionary targetContext), some image, some image, some mapped])
  Trace.record (some trace) arrow (.contextualArrow targetContext mapped image image)
  let actualSource := node "obj.linear_orders.integers" #[]
  let originalData := Backend.TypedMap.encode {
    source := actualSource, target := actualSource,
    callable := node "identity" #[actualSource, actualSource] }
  let originalObject : Wire := {
    form := .object sourceRow, payload := .computed source (.inline actualSource),
    categoryContext := some context }
  let originalMap : Wire := {
    form := .canonicalMorphism sourceCategory, payload := .computed identity (.inline originalData),
    categoryContext := some context, callableObserved := true }
  let mut failures : Array String := #[]
  for mapAvailable in #[true, false] do
    let (harness, calls) ← harnessFor entry mapAvailable
    harness.results.modify (·.insert source originalObject |>.insert identity originalMap)
    try
      let checked : Except Exception Unit ← try
        let descriptor ← realizeUnobserved harness trace "the complete nested Arrow descriptor" arrow
        unless (← calls.get).isEmpty do
          throwError "forming the Arrow descriptor executed its nested action"
        if mapAvailable then
          let actual ← realizeObjectObservation harness trace descriptor
          let events ← calls.get
          unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
              #[some entry.id.raw, some entry.mapAddress] do
            throwError "the nested Arrow did not observe its selected object and defining-map actions"
          let receipts ← harness.actions.get
          unless receipts.size == 2 && receipts[0]!.result.objectObserved &&
              receipts[1]!.result.callableObserved && receipts[1]!.result.owner?.isSome do
            throwError "the nested Arrow lost actual action data or its supplying session"
          let imageData := receipts[0]!.result.fragment
          let mapData := receipts[1]!.result.fragment
          let expected ← scopedNode "arrow" #[imageData, imageData, mapData]
          unless actual.fragment == expected do
            throwError "the Arrow kept a defining-map recipe or replaced an actual endpoint packet"
          let .ok request := events[1]!.getObjVal? "request"
            | throwError "the nested defining-map action lost its public request"
          let .ok invocation := Backend.PointInvocation.decode request
            | throwError "the nested defining-map action changed its whole-domain interface"
          let .ok ("map", #[_, supplied]) := ComputationalData.envelope invocation.arrow
            | throwError "the nested action lost its original source callable"
          unless supplied == originalData && invocation.source == imageData.json &&
              invocation.target == imageData.json && invocation.domain == imageData.json &&
              invocation.argument == node "identity" #[imageData.json, imageData.json] do
            throwError "the nested Arrow substituted a source name, sampled a domain, or lost an image"
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq (← inferType actual.value) (← inferType arrow) <&&>
                isDefEq actual.value arrow) do
            throwError "observing the nested Arrow changed its complete mathematical value"
          let reused ← realizeObjectObservation harness trace actual
          unless reused.fragment == actual.fragment && (← calls.get).size == 2 do
            throwError "reusing the observed Arrow replayed a primitive action"
        else
          let missing ← try
            discard <| realizeObjectObservation harness trace descriptor
            pure false
          catch error => pure (Exception.stratum? error == some .noImplementation)
          unless missing && (← calls.get).map
              (fun event => (event.getObjValAs? String "operation").toOption) ==
                #[some entry.id.raw] do
            throwError "the nested Arrow hid an absent defining-map action"
        pure (.ok ())
      catch error => pure (.error error)
      let status ← match checked with
        | .ok () => pure "passed"
        | .error error =>
            let message ← error.toMessageData.toString
            failures := failures.push message
            pure message
      if let some path ← IO.getEnv "CAS_NESTED_ARROW_REPORT" then
        IO.FS.withFile path .append fun output => output.putStrLn (Json.mkObj [
          ("case", toJson (if mapAvailable then "nested-arrow" else "missing-map-action")),
          ("status", toJson status),
          ("purpose", "Typed Arrow action engineering control; no mathematical verdict"),
          ("formal", toJson (reprStr arrow)),
          ("dispatches", Json.arr (← calls.get))]).compress
    finally harness.stop
  unless failures.isEmpty do
    throwError "nested Arrow action boundary failed: {failures}"

end
end CasCatalogue.NestedArrowActionProbes
