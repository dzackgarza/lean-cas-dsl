/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for the original occurrences of a dependent
construction map. The mathematics is the existing automorphism construction
on Core(Sets); the process returns arbitrary protocol witnesses. Transparent
data envelopes distinguish cache occurrences without changing the selected
formal category, object, or map. No mathematical answer is asserted. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.ConstructionActionOccurrenceProbes
meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def harnessFor (operation mapAddress inputAddress : String) (mapAvailable : Bool) :
    TermElabM (Harness × IO.Ref (Array Json)) := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "construction-occurrence-probe", command := "python3",
      args := #["probe_functor_execution.py", "action", operation,
        "--opaque-objects", "--bare-maps"] }]
    registrations := #[{
      operation, input := inputAddress, backend := "construction-occurrence-probe" }] ++
      (if mapAvailable then #[{
        operation := mapAddress, input := inputAddress,
        backend := "construction-occurrence-probe" }] else #[]) }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == (if mapAvailable then 2 else 1) do
    throwError "the construction occurrence control lost its existing accepted interfaces"
  return ({ harness with dispatches := some calls, demandObjectActions := true }, calls)

private def report (label status : String) (formal : Expr) (calls : Array Json) :
    TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_CONSTRUCTION_OCCURRENCE_REPORT" then
    IO.FS.withFile path .append fun output => output.putStrLn (Json.mkObj [
      ("case", toJson label), ("status", toJson status),
      ("formal", toJson (reprStr formal)),
      ("purpose", "Dependent construction occurrence engineering control; no mathematical verdict"),
      ("dispatches", Json.arr calls)]).compress

run_elab do
  let state ← registryState
  let some entry := state.constructions.find? (·.id.raw == "con.automorphisms")
    | throwError "the existing dependent construction is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set category is absent"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the existing finite object is absent"
  let trace ← Trace.new
  let category ← elabTermAndSynthesize (← `(LeanCategories.Foundation.Mathlib.Sets.{0})) none
  Trace.record (some trace) category (.categoryParameter sets.id #[])
  let underlying ← Semantic.object finite #[← `(2)] (some trace)
  let setContext ← CategoryContext.ofNamed sets underlying
  let context ← CategoryContext.construct setContext ConstructorId.core
  let source ← instantiateMVars (← mkAppM ``CategoryTheory.Core.mk #[underlying])
  Trace.record (some trace) source (.coreObject setContext underlying)
  let identity ← instantiateMVars (← mkAppM ``CategoryTheory.CategoryStruct.id #[source])
  let selected ← DirectConstruction.select entry #[← exprToSyntax category] source
  let formal ← instantiateMVars (← DirectConstruction.map selected source source identity)
  Trace.record (some trace) formal (.constructionMap entry.id #[category] source source identity)
  let categoryData := node "category" #[toJson sets.id.raw, Json.arr #[]]
  let supplied := node "core" #[node finite.id.raw #[toJson (2 : Nat)]]
  let replacement := node "valueData" #[supplied]
  let replacementCategory := node "valueData" #[categoryData]
  -- Both parameter packets have the same fixed declared category. Only the
  -- occurrence placed in the cache later differs.
  for data in #[categoryData, replacementCategory] do
    if let .error message ← ComputationalData.validateAction selected.functor
        (node entry.id.raw #[data]) then
      throwError "the construction parameter control has invalid framing: {message}"
  let mapData := fun endpoint => Backend.TypedMap.encode {
    source := endpoint, target := endpoint,
    callable := node "identity" #[endpoint, endpoint] }
  let originalCategory : Wire := {
    form := .diagrams sets, payload := .computed category (.inline categoryData) }
  let originalObject : Wire := {
    form := contextualForm state context (.diagrams sets),
    payload := .computed source (.inline supplied), categoryContext := some context }
  let originalMap : Wire := {
    form := contextualForm state context originalObject.form true,
    payload := .computed identity (.inline (mapData supplied)),
    categoryContext := some context, callableObserved := true }
  let mut failures : Array String := #[]
  for mapAvailable in #[true, false] do
    let label := if mapAvailable then "construction-original-occurrences" else "construction-missing-map"
    let (harness, calls) ← harnessFor entry.id.raw entry.mapAddress entry.inputAddress mapAvailable
    try
      let checked : Except Exception Unit ← try
        harness.results.modify (·.insert category originalCategory
          |>.insert source originalObject |>.insert identity originalMap)
        let pending ← realizeUnobserved harness trace "the original dependent construction map" formal
        unless (← calls.get).isEmpty do
          throwError "preparing the construction map executed a primitive action"
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType pending.value) (← inferType formal) <&&>
              isDefEq pending.value formal) do
          throwError "preparing the construction map changed its fixed mathematical request"
        report label "prepared-before-cache-replacement" formal (← calls.get)
        harness.results.modify (·.insert category { originalCategory with
            payload := .computed category (.inline replacementCategory) }
          |>.insert source { originalObject with payload := .computed source (.inline replacement) }
          |>.insert identity { originalMap with
            payload := .computed identity (.inline (mapData replacement)) })
        let actual ← if mapAvailable then
          some <$> realizeArrowObservation harness trace pending
        else do
          let missing ← try
            discard <| realizeArrowObservation harness trace pending
            pure false
          catch error => pure (Exception.stratum? error == some .noImplementation)
          unless missing do throwError "the construction hid its absent map registration"
          pure none
        let events ← calls.get
        let expected := if mapAvailable then #[some entry.id.raw, some entry.mapAddress]
          else #[some entry.id.raw]
        unless events.map (fun event => (event.getObjValAs? String "operation").toOption) == expected do
          throwError "the construction did not preserve its ordered primitive dispatch boundary"
        let .ok objectRequest := events[0]!.getObjVal? "request"
          | throwError "the construction object image lost its public request"
        unless (objectRequest.getObjVal? "receiver").toOption == some supplied &&
            (objectRequest.getObjVal? "args").toOption == some (Json.arr #[categoryData]) do
          throwError "construction action replaced a captured source or category parameter from the cache"
        if let some actual := actual then
          let .ok mapRequest := events[1]!.getObjVal? "request"
            | throwError "the construction map lost its public request"
          let .ok invocation := Backend.PointInvocation.decode mapRequest
            | throwError "the construction map lost its complete whole-domain invocation"
          let .ok ("map", #[descriptor, original]) := ComputationalData.envelope invocation.arrow
            | throwError "the construction map lost its original full callable"
          unless descriptor == node entry.id.raw #[categoryData] &&
              invocation.parameters == #[categoryData] && original == mapData supplied do
            throwError "construction map replaced its captured callable or selected parameter occurrence"
          let receipts ← harness.actions.get
          unless receipts.size == 2 && actual.owner?.isSome &&
              actual.owner? == receipts[1]!.result.owner? do
            throwError "the construction result lost its exact supplying session"
          let (imageSource, _) ← contextualMorphismEndpoints selected.target actual.value
          let endpoint ← actionMapEndpoint harness trace actual (some selected.target) imageSource true
          unless endpoint.fragment == receipts[0]!.result.fragment do
            throwError "the returned construction map replaced its actual object image from the cache"
          let reused ← realizeArrowObservation harness trace actual
          unless reused.fragment == actual.fragment && (← calls.get).size == 2 do
            throwError "reusing the actual construction map replayed a primitive"
        pure (.ok ())
      catch error => pure (.error error)
      let status ← match checked with
        | .ok () => pure "passed"
        | .error error =>
          let message ← error.toMessageData.toString
          failures := failures.push message
          pure message
      report label status formal (← calls.get)
    finally harness.stop
  unless failures.isEmpty do
    throwError "construction occurrence boundary failed: {failures}"

end
end CasCatalogue.ConstructionActionOccurrenceProbes
