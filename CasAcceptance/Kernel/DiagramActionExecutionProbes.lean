/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for registered actions nested in a limit's input
diagram. Both executions use one independently fixed formal diagram. The
unchanged protocol fixtures supply arbitrary computational images; neither
their sizes nor their resulting cone establishes a mathematical assertion.
No mathematical declaration or leaf implementation is introduced here. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.DiagramActionExecutionProbes
meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def harnessFor (action : FunctorEntry) (limit : LimitEntry)
    (complete : Bool) : TermElabM (Harness × IO.Ref (Array Json)) := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[
      { name := "diagram-action-probe", command := "python3",
        args := #["probe_functor_execution.py", "action", action.id.raw] },
      { name := "diagram-target-probe", command := "python3",
        args := #["probe_registration.py", "--answer=correct"] }]
    registrations := (if complete then #[{
      operation := action.id.raw, input := action.inputAddress,
      backend := "diagram-action-probe" }] else #[]) ++ #[{
      operation := limit.id.raw, input := limit.category.raw,
      backend := "diagram-target-probe" }] }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == (if complete then 2 else 1) do
    throwError "the existing action and category-wide limit ports were not admitted"
  return ({ harness with dispatches := some calls, demandObjectActions := true }, calls)

private def recordEvidence (label status : String) (diagram formal : Expr)
    (harness : Harness) (calls : IO.Ref (Array Json)) : TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_DIAGRAM_ACTION_REPORT" then
    let actions := (← harness.actions.get).map fun receipt => Json.mkObj [
      ("operation", toJson receipt.operation),
      ("source", receipt.input.json),
      ("sourceOwnership", toJson receipt.input.ownership),
      ("result", receipt.result.json),
      ("resultOwnership", toJson receipt.result.ownership)]
    let report := Json.mkObj [
      ("case", toJson label), ("status", toJson status),
      ("purpose", "Engineering diagram/action framing; no mathematical verdict"),
      ("formalDiagram", toJson (reprStr diagram)),
      ("formalResult", toJson (reprStr formal)),
      ("formalResultType", toJson (reprStr (← inferType formal))),
      ("dispatches", Json.arr (← calls.get)), ("actions", Json.arr actions)]
    IO.FS.withFile path .append fun output => output.putStrLn report.compress

run_elab do
  let state ← registryState
  let trace ← Trace.new
  let some action := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the existing structural action control is absent"
  unless action.structural do
    throwError "the nested diagram control no longer selects a structural action"
  let some limit := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "the existing target-category product is absent"
  let mut sources : Array Wire := #[]
  let mut images : Array Expr := #[]
  -- Keep the returned source packets distinct from the named formal sources.
  -- They are untrusted data at the existing complete LinearOrders interface.
  for (name, actualName) in #[
      ("obj.linear_orders.naturals", "obj.linear_orders.integers"),
      ("obj.linear_orders.integers", "obj.linear_orders.naturals")] do
    let some row := state.objects.find? (·.id.raw == name)
      | throwError "the existing diagram source {name} is absent"
    let some category := state.categories.find? (·.id == row.category)
      | throwError "the diagram source lost its complete registered category"
    let source ← Semantic.object row #[] (some trace)
    let context ← CategoryContext.ofNamed category source
    let actual := node actualName #[]
    if let .error message ← ComputationalData.validatePort source (← inferType source) actual then
      throwError "the original diagram source packet is malformed: {message}"
    sources := sources.push {
      form := .object row, payload := .computed source (.inline actual),
      categoryContext := some context }
    let (image, target) ← Semantic.applyRegisteredFunctor action source #[] (some trace)
    unless target.id == limit.category do
      throwError "the independently selected action does not target the limit's category"
    images := images.push image
  let diagram ← instantiateMVars (← mkAppM ``CategoryTheory.Limits.pair images)
  let presentation ← Semantic.limit false limit.shape diagram limit.category.raw (some trace)
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let formal ← instantiateMVars (← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone])
  Trace.alias (some trace) presentation formal
  let originalNode ← trace.node? formal
  unless originalNode == some (.limit limit.id diagram none) &&
      !formal.hasMVar && !formal.hasLevelMVar && !diagram.hasMVar && !diagram.hasLevelMVar do
    throwError "the control lacks one closed independently selected product diagram"
  let originalType ← instantiateMVars (← inferType formal)
  let mut failures : Array String := #[]
  for complete in #[true, false] do
    let label := if complete then "nested-action-target-diagram" else "missing-nested-action"
    let (harness, calls) ← harnessFor action limit complete
    for source in sources do
      harness.results.modify (·.insert source.value source)
    try
      let checked : Except Exception Unit ← try
        if complete then
          let actual ← realize harness trace "the fixed action-image product" formal
          let events ← calls.get
          unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
              #[some action.id.raw, some action.id.raw, some limit.id.raw] do
            throwError "the target limit did not follow both ordered primitive object actions"
          let receipts ← harness.actions.get
          unless receipts.size == 2 do
            throwError "the diagram did not retain its two actual object-action receipts"
          let expectedImages := #[node "obj.sets.fin" #[toJson (7 : Nat)],
            node "obj.sets.fin" #[toJson (8 : Nat)]]
          for index in [:2] do
            let receipt := receipts[index]!
            let source := sources[index]!
            unless receipt.operation == action.id.raw &&
                receipt.input.value == source.value && receipt.input.fragment == source.fragment &&
                receipt.result.objectObserved && receipt.result.ownership.isEmpty &&
                receipt.result.json == expectedImages[index]! do
              throwError "a nested action changed its actual source occurrence or returned image"
            unless ← withoutModifyingState (withTransparency .all <|
                isDefEq (← inferType receipt.result.value) (← inferType images[index]!) <&&>
                  isDefEq receipt.result.value images[index]!) do
              throwError "a computational action changed its independently fixed formal image"
            let event := events[index]!
            let .ok request := event.getObjVal? "request"
              | throwError "the nested action lost its actual request"
            unless (request.getObjVal? "receiver").toOption == some source.json &&
                (event.getObjVal? "response").toOption ==
                  some (node "valueData" #[receipt.result.json]) do
              throwError "the nested action receipt does not retain its actual request and reply"
          let expectedDiagram := node "pair" (receipts.map (·.result.json))
          let targetEvent := events[2]!
          unless (targetEvent.getObjVal? "request").toOption == some expectedDiagram &&
              (targetEvent.getObjValAs? String "registrationInput").toOption ==
                some limit.category.raw &&
              (targetEvent.getObjValAs? String "backend").toOption ==
                some "diagram-target-probe" do
            throwError "the category-wide limit received action recipes instead of ordered actual images"
          let .construction result _ := actual.payload
            | throwError "the product lost its complete returned construction packet"
          unless result.diagramJson == expectedDiagram do
            throwError "the retained construction did not preserve its actual dispatched diagram"
          unless ← withoutModifyingState (withTransparency .all <| isDefEq result.diagram diagram) do
            throwError "computational diagram observation changed the formal construction"
          let reused ← realize harness trace "the same retained action-image product" formal
          unless reused.fragment == actual.fragment && (← calls.get).size == 3 do
            throwError "reusing the product replayed a primitive action or its construction"
        else
          let missing ← try
            discard <| realize harness trace "the same product with no primitive action" formal
            pure false
          catch error => pure (Exception.stratum? error == some .noImplementation)
          unless missing && (← calls.get).isEmpty && (← harness.actions.get).isEmpty do
            throwError "an absent nested action reached the target limit or changed its failure stratum"
        unless (← trace.node? formal) == originalNode &&
            (← instantiateMVars (← inferType formal)) == originalType do
          throwError "changing computational availability changed the original formal diagram or result type"
        pure (.ok ())
      catch error => pure (.error error)
      match checked with
      | .ok () => recordEvidence label "passed" diagram formal harness calls
      | .error error =>
          let message ← error.toMessageData.toString
          recordEvidence label message diagram formal harness calls
          failures := failures.push s!"{label}: {message}"
    finally harness.stop
  unless failures.isEmpty do
    throwError "nested diagram action boundary failed: {failures}"

end
end CasCatalogue.DiagramActionExecutionProbes
