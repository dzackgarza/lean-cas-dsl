/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Optional engineering checks against the independently published extension input.
This module is built with that mathematical input's isolated package override. Opaque
packets test framing and reuse; no packet establishes a mathematical value or law. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue CasCatalogue.Language

private def parse (text : String) : TermElabM Syntax := do
  let .ok result := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the public composite lift form did not parse: {text}"
  return result

private def envelope (name : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson name), ("args", Json.arr arguments)]

private def opaqueField (name : String) : Json := envelope "opaqueData" #[toJson name]

private def recordSelection (trace : Trace) (plan : SelectedLift.Plan) : TermElabM Expr := do
  let selected ← SelectedLift.retainSelection plan.ports[0]!
  Trace.record (some trace) selected
    (.selectedLift plan.entry.id plan.parameters plan.source plan.inclusion plan.monic)
  return selected

private def cachePacket (harness : Realize.Harness) (plan : SelectedLift.Plan)
    (formal : Expr) (label : String) (source base : Json) :
    TermElabM Realize.LiftExecution := do
  let state ← registryState
  let .functor id ← SelectedLift.innerEdge state plan.entry
    | throwError "the accepted fixture no longer has its published inner action"
  let parameters := (List.range plan.parameters.size).toArray.map fun i =>
    opaqueField s!"{label}: complete parameter {i}"
  let action := envelope id.raw parameters
  let object := opaqueField s!"{label}: actual returned object"
  let image := envelope "functorAction" #[action, object]
  let .ok baseFields := LiftedSubobjectData.subobjectFields base
    | throwError "the fixture lost its full actual base packet"
  let typed (source target : Json) (name : String) :=
    envelope "typedMap" #[source, target, opaqueField s!"{label}: {name}"]
  let outputs := #[object, typed object source "actual defining map",
    typed image baseFields[0]! "actual forward", typed baseFields[0]! image "actual backward"]
  if let .error message ← LiftedSubobjectData.validateSelectionPrefix
      plan action source base outputs then
    throwError "the complete retained fixture is malformed: {message}"
  let execution : Realize.LiftExecution := {
    selections := #[plan], actions := #[action], parameters := #[parameters],
    sources := #[source], bases := #[base], outputs := #[outputs] }
  let some form := state.liftInputForm? plan.entry.inputAddress
    | throwError "the accepted fixture lost its published input form"
  let context ← SelectedLift.context plan
  harness.results.modify (·.insert formal {
    form := Realize.contextualForm state context form
    payload := Realize.dataPayload formal object (some ("composite-probe", 29))
    liftExecution := some execution, categoryContext := some context })
  return execution

run_elab do
  let state ← registryState
  let some innerRow := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "the accepted inner lift is absent"
  let some outerRow := state.lifts.find?
      (·.id.raw == "lift.bilin_module.change_value_restriction")
    | throwError "the independently published outer lift is absent"
  let innerSource ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.source)) none
  let outerSource ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.pairedSource)) none
  let inclusion ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion)) none
  let innerEvidence ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstLift)) none
  let outerEvidence ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.secondLift)) none
  let inner ← SelectedLift.fromEvidence innerRow innerEvidence innerSource inclusion
    (← synthInstance (← mkAppM ``CategoryTheory.Mono #[inclusion]))
  let trace ← Trace.new
  let innerKey ← recordSelection trace inner
  let innerHom ← StructuredProjection.retainPortValue innerKey inner.ports[1]! 1
  Trace.record (some trace) innerHom (.liftProjection innerKey "hom")
  let outer ← SelectedLift.fromEvidence outerRow outerEvidence outerSource innerHom
    (← SelectedLift.homMonic inner)
  let outerKey ← recordSelection trace outer
  unless (← SelectedLift.recorded trace outerKey).plans.size == 1 &&
      (← SelectedLift.recorded trace outerKey true).plans.size == 2 do
    throwError "explicit composition changed the ordinary single-stage reading"
  let refused ← try
    SelectedLift.checkAdjacent outer { inner with source := outerSource }
    pure false
  catch error => pure (Exception.interpretationKind error == .invalid)
  unless refused do throwError "a composed selection accepted a different adjacent full context"
  let context ← SelectedLift.context outer
  let selected ← (objectInContext outerKey context).run { trace := some trace }
  let bound := [(`L, selected)]
  let composite ← (eval {} (← parse "composite_lift(L)")).run { trace := some trace, bound }
  let composedKey ← (semanticObject composite).run {}
  unless composedKey != outerKey && (← isDefEq composedKey outerKey) do
    throwError "the composed selection lost its separate administrative identity"
  let plans := (← SelectedLift.recorded trace composedKey).plans
  unless plans.size == 2 do throwError "the public composed selection lost a stage"
  let harness ← Realize.Harness.empty
  let innerSourceData := opaqueField "actual intermediate source"
  let innerBase := envelope "subobject" #[opaqueField "original base apex",
    opaqueField "original base ambient", opaqueField "original base inclusion"]
  let innerExecution ← cachePacket harness inner innerKey "inner" innerSourceData innerBase
  let outerBase := envelope "subobject" #[(innerExecution.outputs[0]!)[0]!,
    innerSourceData, (innerExecution.outputs[0]!)[1]!]
  let outerExecution ← cachePacket harness outer outerKey "outer"
    (opaqueField "original complete source") outerBase
  let completed ← Realize.realize harness trace "the complete composed selection" composedKey
  let some execution := completed.liftExecution
    | throwError "the composed value discarded its complete execution"
  unless completed.owner? == some ("composite-probe", 29) &&
      execution.outputs == outerExecution.outputs ++ innerExecution.outputs &&
      execution.parameters == outerExecution.parameters ++ innerExecution.parameters &&
      execution.sources == outerExecution.sources ++ innerExecution.sources &&
      execution.bases == outerExecution.bases ++ innerExecution.bases &&
      execution.actions == outerExecution.actions ++ innerExecution.actions do
    throwError "composed selection replaced an actual retained input, output, action or owner"
  let (_, unchanged) ← Realize.retainedLiftExecution harness trace outerKey
  unless unchanged.selections.size == 1 && unchanged.outputs == outerExecution.outputs do
    throwError "composed reuse changed the ordinary outer selection"
  for (index, field) in #["obj", "hom", "forward", "backward"].zipIdx do
    let projected ← (eval {} (← parse s!"C.{index}()")).run
      { trace := some trace, bound := [(`C, composite)] }
    let value ← match projected with
      | .object value .. | .derivedObject value .. |
          .morphism value .. | .derivedMorphism value .. => pure value
      | _ => throwError "the composed projection lost its complete typed value"
    unless ← isDefEq value (← SelectedLift.port plans field) do
      throwError "a composed field changed its accepted full functor-map expression"
    let wire ← Realize.realize harness trace "a reused composed lift projection" value
    unless wire.owner? == completed.owner? &&
        wire.json == (← Realize.liftProjectionData execution field) do
      throwError "a composed field replayed or replaced its retained actual packet"
  let baseMap ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.baseMediator)) none
  let cone ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.pairedCone)) none
  let proof ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone_base_factorization)) none
  let factors ← SelectedLift.factors plans baseMap cone proof
  unless factors.size == 2 do throwError "the composed factor omitted a selected stage"
  let some (domain, _) := homEnds? (← inferType cone) | unreachable!
  let some final := factors.back? | unreachable!
  let some (actualDomain, target) := homEnds? (← inferType final.factor) | unreachable!
  unless ← isDefEq actualDomain domain <&&> isDefEq target composedKey do
    throwError "the composed factor changed the original complete cone domain or selected apex"
  for step in factors do
    unless ← Decide.kernelAccepts (← inferType step.proof) step.proof do
      throwError "a composed factor stage lost its accepted formal source equation"

-- Exercise the actual public port as well as retained-packet reuse. Arbitrary
-- opaque replies witness data flow only; the independent fixture fixes every
-- selected formal object, action, original domain and compatibility proof.
run_elab do
  let state ← registryState
  let some innerRow := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "the accepted inner lift is absent"
  let some outerRow := state.lifts.find?
      (·.id.raw == "lift.bilin_module.change_value_restriction")
    | throwError "the independently published outer lift is absent"
  let innerSource ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.source)) none
  let outerSource ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.pairedSource)) none
  let inclusion ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion)) none
  let innerEvidence ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstLift)) none
  let outerEvidence ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.secondLift)) none
  let inner ← SelectedLift.fromEvidence innerRow innerEvidence innerSource inclusion
    (← synthInstance (← mkAppM ``CategoryTheory.Mono #[inclusion]))
  let trace ← Trace.new
  let innerKey ← recordSelection trace inner
  let innerHom ← StructuredProjection.retainPortValue innerKey inner.ports[1]! 1
  Trace.record (some trace) innerHom (.liftProjection innerKey "hom")
  let outer ← SelectedLift.fromEvidence outerRow outerEvidence outerSource innerHom
    (← SelectedLift.homMonic inner)
  let outerKey ← recordSelection trace outer
  let context ← SelectedLift.context outer
  let selected ← (objectInContext outerKey context).run { trace := some trace }
  let composite ← (eval {} (← parse "composite_lift(L)")).run
    { trace := some trace, bound := [(`L, selected)] }
  let composedKey ← (semanticObject composite).run {}
  let rows := #[innerRow, outerRow]
  let operations := rows.flatMap fun row =>
    LiftField.all.map row.fieldAddress |>.push row.factorAddress
  let manifest : Manifest := {
    backends := #[{
      name := "lift-probe"
      command := "python3"
      args := #["probe_lift_protocol.py"] ++ operations }]
    registrations := rows.flatMap fun row =>
      (LiftField.all.map row.fieldAddress |>.push row.factorAddress).map fun operation =>
        { operation, input := row.inputAddress, backend := "lift-probe" } }
  let observations ← IO.mkRef #[]
  let harness ← Realize.Harness.ofManifest ("CasAcceptance" / "Strata") manifest
  let harness := { harness with dispatches := some observations }
  unless harness.rejected.isEmpty && harness.admitted.size == operations.size do
    throwError "a public selected lift address was not admitted: {reprStr harness.rejected}"
  try
    let .ok session ← harness.connection "lift-probe"
      | throwError "the protocol-only lift probe did not start"
    let owner := some ("lift-probe", session.identity)
    let some inputForm := state.liftInputForm? innerRow.inputAddress
      | throwError "the accepted input form is absent"
    let seed := fun formal label => do
      if (← harness.results.get).contains formal then return
      harness.results.modify (·.insert formal {
        form := inputForm
        payload := Realize.computedPayload formal (opaqueField label) owner })
    for plan in #[inner, outer] do
      seed plan.source s!"actual original source of {plan.entry.id.raw}"
      for (parameter, index) in plan.parameters.zipIdx do
        unless ← isProp (← inferType parameter) do
          seed parameter s!"actual selection parameter {index} of {plan.entry.id.raw}"
    let some (baseSource, baseTarget) := homEnds? (← inferType inclusion)
      | throwError "the fixed original inclusion lost its complete endpoints"
    seed inclusion "actual original inclusion"
    seed baseSource "actual original base apex"
    seed baseTarget "actual original base ambient"
    let innerWire ← Realize.realize harness trace "the first actual selection" innerKey
    let outerWire ← Realize.realize harness trace "the second actual selection" outerKey
    let some innerExecution := innerWire.liftExecution
      | throwError "the first actual selection lost its four returned fields"
    let some outerExecution := outerWire.liftExecution
      | throwError "the second actual selection lost its four returned fields"
    let calls ← observations.get
    unless calls.size == 8 do
      throwError "two selected lifts did not execute exactly their eight public field calls"
    for (execution, offset) in #[(innerExecution, 0), (outerExecution, 4)] do
      let some plan := execution.selections[0]? | unreachable!
      let original := if offset == 0 then inner else outer
      let expectedParameters ← original.parameters.filterMapM fun parameter => do
        if ← isProp (← inferType parameter) then return none
        let some actual := (← harness.results.get)[parameter]?
          | throwError "a supplied selected parameter lost its original actual data"
        return some actual.json
      unless execution.parameters[0]! == expectedParameters do
        throwError "a selected lift omitted or replaced an explicit evidence-family parameter"
      for (field, index) in LiftField.all.zipIdx do
        let call := calls[offset + index]!
        let .ok request := call.getObjVal? "request" | unreachable!
        let .ok response := call.getObjVal? "response" | unreachable!
        let .ok invocation := Backend.LiftInput.decode request (plan.entry.fieldAddress field)
          | throwError "a selected field lost its public complete request"
        unless call.getObjValAs? String "operation" ==
            .ok (plan.entry.fieldAddress field) &&
            invocation.outputs == execution.outputs[0]!.extract 0 index &&
            invocation.parameters == execution.parameters[0]! &&
            response == (execution.outputs[0]!)[index]! do
          throwError "a selected field replayed or replaced an actual preceding output or parameter"
    let .ok outerBase := LiftedSubobjectData.subobjectFields outerExecution.bases[0]!
      | throwError "the second actual lift lost its first stage base packet"
    unless outerBase[0]! == (innerExecution.outputs[0]!)[0]! &&
        outerBase[2]! == (innerExecution.outputs[0]!)[1]! do
      throwError "the second selected lift did not consume the first actual object and defining map"
    let composed ← Realize.realize harness trace "the actual composed selection" composedKey
    let some execution := composed.liftExecution
      | throwError "the actual composed selection lost a retained stage"
    unless composed.owner? == owner && execution.selections.size == 2 &&
        (← observations.get).size == 8 do
      throwError "composition reran a selected port or lost its actual owning session"
    let baseMap ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.baseMediator)) none
    let cone ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.pairedCone)) none
    let proof ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone_base_factorization))
      none
    let some (domain, _) := homEnds? (← inferType cone)
      | throwError "the independently selected cone lost its original generalized domain"
    seed baseMap "actual original base mediator"
    seed cone "actual original complete cone"
    seed domain "actual original generalized domain"
    let factors ← SelectedLift.factors execution.selections baseMap cone proof
    let some final := factors.back? | unreachable!
    Trace.record (some trace) final.factor (.liftFactor composedKey baseMap cone proof)
    let answer ← Realize.realize harness trace "the actual composed universal factor" final.factor
    let calls ← observations.get
    unless calls.size == 10 do
      throwError "the composed factor did not execute exactly one declared factor per stage"
    let .ok firstRequest := calls[8]!.getObjVal? "request" | unreachable!
    let .ok secondRequest := calls[9]!.getObjVal? "request" | unreachable!
    let .ok first := Backend.LiftFactorInput.decode firstRequest innerRow.factorAddress
      | throwError "the first factor request lost its complete public frame"
    let .ok second := Backend.LiftFactorInput.decode secondRequest outerRow.factorAddress
      | throwError "the final factor request lost its complete public frame"
    let .ok firstReply := calls[8]!.getObjVal? "response" | unreachable!
    unless first.lift == innerRow.id.raw && second.lift == outerRow.id.raw &&
        first.outputs == innerExecution.outputs[0]! &&
        second.outputs == outerExecution.outputs[0]! &&
        first.parameters == innerExecution.parameters[0]! &&
        second.parameters == outerExecution.parameters[0]! &&
        second.baseMap.encode == firstReply do
      throwError "the staged factor replaced an actual previous reply, selection or parameter"
    let some actualDomain := (← harness.results.get)[domain]? | unreachable!
    let .ok finalData := Backend.TypedMap.decode answer.json
      | throwError "the final actual factor lost its complete endpoint frame"
    unless finalData.source == actualDomain.json &&
        finalData.target == (outerExecution.outputs[0]!)[0]! && answer.owner? == owner do
      throwError "the final factor changed its original complete domain, selected apex or owner"
    let again ← Realize.realize harness trace "the reused actual composed factor" final.factor
    unless again.json == answer.json && (← observations.get).size == 10 do
      throwError "reuse replaced the returned composite factor or executed it again"
  finally
    harness.stop
