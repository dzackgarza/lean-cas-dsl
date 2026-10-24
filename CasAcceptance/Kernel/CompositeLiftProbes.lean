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
  let some (actualDomain, target) := homEnds? (← inferType factors.back!.factor) | unreachable!
  unless ← isDefEq actualDomain domain <&&> isDefEq target composedKey do
    throwError "the composed factor changed the original complete cone domain or selected apex"
  for step in factors do
    unless ← Decide.kernelAccepts (← inferType step.proof) step.proof do
      throwError "a composed factor stage lost its accepted formal source equation"
