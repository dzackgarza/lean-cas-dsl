/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
import LeanCategories.Catalogue.Semantics.Limits.Lifts
import Mathlib.Algebra.Algebra.Bilinear

/-! Engineering controls for the actual parameters of a prescribed lift action.
The existing protocol-only helper supplies arbitrary opaque data-flow fields.
No returned packet establishes a mathematical answer or categorical law. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue

private def envelope (name : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson name), ("args", Json.arr arguments)]

private def opaqueField (name : String) : Json := envelope "opaqueData" #[toJson name]

run_elab do
  let state ← registryState
  let some sourceCategory := state.categories.find?
      (·.id.raw == "cat.subobjects_bilin_module")
    | throwError "the accepted formed-module subobject category is absent"
  let some row := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "the accepted dependent lift is absent"
  -- Reuse the complete one-stage formal fixture from LiftedSubobjectDataProbes.
  let X ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ (ℤ × ℤ) ℤ))) none
  let selectedSource ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleCategory ℤ ℤ)) none
  let selectedCarrier ← mkAppM ``CategoryTheory.Bundled.α #[selectedSource]
  let selectedX ← mkExpectedTypeHint X selectedCarrier
  let evidence ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.Kernels.forgetMonoLift ℤ ℤ)) none
  let liftType ← whnfR (← inferType evidence)
  let #[_, selectedCategory, _, _, _] := liftType.getAppArgs
    | throwError "the accepted lift omitted its full source category dictionary"
  let sourceArrow ← mkAppOptM ``CategoryTheory.Arrow
    #[some selectedCarrier, some selectedCategory]
  let sourceStruct ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some selectedCarrier, some selectedCategory]
  let identity ← mkAppOptM ``CategoryTheory.CategoryStruct.id
    #[some selectedCarrier, some sourceStruct, some selectedX]
  let receiver ← mkExpectedTypeHint
    (← mkAppOptM ``CategoryTheory.Arrow.mk
      #[some selectedCarrier, some selectedCategory, some selectedX,
        some selectedX, some identity]) sourceArrow
  let base ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (ModuleCat.of ℤ (ℤ × ℤ))), (by
      change Mono (CategoryStruct.id (ModuleCat.of ℤ (ℤ × ℤ))); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let expected ← Semantic.liftSubobject state row receiver base
  let .ok prepared ← LiftedSubobjectData.plan (← inferType expected) sourceCategory
      receiver #[row.id] base
    | throwError "the existing formal lift has no complete public plan"
  let #[component] := prepared.components
    | throwError "the selected fixture changed its number of stages"
  let inner ← SelectedLift.innerEdge state row
  let trace ← Trace.new
  let pureAction ← Realize.edgeDescriptor trace inner component.action
  let operations := LiftField.all.map row.fieldAddress
  let manifest : Manifest := {
    backends := #[{
      name := "lift-probe"
      command := "python3"
      args := #["probe_lift_protocol.py"] ++ operations }]
    registrations := operations.map fun operation =>
      { operation, input := row.inputAddress, backend := "lift-probe" } }
  let observations ← IO.mkRef #[]
  let harness ← Realize.Harness.ofManifest ("CasAcceptance" / "Strata") manifest
  let harness := { harness with dispatches := some observations }
  unless harness.rejected.isEmpty && harness.admitted.size == operations.size do
    throwError "a public lift field was not admitted: {reprStr harness.rejected}"
  try
    let .ok session ← harness.connection "lift-probe"
      | throwError "the existing protocol-only helper did not start"
    let owner := some ("lift-probe", session.identity)
    let some parameterForm := state.objects.find? (·.id.raw == "obj.sets.integers")
      | throwError "the fixture parameter lost its existing set presentation"
    let fixedParameters ← DirectConstruction.dataArguments component.selection.parameters
    unless fixedParameters.size == 2 do
      throwError "the existing lift changed its complete selected parameter vector"
    let actualParameter := opaqueField "actual cached parameter, not its formal recipe"
    for parameter in fixedParameters do
      harness.results.modify (·.insert parameter {
        form := .object parameterForm
        payload := Realize.computedPayload parameter actualParameter owner })
    let parameters ← prepared.components.mapM fun part => do
      Realize.realizedParameters harness trace
        (← DirectConstruction.dataArguments part.selection.parameters)
    let (action, actionDependencies) ← Realize.realizedEdgeDescriptor harness trace
      inner component.action
    let .ok (_, actionParameters) := ComputationalData.envelope action
      | throwError "the actual action omitted its ordered parameters"
    unless action != pureAction && actionParameters == parameters[0]!.1 &&
        actionParameters == fixedParameters.map (fun _ => actualParameter) &&
        !actionDependencies.isEmpty && actionDependencies.all (·.owner? == owner) do
      throwError "the action replaced an actual cached parameter or its owner"
    let sourceObject := opaqueField "actual complete source object"
    let sourceData := envelope "arrow"
      #[sourceObject, sourceObject, opaqueField "actual source map"]
    let baseData := envelope "subobject" #[opaqueField "actual base apex",
      envelope "functorAction" #[action, sourceObject], opaqueField "actual base inclusion"]
    let sourceWire : Realize.Wire := {
      form := .arrow (← Semantic.namedCategoryFor state prepared.sourceCategory)
      payload := Realize.computedPayload receiver sourceData owner }
    let baseWire : Realize.Wire := {
      form := .subobject prepared.baseCategory
      payload := Realize.computedPayload base baseData owner }
    let (packet, returnedOwner) ← Realize.executePrescribedLift harness trace prepared
      sourceWire baseWire parameters (some (Realize.realizedEdgeDescriptor harness trace))
    unless returnedOwner == owner do throwError "the prescribed packet lost its actual owner"
    let .ok packetFields := LiftedSubobjectData.fields "liftedSubobject" 4 packet
      | throwError "the executor omitted its complete retained packet"
    let .ok #[step] := packetFields[3]!.getArr?
      | throwError "the completed packet lost its single selected stage"
    let .ok stepFields := LiftedSubobjectData.fields "liftStep" 5 step
      | throwError "the completed stage lost an input or output field"
    let .ok outputs := stepFields[4]!.getArr?
      | throwError "the completed stage omitted its actual outputs"
    let .ok retainedParameters := step.getObjVal? "parameters"
      | throwError "the completed stage omitted its actual evidence parameters"
    unless stepFields[1]! == action && stepFields[2]! == sourceData &&
        stepFields[3]! == baseData &&
        retainedParameters == Json.arr parameters[0]!.1 do
      throwError "the completed stage replaced actual action or evidence parameters"
    let decodePacket json := do
      LiftedSubobjectData.decode (← inferType expected) sourceCategory
        receiver #[row.id] base json
        (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
        (fun _ formal data objects => do
          ComputationalData.validatePort formal (← inferType formal) data objects)
        (some (parameters.map (·.1)))
    let some checked ← decodePacket packet
      | throwError "the actual completed packet was not recognized"
    let checked ← match checked with
      | .ok checked => pure checked
      | .error message =>
        throwError "the actual owned parameters failed completed-packet validation: {message}"
    unless checked.data == packet && checked.outputs == #[outputs] do
      throwError "completed-packet validation replaced actual parameters or outputs"
    -- An unrelated opaque source cannot supply the remembered forgetful image.
    -- Change both recorded base positions so this tests the retained interface,
    -- rather than merely the equality of the duplicated packet fields.
    let changedBase := envelope "subobject" #[opaqueField "actual base apex",
      envelope "functorAction" #[action, opaqueField "unrelated source object"],
      opaqueField "actual base inclusion"]
    let changedStep := Json.mkObj [("ctor", "liftStep"),
      ("parameters", retainedParameters),
      ("args", Json.arr (stepFields.set! 3 changedBase))]
    let changedPacket := envelope "liftedSubobject"
      ((packetFields.set! 0 changedBase).set! 3 (Json.arr #[changedStep]))
    let some invalid ← decodePacket changedPacket
      | throwError "a changed actual base interface was not recognized"
    if invalid.isOk then throwError "an unrelated source supplied a retained lift base image"
    let calls ← observations.get
    unless calls.size == 4 && outputs.size == 4 do
      throwError "the prescribed lift did not execute its four ordered fields"
    for (field, index) in LiftField.all.zipIdx do
      let call := calls[index]!
      let .ok request := call.getObjVal? "request" | unreachable!
      let .ok response := call.getObjVal? "response" | unreachable!
      let .ok invocation := Backend.LiftInput.decode request (row.fieldAddress field)
        | throwError "an observed request omitted its complete prescribed input"
      unless invocation.originalArrow && invocation.action == action &&
          invocation.parameters == parameters[0]!.1 && invocation.source == sourceData &&
          invocation.base == baseData && invocation.outputs == outputs.extract 0 index &&
          response == outputs[index]! do
        throwError "an actual request replaced a parameter, action or preceding output"
    -- Check the next-source serializer without inventing a repeated forget-lift route.
    let .ok mappedSource := LiftedSubobjectData.mapArrowData action sourceData
      | throwError "the complete source Arrow could not be mapped"
    unless mappedSource == envelope "arrow" #[
        envelope "functorAction" #[action, sourceObject],
        envelope "functorAction" #[action, sourceObject],
        envelope "map" #[action, opaqueField "actual source map"]] do
      throwError "the following source descriptor discarded the actual action parameters"
    let execution : Realize.LiftExecution := {
      selections := #[component.selection], actions := #[stepFields[1]!],
      parameters := #[parameters[0]!.1], sources := #[sourceObject],
      bases := #[stepFields[3]!], outputs := #[outputs] }
    Realize.cacheLiftFields harness execution returnedOwner
    let objectField ← SelectedLift.port execution.selections 0
    let retained ← Realize.realize harness trace "the retained prescribed object field" objectField
    let some retainedExecution := retained.liftExecution
      | throwError "the projected object discarded its completed lift execution"
    unless retained.owner? == owner && retainedExecution.actions == #[action] &&
        retainedExecution.parameters == execution.parameters &&
        retainedExecution.outputs == #[outputs] do
      throwError "object reuse replaced an actual action, parameter, output or owner"
    for index in #[2, 3] do
      let formal ← SelectedLift.port execution.selections index
      let projected ← Realize.realize harness trace "the retained comparison field" formal
      let .ok typed := Backend.TypedMap.decode projected.json
        | throwError "the retained comparison omitted its actual endpoint descriptors"
      let image := envelope "functorAction" #[action, outputs[0]!]
      unless projected.owner? == owner && projected.json ==
          (← Realize.liftProjectionData execution index) &&
          (if index == 2 then typed.source else typed.target) == image do
        throwError "comparison reuse discarded its actual action parameters or owner"
    unless (← observations.get).size == 4 do
      throwError "retained field reuse reran a prescribed computation"
    -- Parameter dependencies carry the same live owner as the completed packet.
    -- A matching token cannot stand in for a different backend or session.
    for (dependencyOwner, expectedStratum) in #[
        (owner, Stratum.noImplementation),
        (some ("lift-probe", session.identity + 1), Stratum.unavailable),
        (some ("foreign-lift-probe", session.identity), Stratum.unavailable)] do
      let empty ← Realize.Harness.empty
      let dispatches ← IO.mkRef #[]
      let empty := { empty with dispatches := some dispatches }
      let dependency : Realize.Wire := {
        form := .object parameterForm
        payload := Realize.computedPayload fixedParameters[0]! actualParameter dependencyOwner }
      let refused ← try
        discard <| Realize.executePrescribedLift empty trace prepared sourceWire baseWire
          #[(parameters[0]!.1, #[dependency])]
        pure false
      catch error =>
        if CasCatalogue.Exception.stratum? error == some expectedStratum then pure true
        else throw error
      unless refused && (← dispatches.get).isEmpty && (← empty.connections.get).isEmpty do
        throwError "the evidence-parameter owner preflight changed dispatch or failure meaning"
    -- Remove evidence-parameter dependencies to isolate the action-owner preflight.
    for (dependencyOwner, expectedStratum) in #[
        (owner, Stratum.noImplementation),
        (some ("lift-probe", session.identity + 1), Stratum.unavailable),
        (some ("foreign-lift-probe", session.identity), Stratum.unavailable)] do
      let empty ← Realize.Harness.empty
      let dispatches ← IO.mkRef #[]
      let empty := { empty with dispatches := some dispatches }
      let encodings ← IO.mkRef (0 : Nat)
      let dependency : Realize.Wire := {
        form := .object parameterForm
        payload := Realize.computedPayload fixedParameters[0]! actualParameter dependencyOwner }
      let encoder : Realize.ActionEncoder := fun _ _ => do
        encodings.modify (· + 1)
        return (action, #[dependency])
      let refused ← try
        discard <| Realize.executePrescribedLift empty trace prepared sourceWire baseWire
          #[(parameters[0]!.1, #[])] (some encoder)
        pure false
      catch error =>
        if CasCatalogue.Exception.stratum? error == some expectedStratum then pure true
        else throw error
      unless refused && (← encodings.get) == 1 && (← dispatches.get).isEmpty &&
          (← empty.connections.get).isEmpty do
        throwError "the action-owner preflight changed dispatch behavior or failure meaning"
  finally
    harness.stop
