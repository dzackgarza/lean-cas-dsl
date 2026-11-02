/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for positioned computational interfaces. Existing
Mathlib product exchange fixes the two different formal objects and their
comparison. Portable graph data are only framing fixtures: these checks assert
neither a mathematical answer nor correctness of that graph as the exchange.
No semantic registration, leaf, external process, or session is created. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

meta section

private def envelopeData (tag : String) (args : Array Json) : DataOwnership.Data :=
  { json := Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)] }

private def requireValid (label : String) (formal : Expr)
    (source target data : DataOwnership.Data) (scope : ComputationalData.InterfaceScope)
    (objects : ComputationalData.InterfaceObjects := #[]) : TermElabM Unit := do
  if let .error message ← ComputationalData.validateEndpointPort
      formal source.json target.json data.json objects (some scope) then
    throwError "{label}: {message}"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted set category is absent"
  let X ← elabTermAndSynthesize (← `(Fin 2)) none
  let Y ← elabTermAndSynthesize (← `(Fin 3)) none
  let source ← mkAppM ``Prod #[X, Y]
  let target ← mkAppM ``Prod #[Y, X]
  let context ← CategoryContext.ofNamed sets source
  if ← withoutModifyingState (withTransparency .all <| isDefEq source target) then
    throwError "the scope control requires different complete formal endpoint objects"
  -- Equal portable representations do not identify these formal objects.
  let shared := envelopeData "obj.sets.fin" #[toJson (6 : Nat)]
  let sourceWire : Wire := {
    form := .diagrams sets, payload := .computed source (.inline shared.json),
    categoryContext := some context }
  let targetWire : Wire := {
    form := .diagrams sets, payload := .computed target (.inline shared.json),
    categoryContext := some context }
  let comparison ← mkAppM ``Equiv.toIso #[← mkAppM ``Equiv.prodComm #[X, Y]]
  let forwardValue ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
  let backwardValue ← mkAppM ``CategoryTheory.Iso.inv #[comparison]
  let keys := (Array.range 6).map toJson
  let graph := envelopeData "finiteGraph"
    #[Json.arr keys, Json.arr (keys.map fun key => Json.arr #[key, key])]
  let mapData ← scopedNode "typedMap" #[shared, shared, graph]
  let prepare := fun (formal : Expr) (domain codomain : Wire) => do
    let wire : Wire := {
      form := .canonicalMorphism sets, payload := .computed formal (.inline mapData.json),
      categoryContext := some context, morphismFramed := true }
    retainCallableEndpoints wire domain codomain context
  let forward ← prepare forwardValue sourceWire targetWire
  let backward ← prepare backwardValue targetWire sourceWire
  let endpoint := { sourceWire with endpointPresentation := some {
    comparison, forward := mapData.json, backward := mapData.json,
    maps := some (forward, backward) } }
  let forwardScope ← callableValidationScope forward context forwardValue
  requireValid "separate equal-packet comparison endpoint positions"
    forwardValue shared shared mapData forwardScope
  -- An unrelated global equal packet cannot choose a positioned endpoint.
  requireValid "positioned endpoint wins over an unrelated global packet"
    forwardValue shared shared mapData forwardScope #[(shared.json, target)]
  let composed ← composeEndpointMaps context forward backward
  let composedScope ← callableValidationScope composed context composed.value
  requireValid "nested comparison composition retains each intermediate role"
    composed.value shared shared composed.fragment composedScope
  -- Deliberately put the other endpoint into the declared source position.
  -- Equal bytes are insufficient; its independently fixed formal role is wrong.
  let wrongTemplate : ActionDataTemplate := .ctor "typedMap"
    #[.wire .object targetWire, .wire .object targetWire, .literal graph]
  let wrongScope ← callableTemplateValidationScope context forwardValue mapData wrongTemplate
  let .error _ ← ComputationalData.validateCallableAt #[]
      (← CategoryContext.hom context source target) mapData.json (some wrongScope)
    | throwError "an equal packet substituted the wrong declared endpoint role"
  let rejectedGlobal ← try
      discard <| operationPresentationObjects #[sourceWire, targetWire]
      pure false
    catch error => pure (Exception.stratum? error == some .ambiguousRealization)
  unless rejectedGlobal do
    throwError "the old incompatible global-association collision guard was weakened"
  -- Both original component orders must work. Neither comparison graph is
  -- executed; all views are derived inertly from retained typed occurrences.
  let inputs := #[sourceWire, targetWire, forward, backward]
  let views := #[(endpoint, target), (targetWire, target)]
  for ordered in #[#[targetWire, endpoint], #[endpoint, targetWire]] do
    for selected in ordered do
      discard <| operationComponentPresentation context selected inputs views
  let identity ← identityAtContext context source
  let identityData ← scopedNode "identity" #[shared, shared]
  let raw : Wire := {
    form := .canonicalMorphism sets, payload := (← scopedPayload identity identityData false),
    categoryContext := some context }
  let raw ← retainCallableEndpoints raw sourceWire sourceWire context
  let framed ← presentMorphism raw endpoint endpoint (some context)
  let logical ← wireValidationScope .map framed (some context) (mapView := .logical)
  let .ok retained ← ComputationalData.interfaceArgument #[]
      (← CategoryContext.hom context source source) framed.json (some logical)
    | throwError "a declared map parameter lost its logical type at an accepted actual frame"
  unless ← withoutModifyingState (withTransparency .all <| isDefEq retained identity) do
    throwError "the map parameter's accepted representation replaced its logical formal value"
  logInfo "PASS: positioned comparison views, nested maps, logical parameters and both sibling orders"

run_elab do
  let nat ← elabTermAndSynthesize (← `(Nat)) none
  let scalar : DataOwnership.Data := { json := toJson (6 : Nat) }
  let neutral : ComputationalData.InterfaceScope := { data := scalar }
  let .ok decoded ← ComputationalData.interfaceArgument #[(scalar.json, mkNatLit 7)]
      nat scalar.json (some neutral)
    | throwError "an unrelated equal portable input obstructed a declared scalar literal"
  unless ← withoutModifyingState (withTransparency .all <| isDefEq decoded (mkNatLit 6)) do
    throwError "an unrelated global packet changed the positioned literal's declared value"
  let opaquePacket := (envelopeData "opaqueData" #[toJson "one token spelling"]).json
  let first := DataOwnership.Data.capture opaquePacket ("first scoped fixture", 1)
  let second := DataOwnership.Data.capture opaquePacket ("second scoped fixture", 2)
  let parent := DataOwnership.Data.array #[second]
  let child : ComputationalData.InterfaceScope := { data := first }
  let .error _ := ComputationalData.InterfaceScope.assemble parent #[ (#[.index 0], child) ]
    | throwError "equal opaque bytes replaced the supplier at a declared field position"
  logInfo "PASS: independent portable literals and exact positioned suppliers"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted set category is absent"
  let source ← elabTermAndSynthesize (← `(Fin 2)) none
  let context ← CategoryContext.ofNamed sets source
  let data := envelopeData "obj.sets.fin" #[toJson (2 : Nat)]
  let fieldWire : Wire := {
    form := .diagrams sets, payload := .computed source (.inline data.json),
    categoryContext := some context }
  let receiver ← mkAppM ``CategoryTheory.Core.mk #[source]
  let plan ← withLocalDeclD `original (← inferType receiver) fun symbolic => do
    let field ← mkAppM ``CategoryTheory.Core.of #[symbolic]
    let some plan ← ComputationalData.recordProjectionPlan? symbolic field
      | throwError "the Core control lost its independently selected field path"
    pure plan
  let whole ← scopedNode "coreObject" #[data]
  let some candidate ← plan.projectData? receiver whole
    | throwError "the neutral schema reader omitted an existing complete Core field"
  unless candidate == data do throwError "the neutral schema reader changed the original field data"
  let opaquePacket := DataOwnership.Data.capture
    (envelopeData "opaqueData" #[toJson "whole opaque Core"]).json ("fixture", 3)
  unless (← plan.projectData? receiver opaquePacket).isNone do
    throwError "a known Core codec opened an opaque whole packet as its single field"
  let wrong := envelopeData "objectProduct" #[data.json, data.json]
  unless (← plan.projectData? receiver wrong).isNone do
    throwError "a known Core codec opened an unrelated whole envelope as its single field"
  let .input expectedPath := plan
    | throwError "the Core control requires the original accepted projection path"
  let reader : ComputationalData.RecordProjectionScopeReader := fun path => do
    unless path.size == expectedPath.size &&
        (path.zip expectedPath).all (fun (actual, expected) => actual.sameDeclaration expected) do
      throwError "the retained scope reader requested a different declared path"
    wireValidationScope .object fieldWire (some context) (mapView := .logical)
  let some (projected, some _) ← plan.applyScoped? receiver whole #[] none (some reader)
    | throwError "the strict retained projection lost its exact field scope"
  unless projected == data do throwError "the retained projection changed original field suppliers"
  logInfo "PASS: neutral schema extraction and strict retained field scopes remain distinct"

run_elab do
  -- ULift has one ordinary computational field and no dedicated public
  -- envelope. Parent and child therefore share bytes but have different types.
  let receiver ← elabTermAndSynthesize (← `((ULift.up (6 : Nat) : ULift.{0} Nat))) none
  let field ← mkAppM ``ULift.down #[receiver]
  let data : DataOwnership.Data := { json := toJson (6 : Nat) }
  let parentScope ← bindValidationScope { data } receiver .value
  let fieldScope ← bindValidationScope { data } field .value
  let plan ← withLocalDeclD `original (← inferType receiver) fun symbolic => do
    let selected ← mkAppM ``ULift.down #[symbolic]
    let some plan ← ComputationalData.recordProjectionPlan? symbolic selected
      | throwError "the transparent record lost its declared single-field path"
    pure plan
  let .input expectedPath := plan
    | throwError "the transparent control requires the original accepted projection path"
  let reader : ComputationalData.RecordProjectionScopeReader := fun path => do
    unless path.size == expectedPath.size &&
        (path.zip expectedPath).all (fun (actual, expected) => actual.sameDeclaration expected) do
      throwError "the transparent reader requested a different original field"
    pure fieldScope
  let some (_, some selected) ← plan.applyScoped? receiver data #[] (some parentScope) (some reader)
    | throwError "a transparent record's parent scope displaced its distinct child role"
  let .ok (some binding) ← ComputationalData.interfaceScopeType (some selected) data.json
      (← inferType field)
    | throwError "the transparent field lost its independently selected complete type"
  unless ← withoutModifyingState (withTransparency .all <| isDefEq binding.formal field) do
    throwError "the transparent projection changed its original field occurrence"
  let wrongReader : ComputationalData.RecordProjectionScopeReader := fun _ => pure parentScope
  unless (← plan.applyScoped? receiver data #[] (some parentScope) (some wrongReader)).isNone do
    throwError "a transparent projection reused its equal-byte parent as the field"
  logInfo "PASS: transparent record projection preserves its distinct declared field role"

end
