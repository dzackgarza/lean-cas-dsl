/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics.Limits.Lifts
meta import CasCatalogue.Realize
meta import CasCatalogue.CategoryContext
meta import CasCatalogue.StructuredProjection
meta import LeanCategories.Catalogue.Semantics.Limits.Lifts

open Lean Meta Elab Term CasCatalogue

/-! Engineering controls for projecting and composing an already returned creation
packet. The arbitrary opaque fields provide no mathematical answer or lift law. -/

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

meta section

/-- The existing protocol process supplies actual opaque fields in a live session.
This engineering fixture registers and computes no mathematical operation. -/
private def withCreatedSession
    (action : Realize.Harness → Nat → TermElabM Unit) : TermElabM Unit := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let harness ← Realize.Harness.ofManifest root {
    backends := #[{
      name := "created-projection", command := "python3"
      args := #["probe_owned_callable.py", "created-projection-field"] }]
    registrations := #[] }
  try
    let session ← match ← harness.connection "created-projection" with
      | .ok session => pure session
      | .error error => throwError "the created-packet fixture's owner is unavailable: {error.render}"
    action harness session.identity
  finally harness.stop

run_elab withCreatedSession fun harness session => do
  let state ← registryState
  let trace ← Trace.new
  let some finite := state.objects.find? (·.id.raw == "obj.finite_sets.fin")
    | throwError "the accepted finite object is unavailable"
  let some category := state.categories.find? (·.id == finite.category)
    | throwError "the accepted finite category is unavailable"
  let some row := state.limits.find? (·.id.raw == "lim.sets.pullback")
    | throwError "the accepted lower construction is unavailable"
  let some lift := state.lifts.find? (·.id == LiftId.finiteSetsPullbacks)
    | throwError "the accepted creation interface is unavailable"
  let object ← Realize.objectAt trace finite #[mkNatLit 2]
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let diagram ← mkAppM ``CategoryTheory.Limits.cospan #[identity, identity]
  let presentation ← Semantic.limit false row.shape diagram category.id.raw (some trace)
  let action ← Semantic.asFunctor (← Semantic.edgeFunctor state lift.edge)
  let mapped ← Semantic.mapOf action identity
  let lowerDiagram ← mkAppM ``CategoryTheory.Limits.cospan #[mapped, mapped]
  let lowerPresentation ← Semantic.limitPresentation row lowerDiagram
  let .ok plan ← StructuredResult.dataPlan row lowerDiagram lowerPresentation
    | throwError "the accepted lower construction has no complete data plan"
  let .ok connection ← harness.connection "created-projection"
    | throwError "the created-packet fixture lost its live connection"
  let supplied ← plan.ports.mapM fun port => do
    let .ok reply ← Backend.call connection.connection "created-projection-field"
        (node "created-projection-field" #[toJson port.index])
      | throwError "the created-packet fixture did not receive its actual field"
    match Backend.ComputationalValue.decode reply with
    | .ok (.opaque _) => pure ()
    | _ => throwError "the created-packet field was not an actual opaque reply"
    let .scoped data ← Realize.receiveComputationalData harness "created-projection"
        "created-projection-field" reply
      | throwError "the created-packet field lost its scoped live supplier"
    Realize.checkDataOwners harness data
    return data
  let answerFragment ← Realize.scopedNode "cone" supplied
  let answer := answerFragment.json
  let objectData := node finite.id.raw #[toJson (2 : Nat)]
  let identityData := node "identity" #[objectData, objectData]
  let diagramData := node "cospan" #[identityData, identityData]
  let packet := StructuredResult.ComputationPacket.created lift.id.raw diagramData answer
  let .ok result ← StructuredResult.complete row diagram diagramData packet presentation
      (fun data => StructuredResult.validateData row lowerDiagram lowerPresentation data
        ComputationalData.validatePort)
    | throwError "the complete created fixture failed its original lower interface"
  Trace.record (some trace) result.apex (.limit row.id diagram (some lift.id))
  let packetFragment ← Realize.scopedNode "createdCone" #[
    { json := toJson lift.id.raw }, { json := diagramData }, answerFragment]
  unless packetFragment.json == packet.json do
    throwError "the created-packet fixture changed its original complete packet"
  let form := Form.createdApex row category.id
  let payload ← Realize.constructionPayload form result { json := diagramData } packetFragment
  let createdWire : Realize.Wire := { form, payload }
  harness.results.modify (·.insert result.apex createdWire)
  let index ← elabTermAndSynthesize (← `(CategoryTheory.Limits.WalkingCospan.left)) none
  let leg ← result.leg index
  Trace.record (some trace) leg (.limitProjection result.apex index)
  let actual ← Realize.realize harness trace "the created defining leg" leg
  let .ok indexData ← Codec.encode index
    | throwError "the fixed construction index has no encoding"
  let wantedLeg := node "constructionLeg" #[toJson row.id.raw, diagramData, packet.json, indexData]
  let wanted := Backend.TypedMap.encode {
    source := createdWire.json, target := objectData, callable := wantedLeg }
  unless actual.json == wanted && actual.owner? == some ("created-projection", session) &&
      actual.value == leg do
    throwError "the created leg lost its actual packet, exact index, original owner or full formal value"
  let again ← Realize.realize harness trace "the reused created defining leg" leg
  unless again.json == wanted && again.owner? == actual.owner? do
    throwError "reusing a created leg replaced its actual computational data"
  let context ← CategoryContext.ofNamed category result.apex
  let some projection ← StructuredProjection.construction? result.apex context (some trace)
    | throwError "the complete creation lost its source data-port interface"
  let sourcePlan ← projection.dataPlan
  for port in sourcePlan.ports do
    let formal ← StructuredProjection.retainPortValue result.apex port.formalField port.index
    Trace.record (some trace) formal (.structuredProjection result.apex "field" (some port.index))
    let field ← Realize.realize harness trace "the created data field" formal
    let expectedField := node "constructionField"
      #[toJson row.id.raw, diagramData, packet.json, toJson port.index]
    let expected ← if (Language.homEnds? port.expectedType).isSome then do
        let some apexBinder := sourcePlan.apexBinder
          | throwError "the original cone lost its apex binder"
        let some apexBinding := sourcePlan.binders[apexBinder]?
          | throwError "the original cone lost its apex binding"
        let some apexIndex := apexBinding.port
          | throwError "the original cone apex is not a returned field"
        let some apexPort := sourcePlan.ports[apexIndex]?
          | throwError "the original cone lost its apex field"
        unless port.domainBinder == some apexBinder do
          throwError "the original cone leg changed its exact apex binder"
        CategoryContext.checkMorphism context formal apexPort.formalField object
        pure <| Backend.TypedMap.encode {
          source := node "constructionField"
            #[toJson row.id.raw, diagramData, packet.json, toJson apexPort.index]
          target := objectData, callable := expectedField }
      else pure expectedField
    unless field.json == expected && field.owner? == actual.owner? do
      throwError "a created data field dropped its complete packet or original owner"
    let reused ← Realize.realize harness trace "the reused created data field" formal
    unless reused.json == expected && reused.owner? == field.owner? do
      throwError "reusing a created data field expanded its formal recipe again"
  let some (source, target) := Language.homEnds? (← inferType leg)
    | throwError "the created leg lost its full Hom interface"
  let targetIdentity ← mkAppM ``CategoryTheory.CategoryStruct.id #[target]
  let targetData := node finite.id.raw #[toJson (2 : Nat)]
  let targetIdentityData := node "identity" #[targetData, targetData]
  -- The identity is an ordinary intrinsic producer at this returned leg's
  -- exact target occurrence; its packet is not a substitute for its receipt.
  let targetEndpoint ← Realize.realizeCallableEndpoint harness trace actual target false (some context)
  let targetIdentityWire ← Realize.captureIntrinsicIdentity targetIdentity
    (.canonicalMorphism category) context targetEndpoint
  unless targetIdentityWire.json == targetIdentityData do
    throwError "the created leg's target identity changed its original public packet"
  harness.results.modify (·.insert targetIdentity targetIdentityWire)
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[leg, targetIdentity]
  Trace.record (some trace) composite
    (.morphismComposition category.id leg targetIdentity source target target)
  let composed ← Realize.realize harness trace "a subsequent composition of the created leg" composite
  let completeIdentity := Backend.TypedMap.encode {
    source := targetData, target := targetData, callable := targetIdentityData }
  unless composed.json == node "compose" #[wanted, completeIdentity] &&
      composed.owner? == actual.owner? do
    throwError "a subsequent composition stripped the complete created packet or its owning session"
  Realize.checkDataOwners harness composed.fragment
  let unavailable (active : Realize.Harness) : TermElabM Bool := do
    try
      Realize.checkDataOwners active composed.fragment
      return false
    catch error => return Exception.stratum? error == some .unavailable
  unless ← unavailable (← Realize.Harness.empty) do
    throwError "the composed created packet became available outside its actual supplier"
  harness.stop
  unless ← unavailable harness do
    throwError "the composed created packet survived expiry of its actual supplier"

end
