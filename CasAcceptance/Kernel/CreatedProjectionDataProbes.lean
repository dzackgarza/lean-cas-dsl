/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics.Limits.Lifts
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics.Limits.Lifts

open Lean Meta Elab Term CasCatalogue

/-! Engineering controls for projecting and composing an already returned creation
packet. The arbitrary opaque fields provide no mathematical answer or lift law. -/

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

run_elab do
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
  let answer := node "cone" (plan.ports.map fun port =>
    node "opaqueData" #[toJson s!"actual returned port {port.index}"])
  let objectData := node finite.id.raw #[toJson (2 : Nat)]
  let identityData := node "identity" #[objectData, objectData]
  let diagramData := node "cospan" #[identityData, identityData]
  let packet := StructuredResult.ComputationPacket.created lift.id.raw diagramData answer
  let .ok result ← StructuredResult.complete row diagram diagramData packet presentation
      (fun data => StructuredResult.validateData row lowerDiagram lowerPresentation data
        ComputationalData.validatePort)
    | throwError "the complete created fixture failed its original lower interface"
  Trace.record (some trace) result.apex (.limit row.id diagram (some lift.id))
  let harness ← Realize.Harness.empty
  harness.results.modify (·.insert result.apex {
    form := .createdApex row category.id
    payload := .construction result (.owned "created-projection" 73) })
  let index ← elabTermAndSynthesize (← `(CategoryTheory.Limits.WalkingCospan.left)) none
  let leg ← result.leg index
  Trace.record (some trace) leg (.limitProjection result.apex index)
  let actual ← Realize.realize harness trace "the created defining leg" leg
  let .ok indexData ← Codec.encode index
    | throwError "the fixed construction index has no encoding"
  let wanted := node "constructionLeg" #[toJson row.id.raw, diagramData, packet.json, indexData]
  unless actual.json == wanted && actual.owner? == some ("created-projection", 73) &&
      actual.value == leg do
    throwError "the created leg lost its actual packet, exact index, original owner or full formal value"
  let again ← Realize.realize harness trace "the reused created defining leg" leg
  unless again.json == wanted && again.owner? == actual.owner? do
    throwError "reusing a created leg replaced its actual computational data"
  let some (source, target) := Language.homEnds? (← inferType leg)
    | throwError "the created leg lost its full Hom interface"
  let targetIdentity ← mkAppM ``CategoryTheory.CategoryStruct.id #[target]
  let targetData := node finite.id.raw #[toJson (2 : Nat)]
  let targetIdentityData := node "identity" #[targetData, targetData]
  harness.results.modify (·.insert targetIdentity {
    form := .canonicalMorphism category
    payload := .ordinary targetIdentity targetIdentityData })
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[leg, targetIdentity]
  Trace.record (some trace) composite
    (.morphismComposition category.id leg targetIdentity source target target)
  let composed ← Realize.realize harness trace "a subsequent composition of the created leg" composite
  unless composed.json == node "compose" #[wanted, targetIdentityData] &&
      composed.owner? == actual.owner? do
    throwError "a subsequent composition stripped the complete created packet or its owning session"
