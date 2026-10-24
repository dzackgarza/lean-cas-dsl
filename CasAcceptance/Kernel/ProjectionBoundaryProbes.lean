/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.ComputationalData
meta import CasCatalogue.ComputationalData
meta import CasCatalogue.Language
meta import CasCatalogue.Semantic
meta import CasCatalogue.StructuredResult
meta import CasCatalogue.Codec

open Lean Meta Elab Term CasCatalogue

/-! Production-validator framing controls. Arbitrary opaque fields and a
deliberately different computational apex make no mathematical correctness claim. -/

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

private def fin (n : Nat) : Json := node "obj.sets.fin" #[toJson n]
private def token (label : String) : Json := node "opaqueData" #[toJson label]

run_elab do
  let source ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 1)) none
  let target ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let expected ← mkAppM ``Quiver.Hom #[source, target]
  let receiver := node "arrow" #[fin 1, fin 2, token "actual stored callable"]
  let projected := node "arrowHom" #[receiver]
  if let .error message ← ComputationalData.validateCallableAt #[] expected projected then
    throwError "the full stored Arrow map was rejected: {message}"
  let point := node "element" #[fin 2, node "point" #[projected]]
  if let .error message ← ComputationalData.validateElementAt target (fin 2)
      (← mkFreshExprMVar expected) point then
    throwError "the production element path lost a complete stored callable: {message}"
  for malformed in #[
      node "arrowHom" #[toJson (0 : Nat)],
      node "arrowHom" #[fin 2],
      node "arrowHom" #[node "arrow" #[fin 1, fin 2]],
      node "arrowHom" #[node "arrow" #[fin 1, fin 3, token "wrong codomain"]],
      node "arrowHom" #[node "arrow" #[fin 2, fin 2, token "wrong domain"]],
      node "subobjectInclusion" #[receiver]] do
    let .error _ ← ComputationalData.validateCallableAt #[] expected malformed
      | throwError "a stored-map projection accepted an incomplete receiver or changed its full endpoint interface"
    let .error _ ← ComputationalData.validateElementAt target (fin 2)
        (← mkFreshExprMVar expected) (node "element" #[fin 2, node "point" #[malformed]])
      | throwError "an element point hid an untyped stored-map projection"

run_elab do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "the accepted product interface is unavailable"
  let X ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let Y ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 3)) none
  let diagram ← mkAppM ``CategoryTheory.Limits.pair #[X, Y]
  let presentation ← Semantic.limitPresentation row diagram
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let maps ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
  let index ← elabTermAndSynthesize
    (← `(CategoryTheory.Discrete.mk CategoryTheory.Limits.WalkingPair.left)) none
  let leg ← mkAppM ``CategoryTheory.NatTrans.app #[maps, index]
  let expected ← inferType leg
  let .ok indexData ← Codec.encode index | throwError "the exact diagram index is not encodable"
  let diagramData := node "pair" #[fin 2, fin 3]
  let left := node "typedMap" #[fin 5, fin 2, token "actual first map"]
  let right := node "typedMap" #[fin 5, fin 3, token "actual second map"]
  let packet := node "cone" #[fin 5, left, right]
  let project := fun packet index =>
    node "constructionLeg" #[toJson row.id.raw, diagramData, packet, index]
  for valid in #[project packet indexData,
      node "limitLeg" #[toJson row.id.raw, diagramData, indexData]] do
    if let .error message ← ComputationalData.validateCallableAt #[] expected valid then
      throwError "a full declared construction leg was rejected: {message}"
  let .ok plan ← StructuredResult.dataPlan row diagram presentation
    | throwError "the accepted product has no complete port plan"
  let some port := plan.ports.find? (fun port => (Language.homEnds? port.expectedType).isSome)
    | throwError "the complete product plan omitted every defining map"
  let field := fun packet index =>
    node "constructionField" #[toJson row.id.raw, diagramData, packet, toJson (index : Nat)]
  if let .error message ← ComputationalData.validateCallableAt #[] port.expectedType
      (field packet port.index) then
    throwError "a full declared computational field was rejected: {message}"
  for malformed in #[
      project (toJson (0 : Nat)) indexData,
      project (node "cone" #[fin 5, left]) indexData,
      project (node "cocone" #[fin 5, left, right]) indexData,
      project (node "cone" #[fin 5,
        node "typedMap" #[fin 4, fin 2, token "changed actual source"], right]) indexData,
      project (node "cone" #[fin 5,
        node "typedMap" #[fin 5, fin 4, token "changed fixed target"], right]) indexData,
      project packet (toJson (0 : Nat)),
      field packet 0,
      field packet plan.ports.size] do
    let .error _ ← ComputationalData.validateCallableAt #[] expected malformed
      | throwError "a construction projection accepted incomplete fields, a changed endpoint or a wrong typed index"

run_elab do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.pullback")
    | throwError "the accepted base construction is unavailable"
  let some finite := state.objects.find? (·.id.raw == "obj.finite_sets.fin")
    | throwError "the accepted creation source object is unavailable"
  let object ← Semantic.object finite #[Syntax.mkNumLit "2"]
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let diagram ← mkAppM ``CategoryTheory.Limits.cospan #[identity, identity]
  let presentation ← Semantic.limit false row.shape diagram finite.category.raw
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let maps ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
  let index ← elabTermAndSynthesize (← `(CategoryTheory.Limits.WalkingCospan.left)) none
  let leg ← mkAppM ``CategoryTheory.NatTrans.app #[maps, index]
  let .ok indexData ← Codec.encode index | throwError "the exact created index has no encoding"
  let objectData := node finite.id.raw #[toJson (2 : Nat)]
  let identityData := node "identity" #[objectData, objectData]
  let diagramData := node "cospan" #[identityData, identityData]
  let lower := node "cone" #[fin 5,
    node "typedMap" #[fin 5, fin 2, token "actual first lower map"],
    node "typedMap" #[fin 5, fin 2, token "actual second lower map"]]
  let packet := node "createdCone" #[toJson LiftId.finiteSetsPullbacks.raw, diagramData, lower]
  let project := fun data => node "constructionLeg" #[toJson row.id.raw, diagramData, data, indexData]
  if let .error message ← ComputationalData.validateCallableAt #[] (← inferType leg) (project packet) then
    throwError "the complete created leg lost its independently selected interface: {message}"
  for bad in #[lower,
      node "createdCone" #[toJson LiftId.finiteSetsPullbacks.raw,
        node "pair" #[objectData, objectData], lower],
      node "createdCone" #[toJson LiftId.finiteSetsPullbacks.raw, diagramData,
        node "cone" #[fin 5]]] do
    let .error _ ← ComputationalData.validateCallableAt #[] (← inferType leg) (project bad)
      | throwError "a created projection discarded its lift, source diagram or complete target fields"
