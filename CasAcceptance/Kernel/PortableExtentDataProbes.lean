/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.ComputationalData
meta import CasCatalogue.ComputationalData
meta import CasCatalogue.Language
meta import CasCatalogue.CategoryContext
meta import CasCatalogue.Semantic

open Lean Meta Elab Term CasCatalogue

/-! Data-boundary controls only. The deliberately different formal objects and
returned subsets are not mathematical answers or correctness evidence. -/

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

private def fin (n : Nat) : Json := node "obj.sets.fin" #[toJson n]
private def token (label : String) : Json := node "opaqueData" #[toJson label]
private def extent (ambient subset : Json) : Json :=
  node "extent" #[toJson "pow.sets", ambient, subset]
private def finite (descriptor : Json) (points : Array Json) : Json :=
  node "finiteData" #[descriptor, Json.arr points]

run_elab do
  let original ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 41)) none
  let expected ← inferType original
  let points := #[toJson (0 : Nat), toJson (2 : Nat)]
  let actual := extent (fin 3) (Json.arr points)
  let packet := finite actual points
  for valid in #[actual, packet, node "valueData" #[packet]] do
    if let .error message ← ComputationalData.validatePort original expected valid then
      throwError "a published portable extent was rejected: {message}"
  if let .error message ← ComputationalData.interfaceArgument #[] expected actual then
    throwError "the portable object has no typed public argument interface: {message}"
  let .ok (some keys) ← ComputationalData.endpointKeys actual
    | throwError "the actual finite-subset representation lost its point keys"
  unless keys == points do throwError "actual keys were replaced by formal members"
  let expectedMap ← mkAppM ``Quiver.Hom #[original, original]
  let formalMap ← mkFreshExprMVar expectedMap
  let graph := Json.arr #[Json.arr #[points[0]!, points[1]!],
    Json.arr #[points[1]!, points[0]!]]
  if let .error message ← ComputationalData.validateEndpointPort formalMap packet packet
      (node "typedMap" #[packet, packet, graph]) then
    throwError "the whole map lost its actual extent endpoints: {message}"
  for malformed in #[
      node "extent" #[toJson "pow.unknown", fin 3, Json.arr points],
      extent (toJson (3 : Nat)) (Json.arr points),
      extent (fin 2) (Json.arr points),
      extent (fin 3) (Json.arr #[points[0]!, points[0]!]),
      finite actual #[points[0]!], finite actual #[points[0]!, points[0]!],
      finite actual #[points[0]!, toJson (1 : Nat)]] do
    let .error _ ← ComputationalData.validatePort original expected malformed
      | throwError "the portable extent accepted malformed framing or a different actual inventory"
  let .error _ ← ComputationalData.validateEndpointPort formalMap packet packet
      (node "typedMap" #[packet, packet,
        Json.arr #[Json.arr #[points[0]!, toJson (1 : Nat)],
          Json.arr #[points[1]!, points[0]!]]])
    | throwError "the whole map accepted a value outside its actual extent target"
  -- A well-framed different subset must remain data, not be rejected merely
  -- because it differs from the independently fixed formal object.
  if let .error message ← ComputationalData.validatePort original expected
      (finite (extent (fin 3) (Json.arr #[toJson (1 : Nat)])) #[toJson (1 : Nat)]) then
    throwError "computational framing attempted to decide the mathematical answer: {message}"

run_elab do
  let original ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 41)) none
  let expected ← inferType original
  let opaqueSubset := extent (fin 3) (token "actual subset supplier")
  if let .error message ← ComputationalData.validatePort original expected
      (finite opaqueSubset #[toJson (2 : Nat)]) then
    throwError "an extent with an owned subset lost its ambient point interface: {message}"
  let .error _ ← ComputationalData.validatePort original expected
      (finite opaqueSubset #[toJson (3 : Nat)])
    | throwError "an extent inventory was checked against the original formal carrier"

run_elab do
  let original ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 41)) none
  let residue := node "obj.sets.integers_mod" #[toJson (5 : Nat)]
  let ambient := node "obj.sets.vectors" #[residue, toJson (2 : Nat)]
  let point := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (1 : Nat)],
    Json.arr #[toJson (1 : Nat), toJson (0 : Nat)]]
  let packet := finite (extent ambient (Json.arr #[point])) #[point]
  if let .error message ← ComputationalData.validatePort original (← inferType original) packet then
    throwError "a function-valued ambient point lost its released graph codec: {message}"
  let badPoint := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (5 : Nat)],
    Json.arr #[toJson (1 : Nat), toJson (0 : Nat)]]
  let .error _ ← ComputationalData.validatePort original (← inferType original)
      (finite (extent ambient (Json.arr #[badPoint])) #[badPoint])
    | throwError "the actual ambient point interface accepted an out-of-range coordinate"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted set category is unavailable"
  let original ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 41)) none
  let context ← CategoryContext.ofNamed sets original
  let action ← mkAppOptM ``CategoryTheory.Functor.id
    #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context)]
  let points := #[toJson (0 : Nat), toJson (2 : Nat)]
  let packet := finite (extent (fin 3) (Json.arr points)) points
  if ComputationalData.hasSelectedObjectDescriptor state packet then
    throwError "a portable anonymous extent selected a mathematical object"
  unless ComputationalData.hasSelectedObjectDescriptor state (finite (fin 3) points) do
    throwError "a transparent wrapper discarded an actual named selection"
  if let .error message ← ComputationalData.interfaceActionSource #[(packet, original)]
      original packet action context.bundle (some context.expression) then
    throwError "an exact retained anonymous action input was rejected: {message}"
  let .error _ ← ComputationalData.interfaceActionSource #[] original packet action
      context.bundle (some context.expression)
    | throwError "an anonymous returned extent supplied its own formal receiver"
  let other ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 7)) none
  let .error _ ← ComputationalData.interfaceActionSource #[(packet, other)] original packet action
      context.bundle (some context.expression)
    | throwError "an anonymous packet replaced the independent retained formal receiver"
