/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.ComputationalData
meta import CasCatalogue.ComputationalData
meta import CasCatalogue.Language
meta import CasContract.Port

open Lean Meta Elab Term CasCatalogue

/-! Production response-validator controls. These check the declared type and
ordered data interface; they intentionally do not establish backend membership. -/

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

run_elab do
  let fin := fun n => node "obj.sets.fin" #[toJson (n : Nat)]
  let natural := node "obj.sets.naturals" #[]
  let positive := node "obj.sets.positive_naturals" #[]
  let target ← elabTermAndSynthesize (← `(CasCatalogue.Algebra.Semirings.positiveNaturals)) none
  let expected ← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, target]
  let original := node "opaqueData" #[toJson "actual unchecked natural"]
  let admitted : Backend.AdmittedPoint := {
    object := "obj.sets.positive_naturals", parameters := #[],
    domain := fin 1, source := natural, target := positive, argument := original }
  if let .error message ← ComputationalData.validateCallableAt #[] expected admitted.encode then
    throwError "the complete scalar admission was rejected: {message}"
  -- Zero has the declared scalar type. Its failure of positivity belongs to
  -- mathematical acceptance, not to this framing validator.
  if let .error message ← ComputationalData.validateCallableAt #[] expected
      { admitted with argument := toJson (0 : Nat) }.encode then
    throwError "the admission validator tried to establish backend membership: {message}"
  for bad in #[
      { admitted with object := "obj.sets.primes" },
      { admitted with parameters := #[toJson (2 : Nat)] },
      { admitted with source := fin 2 },
      { admitted with target := natural },
      { admitted with domain := fin 2 }] do
    let .error _ ← ComputationalData.validateCallableAt #[] expected bad.encode
      | throwError "an admission changed its registered input, result, owner or ordered parameters"
  let malformed := node "element" #[positive,
    node "point" #[{ admitted with object := "obj.sets.primes" }.encode]]
  let .error _ ← ComputationalData.validateElementAt target positive
      (← mkFreshExprMVar expected) malformed
    | throwError "the production element path accepted an unrelated published admission"

run_elab do
  let fin := fun n => node "obj.sets.fin" #[toJson (n : Nat)]
  let targetData := node "obj.sets.maps" #[fin 2, fin 3]
  let target ← elabTermAndSynthesize
    (← `(CasCatalogue.Foundation.Maps.maps (Fin 2) (Fin 3))) none
  let expected ← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, target]
  let admitted : Backend.AdmittedPoint := {
    object := "obj.sets.maps", parameters := #[fin 2, fin 3],
    domain := fin 2, source := fin 3, target := targetData,
    argument := node "opaqueData" #[toJson "actual whole callable"] }
  if let .error message ← ComputationalData.validateCallableAt #[] expected admitted.encode then
    throwError "the whole callable admission lost its original nonsingleton domain: {message}"
  let element := node "element" #[targetData, node "point" #[admitted.encode]]
  if let .error message ← ComputationalData.validateElementAt target targetData
      (← mkFreshExprMVar expected) element then
    throwError "the production element path rejected a complete whole-map admission: {message}"
  for bad in #[
      { admitted with parameters := #[fin 3, fin 3] },
      { admitted with parameters := #[fin 2] },
      { admitted with parameters := #[fin 2, fin 3, fin 1] },
      { admitted with domain := fin 4 },
      { admitted with source := fin 4 },
      { admitted with target := node "obj.sets.maps" #[fin 2, fin 4] }] do
    let .error _ ← ComputationalData.validateCallableAt #[] expected bad.encode
      | throwError "a whole-map admission changed an ordered parameter or original complete endpoint"
  let vectors ← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.LinearAlgebra.vectors (Fin 3) 2)) none
  unless ← withTransparency .all <| isDefEq vectors target do
    throwError "the same-carrier admission control lost its shared underlying type"
  let vectorType ← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, vectors]
  let vectorData := node "obj.sets.vectors" #[fin 3, toJson (2 : Nat)]
  for packet in #[admitted.encode, { admitted with target := vectorData }.encode] do
    let .error _ ← ComputationalData.validateCallableAt #[] vectorType packet
      | throwError "a different named object borrowed the map object's admission by carrier equality"
