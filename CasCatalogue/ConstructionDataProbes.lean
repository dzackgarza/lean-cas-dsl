/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
import LeanCategories.Catalogue.Semantics
import CasCatalogue.ConstructionData
meta import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.ConstructionData

open Lean Meta Elab Term Command

namespace CasCatalogue.ConstructionDataProbes

-- Engineering checks of descriptor parsing and endpoint checking, not engine acceptance.
run_cmd liftTermElabM do
  let X ← elabTermAndSynthesize (← `(ℕ)) none
  let Y ← elabTermAndSynthesize (← `(ℤ)) none
  let hom ← mkAppM ``Quiver.Hom #[X, X]
  let read := fun (type : Expr) (j : Json) => do
    let value := if j == toJson "nat" then X else Y
    unless ← isDefEq (← inferType value) type do return .error "wrong endpoint type"
    return .ok value
  let wire := fun (name : String) (args : Array Json) =>
    Json.mkObj [("ctor", toJson name), ("args", Json.arr args)]
  let value ← match ← ConstructionData.decode hom
      (wire "identity" #[toJson "nat", toJson "nat"]) read with
    | some (.ok value) => pure value
    | some (.error message) => throwError "identity on an infinite carrier failed: {message}"
    | none => throwError "identity descriptor was not recognized"
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[X]
  unless ← isDefEq value identity do throwError "identity descriptor changed its value"
  let some (.error _) ← ConstructionData.decode hom
      (wire "identity" #[toJson "nat", toJson "int"]) read
    | throwError "identity accepted the wrong endpoint"
  let Z ← elabTermAndSynthesize (← `(ModuleCat.of ℤ ℤ)) none
  let zeroType ← mkAppM ``Quiver.Hom #[Z, Z]
  let zeroRead := fun (type : Expr) (_ : Json) => do
    unless ← isDefEq (← inferType Z) type do return .error "wrong module endpoint type"
    return .ok Z
  let some (.ok zero) ← ConstructionData.decode zeroType
      (wire "zero" #[toJson "module", toJson "module"]) zeroRead
    | throwError "categorical zero on an infinite module failed"
  let expectedZero ← elabTermEnsuringType (← `(0)) zeroType
  unless ← isDefEq zero expectedZero do throwError "zero descriptor changed its value"
  let some (.error _) ← ConstructionData.decode hom
      (wire "zero" #[toJson "nat", toJson "nat"]) read
    | throwError "zero accepted a category without zero morphisms"
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "missing independently registered product presentation"
  let diagram ← mkAppM ``CategoryTheory.Limits.pair #[X, Y]
  let other ← mkAppM ``CategoryTheory.Limits.pair #[Y, X]
  let presentation ← Semantic.limitPresentation row diagram
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  let readDiagram := fun (type : Expr) (j : Json) => do
    let value := if j == toJson "diagram" then diagram else other
    unless ← isDefEq (← inferType value) type do return .error "wrong diagram type"
    return .ok value
  let index ← elabTermAndSynthesize
    (← `(CategoryTheory.Discrete.mk CategoryTheory.Limits.WalkingPair.left)) none
  let legRead := fun (type : Expr) (j : Json) => do
    if j == toJson "left" then
      unless ← isDefEq (← inferType index) type do return .error "wrong index type"
      return .ok index
    readDiagram type j
  let transformation ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
  let leg ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, index]
  let some (.ok decodedLeg) ← ConstructionData.decode (← inferType leg)
      (wire "limitLeg" #[toJson row.id.raw, toJson "diagram", toJson "left"]) legRead
    | throwError "canonical infinite product leg failed"
  unless ← isDefEq decodedLeg leg do throwError "canonical leg changed its defining data"
  let some (.error _) ← ConstructionData.decode (← inferType leg)
      (wire "limitLeg" #[toJson row.id.raw, toJson "other", toJson "left"]) legRead
    | throwError "canonical leg accepted a different diagram at the requested endpoints"
  let some (.ok value) ← ConstructionData.decode (← inferType apex)
      (wire "limitApex" #[toJson row.id.raw, toJson "diagram"]) readDiagram
    | throwError "canonical infinite product apex failed"
  unless ← isDefEq value apex do throwError "canonical apex descriptor changed its data"
  let some (.error _) ← ConstructionData.decode hom
      (wire "limitApex" #[toJson row.id.raw, toJson "diagram"]) readDiagram
    | throwError "canonical apex accepted a wrong result type"
  let some (.error _) ← ConstructionData.decode (← inferType apex)
      (wire "limitApex" #[toJson "unregistered", toJson "diagram"]) readDiagram
    | throwError "canonical apex accepted an unregistered presentation"

end CasCatalogue.ConstructionDataProbes
