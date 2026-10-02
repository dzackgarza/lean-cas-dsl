/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
import LeanCategories.Catalogue.Semantics
import CasCatalogue.FunctorActionData
meta import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.FunctorActionData

open Lean Meta Elab Term Command
namespace CasCatalogue.FunctorActionDataProbes

-- Engineering checks of generic categorical data, never engine correctness assertions.
run_cmd liftTermElabM do
  let state ← registryState
  let some kernel := state.functors.find? (·.id.raw == "fun.arrows_modules.kernel")
    | throwError "missing accepted kernel functor"
  let R ← elabTermAndSynthesize (← `(RingCat.of ℤ)) none
  let F ← mkAppM kernel.declaration #[R]
  let Z ← elabTermAndSynthesize (← `(ModuleCat.of ℤ ℤ)) none
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[Z]
  let source ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let image ← mkAppM ``CategoryTheory.Functor.obj #[F, source]
  let wrongSource ← elabTermAndSynthesize (← `(ℕ)) none
  let wire := fun (name : String) (args : Array Json) =>
    Json.mkObj [("ctor", toJson name), ("args", Json.arr args)]
  let edge := wire kernel.id.raw #[toJson "integer-ring"]
  let action := wire "functorAction" #[edge, toJson "source-arrow"]
  let readFunctor := fun (json : Json) => do
    unless json == edge do return .error "unregistered exact descriptor"
    return .ok (F, kernel.source, kernel.target)
  let readSource := fun (category : CategoryExpr) (expected : Expr) (json : Json) => do
    unless category.syntacticEq kernel.source do return .error "wrong selected category"
    let value := if json == toJson "source-arrow" then source else wrongSource
    unless ← isDefEq (← inferType value) expected do return .error "wrong source type"
    return .ok value
  let result ← FunctorActionData.decode (← inferType image) action readFunctor readSource
  let some (.ok result) := result | throwError "registered functor action failed"
  unless ← isDefEq result image do throwError "functor action changed its source or edge"
  let some (.ok (inferred, category)) ←
      FunctorActionData.decodeInferred action readFunctor readSource
    | throwError "registered functor action inference failed"
  unless category.syntacticEq kernel.target && (← isDefEq inferred image) do
    throwError "inferred functor action changed the actual target metadata or data"
  let bad := wire "functorAction" #[edge, toJson "wrong-source"]
  let some (.error _) ← FunctorActionData.decode (← inferType image) bad readFunctor readSource
    | throwError "functor action accepted source data in a different category"
  let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[image]
  let apex ← mkAppM ``CategoryTheory.Arrow.left #[arrow]
  let inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
  for (tag, value) in #[("subobjectApex", apex), ("subobjectInclusion", inclusion)] do
    let some (.ok result) ← FunctorActionData.decode (← inferType value)
        (wire tag #[action]) readFunctor readSource
      | throwError "registered subobject projection failed: {tag}"
    unless ← isDefEq result value do throwError "subobject projection changed actual data"
    let some (.ok (inferred, category)) ← FunctorActionData.decodeInferred
        (wire tag #[action]) readFunctor readSource
      | throwError "subobject projection inference failed"
    let .construct _ #[.category base] := kernel.target
      | throwError "accepted kernel target is not the subobject constructor"
    unless category.syntacticEq base && (← isDefEq inferred value) do
      throwError "subobject projection inference changed actual base metadata or data"
  let some (.error _) ← FunctorActionData.decode (← inferType identity)
      (wire "subobjectInclusion" #[action]) readFunctor readSource
    | throwError "subobject inclusion accepted the wrong exact endpoints"
  let some (.error _) ← FunctorActionData.decode (← inferType apex)
      (wire "subobjectApex" #[edge]) readFunctor readSource
    | throwError "subobject projection accepted incomplete action data"

end CasCatalogue.FunctorActionDataProbes
