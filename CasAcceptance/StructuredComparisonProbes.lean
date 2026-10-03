module

public meta import CasCatalogue.TestSuite
public meta import CasCatalogue.StructuredResult
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import Mathlib.Algebra.Algebra.Bilinear

/-! Engineering checks of retained universal cones and complete subobject comparisons.
These use existing categorical evidence; they supply no backend correctness oracle. -/

open Lean Meta Elab Term Command CategoryTheory CasCatalogue

namespace CasAcceptance.StructuredComparisonProbes

run_elab do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "missing accepted product"
  let X ← elabTermAndSynthesize (← `(Fin 2)) none
  let Y ← elabTermAndSynthesize (← `(Fin 1)) none
  let diagram ← mkAppM ``CategoryTheory.Limits.pair #[X, Y]
  let presentation ← Semantic.limitPresentation row diagram
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  let iso ← elabTermAndSynthesize (← `((Equiv.prodComm (Fin 1) (Fin 2)).toIso)) none
  let marker := Json.mkObj [("original", toJson "retained")]
  let comparison ← mkAppM ``CategoryTheory.Iso.refl #[apex]
  let result : StructuredResult.Result := {
    diagram, cone, apex, answer := marker, imageIso := some comparison,
    presentation := some presentation }
  let .ok extended ← StructuredResult.extendCreated result iso
    | throwError "the checked nonidentity apex extension failed"
  let expectedCone ← mkAppM ``CategoryTheory.Limits.Cone.extend
    #[cone, ← mkAppM ``CategoryTheory.Iso.hom #[iso]]
  unless ← isDefEq extended.cone expectedCone do
    throwError "the apex extension replaced the actual defining maps"
  let expectedApex ← elabTermAndSynthesize (← `(Fin 1 × Fin 2)) none
  unless ← isDefEq extended.apex expectedApex do
    throwError "the apex extension lost the full requested source"
  unless extended.answer == marker && extended.imageIso == some comparison do
    throwError "the apex extension replaced original reconstruction data"
  let some rebuilt := extended.presentation
    | throwError "the apex extension dropped universal evidence"
  let rebuiltCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[rebuilt]
  unless ← isDefEq rebuiltCone expectedCone do
    throwError "the retained universal evidence is over another cone"
  discard <| StructuredResult.checkReconstruction rebuilt
  if (← StructuredResult.extendCreated { result with presentation := none } iso).isOk then
    throwError "an apex extension without universal evidence was accepted"
  let wrong ← elabTermAndSynthesize (← `(CategoryTheory.Iso.refl (Fin 3))) none
  if (← StructuredResult.extendCreated result wrong).isOk then
    throwError "an apex comparison with wrong complete endpoints was accepted"
  let Z ← elabTermAndSynthesize (← `(Fin 3)) none
  let wrongDiagram ← mkAppM ``CategoryTheory.Limits.pair #[Z, Y]
  if (← StructuredResult.extendCreated { result with diagram := wrongDiagram } iso).isOk then
    throwError "universal evidence over a different complete diagram was accepted"

run_elab do
  let original ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (Fin 2 × Fin 1)), (by
      change Mono (CategoryStruct.id (Fin 2 × Fin 1)); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (Type 0) => Mono a.hom)))) none
  let returned ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (Equiv.prodComm (Fin 2) (Fin 1)).toIso.inv, (by
      change Mono (Equiv.prodComm (Fin 2) (Fin 1)).toIso.inv
      letI := CategoryTheory.Iso.isIso_inv (Equiv.prodComm (Fin 2) (Fin 1)).toIso
      infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (Type 0) => Mono a.hom)))) none
  let iso ← elabTermAndSynthesize (← `((Equiv.prodComm (Fin 2) (Fin 1)).toIso)) none
  let square ← mkAppM ``CategoryTheory.Iso.hom_inv_id #[iso]
  let .ok comparison ← StructuredResult.subobjectComparison original returned iso square
    | throwError "full nonidentity subobject comparison failed"
  let wanted ← mkAppM ``CategoryTheory.Iso #[original, returned]
  unless ← withTransparency .all <| isDefEq (← inferType comparison) wanted do
    throwError "subobject comparison lost the complete structured endpoints"
  discard <| StructuredResult.checkReconstruction comparison
  let wrong ← elabTermAndSynthesize (← `(CategoryTheory.Iso.refl (Fin 3))) none
  if (← StructuredResult.subobjectComparison original returned wrong square).isOk then
    throwError "wrong full apex endpoints accepted"
  let unrelated ← mkEqRefl (mkNatLit 0)
  if (← StructuredResult.subobjectComparison original returned iso unrelated).isOk then
    throwError "an unrelated inclusion-square proof accepted"
  let other ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (Fin 3)), (by
      change Mono (CategoryStruct.id (Fin 3)); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (Type 0) => Mono a.hom)))) none
  if (← StructuredResult.subobjectComparison original other iso square).isOk then
    throwError "a different fixed ambient object accepted"

/-! Actual accepted cartesian lift engineering checks. The full chosen form remains
part of each endpoint; these are reconstruction regressions, not mathematical acceptance. -/

run_elab do
  let X ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ (ℤ × ℤ) ℤ))) none
  let L ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.Kernels.forgetMonoLift ℤ ℤ)) none
  let ambientIso ← mkAppM ``CategoryTheory.Iso.refl #[X]
  let original ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (ModuleCat.of ℤ (ℤ × ℤ))), (by
      change Mono (CategoryStruct.id (ModuleCat.of ℤ (ℤ × ℤ))); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let e ← elabTermAndSynthesize (← `(
    (LinearEquiv.prodComm ℤ ℤ ℤ).toModuleIso)) none
  let returned ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk $(← exprToSyntax (← mkAppM ``CategoryTheory.Iso.inv #[e])), (by
      change Mono $(← exprToSyntax (← mkAppM ``CategoryTheory.Iso.inv #[e]))
      letI := CategoryTheory.Iso.isIso_inv $(← exprToSyntax e)
      infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let .ok baseIso ← StructuredResult.subobjectComparison original returned e
      (← mkAppM ``CategoryTheory.Iso.hom_inv_id #[e])
    | throwError "base comparison failed"
  let lift (ambient value : Expr) := do
    let a ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[value]
    let i ← mkAppM ``CategoryTheory.Arrow.hom #[a]
    let mono ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[value]
    elabTermAndSynthesize (← `(
      letI : Mono $(← exprToSyntax i) := $(← exprToSyntax mono)
      let h := @CasCatalogue.MonoLift.hom _ _ _ _ _ $(← exprToSyntax L) $(← exprToSyntax ambient) _
        $(← exprToSyntax i) $(← exprToSyntax mono)
      (⟨Arrow.mk h, @CasCatalogue.MonoLift.hom_mono _ _ _ _ _ $(← exprToSyntax L)
        $(← exprToSyntax ambient) _ $(← exprToSyntax i) $(← exprToSyntax mono)⟩ :
        ObjectProperty.FullSubcategory
          (fun a : Arrow (LeanCategories.Modules.Bilinear.Valued.BilinModuleCat ℤ ℤ) => Mono a.hom)))) none
  let originalLifted ← lift X original
  let returnedLifted ← lift X returned
  let result ← StructuredResult.liftSubobjectComparison L X X ambientIso
      original returned baseIso originalLifted returnedLifted
  let comparison ← match result with
    | .ok comparison => pure comparison
    | .error message => throwError "full selected formed-module lift comparison failed: {message}"
  let wanted ← mkAppM ``CategoryTheory.Iso #[originalLifted, returnedLifted]
  unless ← withTransparency .all <| isDefEq (← inferType comparison) wanted do
    throwError "full selected lifted endpoints were lost"
  discard <| StructuredResult.checkReconstruction comparison
  discard <| StructuredResult.checkReconstruction
    (← mkAppM ``CategoryTheory.Iso.hom_inv_id #[comparison])
  discard <| StructuredResult.checkReconstruction
    (← mkAppM ``CategoryTheory.Iso.inv_hom_id #[comparison])
  let wrongIso ← mkAppM ``CategoryTheory.Iso.refl #[original]
  if (← StructuredResult.liftSubobjectComparison L X X ambientIso original returned
      wrongIso originalLifted returnedLifted).isOk then
    throwError "wrong base comparison endpoints accepted"
  if (← StructuredResult.liftSubobjectComparison L X X ambientIso original returned
      baseIso returnedLifted originalLifted).isOk then
    throwError "wrong exact lifted defining maps accepted"
  let ambientSwap ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.isoMk
      (L := $(← exprToSyntax X)) (M := $(← exprToSyntax X))
      (LinearEquiv.prodComm ℤ ℤ ℤ) (fun _ _ => rfl))) none
  let U ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.forget ℤ ℤ)) none
  let mappedSwap ← mkAppM ``CategoryTheory.Functor.mapIso #[U, ambientSwap]
  let originalArrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[original]
  let baseArrowSwap ← elabTermAndSynthesize (← `(
    CategoryTheory.Arrow.isoMk
      (f := $(← exprToSyntax originalArrow)) (g := $(← exprToSyntax originalArrow))
      $(← exprToSyntax mappedSwap) $(← exprToSyntax mappedSwap) (by
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        simp only [Category.comp_id, Category.id_comp]))) none
  let fullBaseSwap ← elabTermAndSynthesize (← `(
    CategoryTheory.ObjectProperty.isoMk
      (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)
      (X := $(← exprToSyntax original)) (Y := $(← exprToSyntax original))
      $(← exprToSyntax baseArrowSwap))) none
  match ← StructuredResult.liftSubobjectComparison L X X ambientSwap original original
      fullBaseSwap originalLifted originalLifted with
  | .error message => throwError "nonidentity ambient comparison failed: {message}"
  | .ok comparison =>
      discard <| StructuredResult.checkReconstruction comparison
      discard <| StructuredResult.checkReconstruction
        (← mkAppM ``CategoryTheory.Iso.hom_inv_id #[comparison])
      discard <| StructuredResult.checkReconstruction
        (← mkAppM ``CategoryTheory.Iso.inv_hom_id #[comparison])
  if (← StructuredResult.liftSubobjectComparison L X X ambientIso original original
      fullBaseSwap originalLifted originalLifted).isOk then
    throwError "base ambient component inconsistent with exact source action accepted"
  let differentForm ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      ((LinearMap.mul ℤ ℤ).compl₁₂
        (LinearMap.fst ℤ ℤ ℤ) (LinearMap.fst ℤ ℤ ℤ)))) none
  unless ← withTransparency .all <| isDefEq
      (← mkAppM ``CategoryTheory.Functor.obj #[U, X])
      (← mkAppM ``CategoryTheory.Functor.obj #[U, differentForm]) do
    throwError "the chosen-form negative does not have the identical module carrier"
  if ← withoutModifyingState <| withTransparency .all <| isDefEq X differentForm then
    throwError "the chosen-form negative does not retain distinct pairing data"
  let wrongFormLifted ← lift differentForm original
  let identicalBase ← mkAppM ``CategoryTheory.Iso.refl #[original]
  if (← StructuredResult.liftSubobjectComparison L X X ambientIso original original
      identicalBase originalLifted wrongFormLifted).isOk then
    throwError "a different chosen pairing on the identical module carrier was accepted"
  if (← StructuredResult.liftSubobjectComparison L X differentForm ambientIso original original
      identicalBase originalLifted wrongFormLifted).isOk then
    throwError "the ambient comparison silently identified different chosen pairings"
  logInfo "PASS: selected formed-module lift comparisons and inverse equations; wrong full endpoints, defining maps, ambient action and same-carrier chosen pairing rejected"



end CasAcceptance.StructuredComparisonProbes
