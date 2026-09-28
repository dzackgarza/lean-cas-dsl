/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.FibrationCatalogue
public import CasCatalogue.Registry.Extension
public import CasCatalogue.Leaves.Modules.CatalogueRegistration
public import CasCatalogue.Leaves.Modules.Bilinear.Valued.CatalogueRegistration
public import CasCatalogue.Leaves.Exceptional.CatalogueRegistration
public import LeanCategories.Lattices.Valued.BilRefinements
public meta import CasCatalogue.FibrationCatalogue
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Modules.Expressions
public meta import CasCatalogue.Leaves.Algebra.Catalogue.Rings

@[expose] public section

/-!
# Registered fibrations (CC-FIB)

Each row registers a projection functor and a Lean proof that it is a cartesian or cocartesian
fibration (`FibrationEntry`); registration checks that the proof is about exactly the realized
projection.

* `fib.modules` — `∫ᶜ Mod → Ring`, cartesian, reindexing = restriction of scalars
  (`CategoryFamilyRealization.projection_isFibered`).
* `fib.modules_ext` — `∫ Mod → CommRing`, cocartesian, transport = extension of scalars
  (`Pseudofunctor.Grothendieck.isCofibered_forget`).
* `fib.bilin_forms` — `p : Bil → ∫ Mod`, cocartesian (FOUNDATIONS Proposition 31.2b,
  `BilinFormsOverRings.isCofibered_values`).
-/

namespace CasCatalogue.Catalogue.FibrationRegistration
open LeanCategories

open CategoryTheory LeanCategories CasCatalogue
open CasCatalogue.Modules.CatalogueRegistration
open LeanCategories.Lattices.Valued

noncomputable section

universe u w

/-! ### `fib.modules` -/

noncomputable def modulesProjectionDeclaration :
    modulesTotalCategory.{u, w} ⥤ Algebra.Rings.{u} :=
  modulesFamilyRealization.{u, w}.projection

noncomputable def modulesProjectionRealization :
    FunctorRealization Fibrations.ModulesProjectionExpr modulesTotalCategory.{u, w}
      Algebra.Rings.{u} modulesProjectionDeclaration :=
  { sourceRealization := modulesTotalRealization
    targetRealization := Algebra.CatalogueRegistration.ringsRealization }

theorem modulesProjection_isFibered : modulesProjectionDeclaration.{u, w}.IsFibered :=
  modulesFamilyRealization.{u, w}.projection_isFibered

/-! ### `fib.modules_ext` -/

noncomputable def modulesOverRingsExtCategory : ObjCat.{u + 1, u} :=
  Cat.of ModulesOverRingsExt.{u}

noncomputable def modulesOverRingsExtRealization :
    CategoryRealization Fibrations.ModulesOverRingsExt modulesOverRingsExtCategory.{u} := {}

noncomputable def modulesExtRingDeclaration :
    modulesOverRingsExtCategory.{u} ⥤ Algebra.CommutativeRings.{u} :=
  ModulesOverRingsExt.ring

noncomputable def modulesExtRingRealization :
    FunctorRealization Fibrations.ModulesExtRingExpr modulesOverRingsExtCategory.{u}
      Algebra.CommutativeRings.{u} modulesExtRingDeclaration :=
  { sourceRealization := modulesOverRingsExtRealization
    targetRealization := Algebra.CatalogueRegistration.commutativeRingsRealization }

theorem modulesExtRing_isCofibered : modulesExtRingDeclaration.{u}.IsCofibered :=
  Pseudofunctor.Grothendieck.isCofibered_forget _

/-! ### `fib.bilin_forms` -/

noncomputable def bilinFormsOverRingsCategory : ObjCat.{u + 1, u} :=
  Cat.of BilinFormsOverRings.{u}

noncomputable def bilinFormsOverRingsRealization :
    CategoryRealization Fibrations.BilinFormsOverRings bilinFormsOverRingsCategory.{u} := {}

noncomputable def bilinFormsValuesDeclaration :
    bilinFormsOverRingsCategory.{u} ⥤ modulesOverRingsExtCategory.{u} :=
  BilinFormsOverRings.values

noncomputable def bilinFormsValuesRealization :
    FunctorRealization Fibrations.BilinFormsValuesExpr bilinFormsOverRingsCategory.{u}
      modulesOverRingsExtCategory.{u} bilinFormsValuesDeclaration :=
  { sourceRealization := bilinFormsOverRingsRealization
    targetRealization := modulesOverRingsExtRealization }

theorem bilinFormsValues_isCofibered : bilinFormsValuesDeclaration.{u}.IsCofibered :=
  BilinFormsOverRings.isCofibered_values

/-! ### Lattices as a refinement of `Bil` -/

noncomputable def latticeClassifierDeclaration : Classifier bilinFormsOverRingsCategory.{u} :=
  latticeClassifier.{u}.toClassifier

noncomputable def latticeClassifierRealization :
    ClassifierRealization Fibrations.BilinFormsOverRings ClassifierId.bilLattice
      bilinFormsOverRingsCategory.{u} latticeClassifierDeclaration :=
  { hostRealization := bilinFormsOverRingsRealization, totalRealization := {} }

noncomputable def latticesOverRingsCategory : ObjCat.{u + 1, u} :=
  (Classifier.reindex (𝟙 bilinFormsOverRingsCategory.{u})
    latticeClassifierDeclaration).total

noncomputable def latticesOverRingsRealization :
    CategoryRealization Fibrations.LatticesOverRings latticesOverRingsCategory.{u} := {}

noncomputable def latticesOverRingsRefinement :
    RefinementRealization Fibrations.LatticesOverRings latticesOverRingsCategory.{u} where
  base := Fibrations.BilinFormsOverRings
  classifierId := ClassifierId.bilLattice
  expression_eq := rfl
  baseCategory := bilinFormsOverRingsCategory
  host := Fibrations.BilinFormsOverRings
  hostCategory := bilinFormsOverRingsCategory
  baseRealization := bilinFormsOverRingsRealization
  classifier := latticeClassifierDeclaration
  classifierRealization := latticeClassifierRealization
  baseToHost := 𝟙 _
  reindexed := Classifier.reindex (𝟙 _) latticeClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl

/-! ### Integral forms: the pullback of `Bil` along the regular section -/

noncomputable def regularSectionDeclaration :
    Algebra.CommutativeRings.{u} ⥤ modulesOverRingsExtCategory.{u} :=
  regularSection.{u}

noncomputable def regularSectionRealization :
    FunctorRealization Fibrations.RegularSectionExpr Algebra.CommutativeRings.{u}
      modulesOverRingsExtCategory.{u} regularSectionDeclaration :=
  { sourceRealization := Algebra.CatalogueRegistration.commutativeRingsRealization
    targetRealization := modulesOverRingsExtRealization }

noncomputable def valuesClassifierDeclaration : Classifier modulesOverRingsExtCategory.{u} :=
  { total := bilinFormsOverRingsCategory.{u}
    forget := bilinFormsValuesDeclaration.toCatHom }

noncomputable def valuesClassifierRealization :
    ClassifierRealization Fibrations.ModulesOverRingsExt ClassifierId.bilValues
      modulesOverRingsExtCategory.{u} valuesClassifierDeclaration :=
  { hostRealization := modulesOverRingsExtRealization, totalRealization := {} }

noncomputable def integralFormsCategory : ObjCat.{u + 1, u} :=
  (Classifier.reindex regularSectionDeclaration.{u}.toCatHom valuesClassifierDeclaration).total

noncomputable def integralFormsRealization :
    CategoryRealization Fibrations.IntegralForms integralFormsCategory.{u} := {}

noncomputable def integralFormsRefinement :
    RefinementRealization Fibrations.IntegralForms integralFormsCategory.{u} where
  base := Algebra.Catalogue.Rings.CommutativeRings
  classifierId := ClassifierId.bilValues
  expression_eq := rfl
  baseCategory := Algebra.CommutativeRings
  host := Fibrations.ModulesOverRingsExt
  hostCategory := modulesOverRingsExtCategory
  baseRealization := Algebra.CatalogueRegistration.commutativeRingsRealization
  classifier := valuesClassifierDeclaration
  classifierRealization := valuesClassifierRealization
  baseToHost := regularSectionDeclaration.toCatHom
  reindexed := Classifier.reindex regularSectionDeclaration.toCatHom valuesClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl

noncomputable def integralFormsToBilDeclaration :
    integralFormsCategory.{u} ⟶ bilinFormsOverRingsCategory.{u} :=
  (Classifier.reindex regularSectionDeclaration.{u}.toCatHom
    valuesClassifierDeclaration).axiomProjection

noncomputable def integralFormsToBilRealization :
    FunctorRealization Fibrations.IntegralFormsToBilExpr integralFormsCategory.{u}
      bilinFormsOverRingsCategory.{u} integralFormsToBilDeclaration.toFunctor :=
  { sourceRealization := integralFormsRealization
    targetRealization := bilinFormsOverRingsRealization }

noncomputable def integralLatticesCategory : ObjCat.{u + 1, u} :=
  (Classifier.reindex integralFormsToBilDeclaration.{u} latticeClassifierDeclaration).total

noncomputable def integralLatticesRealization :
    CategoryRealization Fibrations.IntegralLattices integralLatticesCategory.{u} := {}

noncomputable def integralLatticesRefinement :
    RefinementRealization Fibrations.IntegralLattices integralLatticesCategory.{u} where
  base := Fibrations.IntegralForms
  classifierId := ClassifierId.bilLattice
  expression_eq := rfl
  baseCategory := integralFormsCategory
  host := Fibrations.BilinFormsOverRings
  hostCategory := bilinFormsOverRingsCategory
  baseRealization := integralFormsRealization
  classifier := latticeClassifierDeclaration
  classifierRealization := latticeClassifierRealization
  baseToHost := integralFormsToBilDeclaration
  reindexed := Classifier.reindex integralFormsToBilDeclaration latticeClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl

normalized_registry .functor
  { id := FunctorId.modulesProjection,
    source := Modules.ModulesTotal
    target := Algebra.Catalogue.Rings.Rings
    declaration :=
      `CasCatalogue.Catalogue.FibrationRegistration.modulesProjectionDeclaration
    realization :=
      `CasCatalogue.Catalogue.FibrationRegistration.modulesProjectionRealization
    expression := Fibrations.ModulesProjectionExpr }
normalized_registry .fibration
  { id := FibrationId.modules, projection := FunctorId.modulesProjection,
    variance := .cartesian
    evidence := `CasCatalogue.Catalogue.FibrationRegistration.modulesProjection_isFibered }

normalized_registry .category
  { id := CategoryId.modulesOverRingsExt,
    declaration :=
      `CasCatalogue.Catalogue.FibrationRegistration.modulesOverRingsExtCategory
    expression := Fibrations.ModulesOverRingsExt
    realization :=
      `CasCatalogue.Catalogue.FibrationRegistration.modulesOverRingsExtRealization }
normalized_registry .functor
  { id := FunctorId.modulesExtRing,
    source := Fibrations.ModulesOverRingsExt
    target := Algebra.Catalogue.Rings.CommutativeRings
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.modulesExtRingDeclaration
    realization := `CasCatalogue.Catalogue.FibrationRegistration.modulesExtRingRealization
    expression := Fibrations.ModulesExtRingExpr }
normalized_registry .fibration
  { id := FibrationId.modulesExt, projection := FunctorId.modulesExtRing,
    variance := .cocartesian
    evidence := `CasCatalogue.Catalogue.FibrationRegistration.modulesExtRing_isCofibered }

normalized_registry .category
  { id := CategoryId.bilinFormsOverRings,
    declaration :=
      `CasCatalogue.Catalogue.FibrationRegistration.bilinFormsOverRingsCategory
    expression := Fibrations.BilinFormsOverRings
    realization :=
      `CasCatalogue.Catalogue.FibrationRegistration.bilinFormsOverRingsRealization }
normalized_registry .functor
  { id := FunctorId.bilinFormsValues,
    source := Fibrations.BilinFormsOverRings
    target := Fibrations.ModulesOverRingsExt
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.bilinFormsValuesDeclaration
    realization := `CasCatalogue.Catalogue.FibrationRegistration.bilinFormsValuesRealization
    expression := Fibrations.BilinFormsValuesExpr }
normalized_registry .fibration
  { id := FibrationId.bilinForms, projection := FunctorId.bilinFormsValues,
    variance := .cocartesian
    evidence := `CasCatalogue.Catalogue.FibrationRegistration.bilinFormsValues_isCofibered }

end

normalized_registry .functor
  { id := FunctorId.modulesExtRegularSection,
    source := Algebra.Catalogue.Rings.CommutativeRings
    target := Fibrations.ModulesOverRingsExt
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.regularSectionDeclaration
    realization := `CasCatalogue.Catalogue.FibrationRegistration.regularSectionRealization
    expression := Fibrations.RegularSectionExpr }
normalized_registry .classifier
  { id := ClassifierId.bilValues,
    declaration :=
      `CasCatalogue.Catalogue.FibrationRegistration.valuesClassifierDeclaration
    host := Fibrations.ModulesOverRingsExt
    realization :=
      `CasCatalogue.Catalogue.FibrationRegistration.valuesClassifierRealization }
normalized_registry .category
  { id := CategoryId.integralForms,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.integralFormsCategory
    expression := Fibrations.IntegralForms
    realization := `CasCatalogue.Catalogue.FibrationRegistration.integralFormsRealization
    refinementRealization :=
      some `CasCatalogue.Catalogue.FibrationRegistration.integralFormsRefinement }
normalized_registry .classifier
  { id := ClassifierId.bilLattice,
    declaration :=
      `CasCatalogue.Catalogue.FibrationRegistration.latticeClassifierDeclaration
    host := Fibrations.BilinFormsOverRings
    realization :=
      `CasCatalogue.Catalogue.FibrationRegistration.latticeClassifierRealization }
normalized_registry .category
  { id := CategoryId.latticesOverRings,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.latticesOverRingsCategory
    expression := Fibrations.LatticesOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.latticesOverRingsRealization
    refinementRealization :=
      some `CasCatalogue.Catalogue.FibrationRegistration.latticesOverRingsRefinement }

normalized_registry .functor
  { id := FunctorId.integralFormsToBil,
    source := Fibrations.IntegralForms
    target := Fibrations.BilinFormsOverRings
    declaration :=
      `CasCatalogue.Catalogue.FibrationRegistration.integralFormsToBilDeclaration
    realization :=
      `CasCatalogue.Catalogue.FibrationRegistration.integralFormsToBilRealization
    expression := Fibrations.IntegralFormsToBilExpr
    structural := true }
normalized_registry .category
  { id := CategoryId.integralLattices,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.integralLatticesCategory
    expression := Fibrations.IntegralLattices
    realization :=
      `CasCatalogue.Catalogue.FibrationRegistration.integralLatticesRealization
    refinementRealization :=
      some `CasCatalogue.Catalogue.FibrationRegistration.integralLatticesRefinement }

/-! ### Negative probe: a refinement must be the pullback along the identity of its host -/

/-- A constant endofunctor of `Bil`, at the zero `ℤ`-valued form on `ℤ`. -/
noncomputable def constantBilEndo : bilinFormsOverRingsCategory.{0} ⟶ bilinFormsOverRingsCategory :=
  ((Functor.const _).obj
    (⟨CommRingCat.of ℤ,
      LeanCategories.Modules.Bilinear.Valued.BilWFormCat.of (ModuleCat.of ℤ ℤ)
        (ModuleCat.of ℤ ℤ) 0⟩ : BilinFormsOverRings.{0})).toCatHom

noncomputable def badLatticesCategory : ObjCat.{1, 0} :=
  (Classifier.reindex constantBilEndo latticeClassifierDeclaration).total

noncomputable def badLatticesRealization :
    CategoryRealization Fibrations.LatticesOverRings badLatticesCategory := {}

noncomputable def badLatticesRefinement :
    RefinementRealization Fibrations.LatticesOverRings badLatticesCategory where
  base := Fibrations.BilinFormsOverRings
  classifierId := ClassifierId.bilLattice
  expression_eq := rfl
  baseCategory := bilinFormsOverRingsCategory
  host := Fibrations.BilinFormsOverRings
  hostCategory := bilinFormsOverRingsCategory
  baseRealization := bilinFormsOverRingsRealization
  classifier := latticeClassifierDeclaration
  classifierRealization := latticeClassifierRealization
  baseToHost := constantBilEndo
  reindexed := Classifier.reindex constantBilEndo latticeClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let state ← pure ()
    let _ := state
    let accepted ← try
        validateRegistryEntryDeclaration (.category
          { id := ⟨"cat.probe.bad_lattices"⟩
            declaration := `CasCatalogue.Catalogue.FibrationRegistration.badLatticesCategory
            expression := Fibrations.LatticesOverRings
            realization :=
              `CasCatalogue.Catalogue.FibrationRegistration.badLatticesRealization
            refinementRealization :=
              some `CasCatalogue.Catalogue.FibrationRegistration.badLatticesRefinement })
        pure true
      catch _ => pure false
    if accepted then
      throwError "a refinement along a constant functor was accepted"

/-! ### Negative probe: a pullback must be along a registered route -/

/-- A constant functor `CommRing ⥤ ∫ Mod` at `(ℤ, ℤ)`: not a registered route. -/
noncomputable def constantSection :
    Algebra.CommutativeRings.{0} ⥤ modulesOverRingsExtCategory.{0} :=
  (Functor.const _).obj (regularSection.obj (CommRingCat.of ℤ))

noncomputable def badIntegralFormsCategory : ObjCat.{1, 0} :=
  (Classifier.reindex constantSection.toCatHom valuesClassifierDeclaration).total

noncomputable def badIntegralFormsRealization :
    CategoryRealization Fibrations.IntegralForms badIntegralFormsCategory := {}

noncomputable def badIntegralFormsRefinement :
    RefinementRealization Fibrations.IntegralForms badIntegralFormsCategory where
  base := Algebra.Catalogue.Rings.CommutativeRings
  classifierId := ClassifierId.bilValues
  expression_eq := rfl
  baseCategory := Algebra.CommutativeRings
  host := Fibrations.ModulesOverRingsExt
  hostCategory := modulesOverRingsExtCategory
  baseRealization := Algebra.CatalogueRegistration.commutativeRingsRealization
  classifier := valuesClassifierDeclaration
  classifierRealization := valuesClassifierRealization
  baseToHost := constantSection.toCatHom
  reindexed := Classifier.reindex constantSection.toCatHom valuesClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let accepted ← try
        validateRegistryEntryDeclaration (.category
          { id := ⟨"cat.probe.bad_integral_forms"⟩
            declaration :=
              `CasCatalogue.Catalogue.FibrationRegistration.badIntegralFormsCategory
            expression := Fibrations.IntegralForms
            realization :=
              `CasCatalogue.Catalogue.FibrationRegistration.badIntegralFormsRealization
            refinementRealization :=
              some `CasCatalogue.Catalogue.FibrationRegistration.badIntegralFormsRefinement })
        pure true
      catch _ => pure false
    if accepted then
      throwError "a pullback along an unregistered constant functor was accepted"

/-! ### Negative probes: evidence must prove the stated variance of the registered projection -/

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let rejects (entry : RegistryEntry) : MetaM Bool := do
      try
        validateRegistryEntryDeclaration entry
        pure false
      catch _ => pure true
    -- cartesian evidence registered as cocartesian
    unless ← rejects (.fibration
        { id := ⟨"fib.probe.variance"⟩, projection := FunctorId.modulesProjection,
          variance := .cocartesian
          evidence :=
            `CasCatalogue.Catalogue.FibrationRegistration.modulesProjection_isFibered }) do
      throwError "cartesian evidence was accepted for a cocartesian fibration"
    -- evidence about another functor
    unless ← rejects (.fibration
        { id := ⟨"fib.probe.functor"⟩, projection := FunctorId.bilinFormsValues,
          variance := .cocartesian
          evidence :=
            `CasCatalogue.Catalogue.FibrationRegistration.modulesExtRing_isCofibered }) do
      throwError "evidence about q was accepted for p"
    -- positive control
    if ← rejects (.fibration
        { id := ⟨"fib.probe.control"⟩, projection := FunctorId.bilinFormsValues,
          variance := .cocartesian
          evidence :=
            `CasCatalogue.Catalogue.FibrationRegistration.bilinFormsValues_isCofibered }) then
      throwError "the canonical forms fibration was rejected"

end CasCatalogue.Catalogue.FibrationRegistration
