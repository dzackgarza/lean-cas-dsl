/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.FibrationRegistration
public meta import CasCatalogue.Semantics.FibrationRegistration
public meta import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# The lattice conditions as classifiers on `Bil` (CC-FIB, audit §4)

Finite carrier, free carrier, evenness (`b(v, v) ∈ 2W`) and unimodularity (bijective adjoint) are
property classifiers on the total category `Bil` of bilinear forms, uniform over rings and value
modules (`LeanCategories.Lattices.Valued.BilRefinements`). The lattice kinds are refinements along
the registered projections to `Bil`:

* finite projective lattices = lattices refined by a finite carrier;
* finite free lattices = finite projective lattices refined by a free carrier;
* unimodular lattices = lattices refined by unimodularity;
* even integral lattices = integral lattices refined by evenness (`isEven_iff_exists_two_smul`:
  at `W = R` this is the classical `IsEven`, the `2R`-integrality of the diagonal form).
-/

namespace CasCatalogue

namespace ClassifierId
/-- A finite carrier, on `Bil`. -/
def bilFinite : ClassifierId := ⟨"clf.bilin_forms.finite"⟩
/-- A free carrier, on `Bil`. -/
def bilFree : ClassifierId := ⟨"clf.bilin_forms.free"⟩
/-- Evenness, `b(v, v) ∈ 2W`, on `Bil`. -/
def bilEven : ClassifierId := ⟨"clf.bilin_forms.even"⟩
/-- Unimodularity, a bijective adjoint, on `Bil`. -/
def bilUnimodular : ClassifierId := ⟨"clf.bilin_forms.unimodular"⟩
end ClassifierId

namespace CategoryId
/-- Finite projective lattices: lattices with a finite carrier. -/
def finiteProjectiveLatticesOverRings : CategoryId := ⟨"cat.finite_projective_lattices_over_rings"⟩
/-- Finite free lattices: finite projective lattices with a free carrier. -/
def finiteFreeLatticesOverRings : CategoryId := ⟨"cat.finite_free_lattices_over_rings"⟩
/-- Unimodular lattices: lattices with a bijective adjoint. -/
def unimodularLatticesOverRings : CategoryId := ⟨"cat.unimodular_lattices_over_rings"⟩
/-- Even integral lattices: `b(v, v) ∈ 2R`. -/
def evenIntegralLattices : CategoryId := ⟨"cat.even_integral_lattices"⟩
end CategoryId

namespace FunctorId
/-- Lattices to `Bil`: the projection of the lattice refinement. -/
def latticesToBil : FunctorId := ⟨"fun.lattices_over_rings.to_bil"⟩
/-- Finite projective lattices to `Bil`. -/
def finiteProjectiveLatticesToBil : FunctorId := ⟨"fun.finite_projective_lattices.to_bil"⟩
/-- Integral lattices to `Bil`, through integral forms. -/
def integralLatticesToBil : FunctorId := ⟨"fun.integral_lattices.to_bil"⟩
end FunctorId

namespace Fibrations
def FiniteProjectiveLatticesOverRings : CategoryExpr := .refine Fibrations.LatticesOverRings ClassifierId.bilFinite
def FiniteFreeLatticesOverRings : CategoryExpr := .refine FiniteProjectiveLatticesOverRings ClassifierId.bilFree
def UnimodularLatticesOverRings : CategoryExpr := .refine Fibrations.LatticesOverRings ClassifierId.bilUnimodular
def EvenIntegralLattices : CategoryExpr := .refine Fibrations.IntegralLattices ClassifierId.bilEven
def LatticesToBilExpr : FunctorExpr LatticesOverRings BilinFormsOverRings :=
  .atomic FunctorId.latticesToBil
def FiniteProjectiveLatticesToBilExpr :
    FunctorExpr FiniteProjectiveLatticesOverRings BilinFormsOverRings :=
  .atomic FunctorId.finiteProjectiveLatticesToBil
def IntegralLatticesToBilExpr : FunctorExpr IntegralLattices BilinFormsOverRings :=
  .atomic FunctorId.integralLatticesToBil
end Fibrations

namespace Catalogue.FibrationRegistration

open CategoryTheory LeanCategories LeanCategories.Lattices.Valued

universe u

/-- Lattices to `Bil`: the projection of the lattice refinement. -/
noncomputable def latticesToBil : latticesOverRingsCategory.{u} ⟶ bilinFormsOverRingsCategory.{u} :=
  (Classifier.reindex (𝟙 bilinFormsOverRingsCategory.{u}) latticeClassifierDeclaration).baseProjection

/-- Integral lattices to `Bil`: through integral forms. -/
noncomputable def integralLatticesToBil :
    integralLatticesCategory.{u} ⟶ bilinFormsOverRingsCategory.{u} :=
  (Classifier.reindex integralFormsToBilDeclaration.{u} latticeClassifierDeclaration).baseProjection ≫
    integralFormsToBilDeclaration

noncomputable def finiteClassifierDeclaration : Classifier bilinFormsOverRingsCategory.{u} :=
  finiteClassifier.{u}.toClassifier

noncomputable def finiteClassifierRealization :
    ClassifierRealization Fibrations.BilinFormsOverRings ClassifierId.bilFinite
      bilinFormsOverRingsCategory.{u} finiteClassifierDeclaration :=
  { hostRealization := bilinFormsOverRingsRealization, totalRealization := {} }

noncomputable def freeClassifierDeclaration : Classifier bilinFormsOverRingsCategory.{u} :=
  freeClassifier.{u}.toClassifier

noncomputable def freeClassifierRealization :
    ClassifierRealization Fibrations.BilinFormsOverRings ClassifierId.bilFree
      bilinFormsOverRingsCategory.{u} freeClassifierDeclaration :=
  { hostRealization := bilinFormsOverRingsRealization, totalRealization := {} }

noncomputable def evenClassifierDeclaration : Classifier bilinFormsOverRingsCategory.{u} :=
  evenClassifier.{u}.toClassifier

noncomputable def evenClassifierRealization :
    ClassifierRealization Fibrations.BilinFormsOverRings ClassifierId.bilEven
      bilinFormsOverRingsCategory.{u} evenClassifierDeclaration :=
  { hostRealization := bilinFormsOverRingsRealization, totalRealization := {} }

noncomputable def unimodularClassifierDeclaration : Classifier bilinFormsOverRingsCategory.{u} :=
  unimodularClassifier.{u}.toClassifier

noncomputable def unimodularClassifierRealization :
    ClassifierRealization Fibrations.BilinFormsOverRings ClassifierId.bilUnimodular
      bilinFormsOverRingsCategory.{u} unimodularClassifierDeclaration :=
  { hostRealization := bilinFormsOverRingsRealization, totalRealization := {} }

noncomputable def finiteProjectiveLatticesCategory : ObjCat.{u + 1, u} :=
  (Classifier.reindex latticesToBil.{u} finiteClassifierDeclaration).total

noncomputable def finiteProjectiveLatticesRealization :
    CategoryRealization Fibrations.FiniteProjectiveLatticesOverRings finiteProjectiveLatticesCategory.{u} := {}

noncomputable def finiteProjectiveLatticesRefinement :
    RefinementRealization Fibrations.FiniteProjectiveLatticesOverRings finiteProjectiveLatticesCategory.{u} where
  base := Fibrations.LatticesOverRings
  classifierId := ClassifierId.bilFinite
  expression_eq := rfl
  baseCategory := latticesOverRingsCategory
  host := Fibrations.BilinFormsOverRings
  hostCategory := bilinFormsOverRingsCategory
  baseRealization := latticesOverRingsRealization
  classifier := finiteClassifierDeclaration
  classifierRealization := finiteClassifierRealization
  baseToHost := latticesToBil
  reindexed := Classifier.reindex latticesToBil finiteClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl

/-- Finite projective lattices to `Bil`. -/
noncomputable def finiteProjectiveLatticesToBil :
    finiteProjectiveLatticesCategory.{u} ⟶ bilinFormsOverRingsCategory.{u} :=
  (Classifier.reindex latticesToBil.{u} finiteClassifierDeclaration).baseProjection ≫ latticesToBil

noncomputable def finiteFreeLatticesCategory : ObjCat.{u + 1, u} :=
  (Classifier.reindex finiteProjectiveLatticesToBil.{u} freeClassifierDeclaration).total

noncomputable def finiteFreeLatticesRealization :
    CategoryRealization Fibrations.FiniteFreeLatticesOverRings finiteFreeLatticesCategory.{u} := {}

noncomputable def finiteFreeLatticesRefinement :
    RefinementRealization Fibrations.FiniteFreeLatticesOverRings finiteFreeLatticesCategory.{u} where
  base := Fibrations.FiniteProjectiveLatticesOverRings
  classifierId := ClassifierId.bilFree
  expression_eq := rfl
  baseCategory := finiteProjectiveLatticesCategory
  host := Fibrations.BilinFormsOverRings
  hostCategory := bilinFormsOverRingsCategory
  baseRealization := finiteProjectiveLatticesRealization
  classifier := freeClassifierDeclaration
  classifierRealization := freeClassifierRealization
  baseToHost := finiteProjectiveLatticesToBil
  reindexed := Classifier.reindex finiteProjectiveLatticesToBil freeClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl

noncomputable def unimodularLatticesCategory : ObjCat.{u + 1, u} :=
  (Classifier.reindex latticesToBil.{u} unimodularClassifierDeclaration).total

noncomputable def unimodularLatticesRealization :
    CategoryRealization Fibrations.UnimodularLatticesOverRings unimodularLatticesCategory.{u} := {}

noncomputable def unimodularLatticesRefinement :
    RefinementRealization Fibrations.UnimodularLatticesOverRings unimodularLatticesCategory.{u} where
  base := Fibrations.LatticesOverRings
  classifierId := ClassifierId.bilUnimodular
  expression_eq := rfl
  baseCategory := latticesOverRingsCategory
  host := Fibrations.BilinFormsOverRings
  hostCategory := bilinFormsOverRingsCategory
  baseRealization := latticesOverRingsRealization
  classifier := unimodularClassifierDeclaration
  classifierRealization := unimodularClassifierRealization
  baseToHost := latticesToBil
  reindexed := Classifier.reindex latticesToBil unimodularClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl

noncomputable def evenIntegralLatticesCategory : ObjCat.{u + 1, u} :=
  (Classifier.reindex integralLatticesToBil.{u} evenClassifierDeclaration).total

noncomputable def evenIntegralLatticesRealization :
    CategoryRealization Fibrations.EvenIntegralLattices evenIntegralLatticesCategory.{u} := {}

noncomputable def evenIntegralLatticesRefinement :
    RefinementRealization Fibrations.EvenIntegralLattices evenIntegralLatticesCategory.{u} where
  base := Fibrations.IntegralLattices
  classifierId := ClassifierId.bilEven
  expression_eq := rfl
  baseCategory := integralLatticesCategory
  host := Fibrations.BilinFormsOverRings
  hostCategory := bilinFormsOverRingsCategory
  baseRealization := integralLatticesRealization
  classifier := evenClassifierDeclaration
  classifierRealization := evenClassifierRealization
  baseToHost := integralLatticesToBil
  reindexed := Classifier.reindex integralLatticesToBil evenClassifierDeclaration
  equivalence := CategoryTheory.Equivalence.refl
  baseProjection := _
  baseProjection_eq := rfl
  classifierProjection := _
  classifierProjection_eq := rfl


noncomputable def latticesToBilRealization :
    FunctorRealization Fibrations.LatticesToBilExpr latticesOverRingsCategory.{u}
      bilinFormsOverRingsCategory.{u} latticesToBil.toFunctor :=
  { sourceRealization := latticesOverRingsRealization
    targetRealization := bilinFormsOverRingsRealization }

noncomputable def integralLatticesToBilRealization :
    FunctorRealization Fibrations.IntegralLatticesToBilExpr integralLatticesCategory.{u}
      bilinFormsOverRingsCategory.{u} integralLatticesToBil.toFunctor :=
  { sourceRealization := integralLatticesRealization
    targetRealization := bilinFormsOverRingsRealization }

noncomputable def finiteProjectiveLatticesToBilRealization :
    FunctorRealization Fibrations.FiniteProjectiveLatticesToBilExpr
      finiteProjectiveLatticesCategory.{u} bilinFormsOverRingsCategory.{u}
      finiteProjectiveLatticesToBil.toFunctor :=
  { sourceRealization := finiteProjectiveLatticesRealization
    targetRealization := bilinFormsOverRingsRealization }

end Catalogue.FibrationRegistration

normalized_registry .functor
  { id := FunctorId.latticesToBil, source := Fibrations.LatticesOverRings
    target := Fibrations.BilinFormsOverRings
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.latticesToBil
    realization := `CasCatalogue.Catalogue.FibrationRegistration.latticesToBilRealization
    expression := Fibrations.LatticesToBilExpr }
normalized_registry .functor
  { id := FunctorId.integralLatticesToBil, source := Fibrations.IntegralLattices
    target := Fibrations.BilinFormsOverRings
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.integralLatticesToBil
    realization := `CasCatalogue.Catalogue.FibrationRegistration.integralLatticesToBilRealization
    expression := Fibrations.IntegralLatticesToBilExpr }
normalized_registry .classifier
  { id := ClassifierId.bilFinite,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.finiteClassifierDeclaration
    host := Fibrations.BilinFormsOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.finiteClassifierRealization }
normalized_registry .classifier
  { id := ClassifierId.bilFree,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.freeClassifierDeclaration
    host := Fibrations.BilinFormsOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.freeClassifierRealization }
normalized_registry .classifier
  { id := ClassifierId.bilEven,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.evenClassifierDeclaration
    host := Fibrations.BilinFormsOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.evenClassifierRealization }
normalized_registry .classifier
  { id := ClassifierId.bilUnimodular,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.unimodularClassifierDeclaration
    host := Fibrations.BilinFormsOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.unimodularClassifierRealization }
normalized_registry .category
  { id := CategoryId.finiteProjectiveLatticesOverRings,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.finiteProjectiveLatticesCategory
    expression := Fibrations.FiniteProjectiveLatticesOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.finiteProjectiveLatticesRealization
    refinementRealization :=
      some `CasCatalogue.Catalogue.FibrationRegistration.finiteProjectiveLatticesRefinement }
normalized_registry .functor
  { id := FunctorId.finiteProjectiveLatticesToBil
    source := Fibrations.FiniteProjectiveLatticesOverRings
    target := Fibrations.BilinFormsOverRings
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.finiteProjectiveLatticesToBil
    realization :=
      `CasCatalogue.Catalogue.FibrationRegistration.finiteProjectiveLatticesToBilRealization
    expression := Fibrations.FiniteProjectiveLatticesToBilExpr }
normalized_registry .category
  { id := CategoryId.finiteFreeLatticesOverRings,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.finiteFreeLatticesCategory
    expression := Fibrations.FiniteFreeLatticesOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.finiteFreeLatticesRealization
    refinementRealization :=
      some `CasCatalogue.Catalogue.FibrationRegistration.finiteFreeLatticesRefinement }
normalized_registry .category
  { id := CategoryId.unimodularLatticesOverRings,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.unimodularLatticesCategory
    expression := Fibrations.UnimodularLatticesOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.unimodularLatticesRealization
    refinementRealization :=
      some `CasCatalogue.Catalogue.FibrationRegistration.unimodularLatticesRefinement }
normalized_registry .category
  { id := CategoryId.evenIntegralLattices,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.evenIntegralLatticesCategory
    expression := Fibrations.EvenIntegralLattices
    realization := `CasCatalogue.Catalogue.FibrationRegistration.evenIntegralLatticesRealization
    refinementRealization :=
      some `CasCatalogue.Catalogue.FibrationRegistration.evenIntegralLatticesRefinement }

end CasCatalogue
