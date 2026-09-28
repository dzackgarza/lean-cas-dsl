/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.FibrationRegistration
public import LeanCategories.Modules.Quadratic.Valued.BaseChangePseudofunctor
public meta import CasCatalogue.FibrationRegistration
public meta import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# The quadratic forms fibration (CC-FIB, `cc-quad-basechange`)

`fib.quad_forms`: the total category `Quad` of quadratic forms over all commutative rings and value
modules (the Grothendieck construction of characteristic-free base change,
`LeanCategories.Modules.Quadratic.Valued.quadBaseChangePseudofunctor`) projects to commutative rings
as a cocartesian fibration; its transport is base change `s ⊗ m ↦ s² ⊗ q(m)`, with no hypothesis on
`2`. (The finer projection to value modules over rings, as `fib.bilin_forms` has for `Bil`, is not
registered.)
-/

namespace CasCatalogue

namespace CategoryId
/-- Quadratic forms over all commutative rings and value modules. -/
def quadFormsOverRings : CategoryId := ⟨"cat.quad_forms_over_rings"⟩
end CategoryId

namespace FunctorId
/-- The projection of quadratic forms to their commutative ring. -/
def quadFormsRing : FunctorId := ⟨"fun.quad_forms.ring"⟩
end FunctorId

namespace FibrationId
def quadForms : FibrationId := ⟨"fib.quad_forms"⟩
end FibrationId

namespace Fibrations
def QuadFormsOverRings : CategoryExpr := .atom CategoryId.quadFormsOverRings
def QuadFormsRingExpr : FunctorExpr QuadFormsOverRings Algebra.Catalogue.Rings.CommutativeRings :=
  .atomic FunctorId.quadFormsRing
end Fibrations

namespace Catalogue.FibrationRegistration

open CategoryTheory LeanCategories LeanCategories.Modules.Quadratic.Valued

universe u

noncomputable def quadFormsOverRingsCategory : ObjCat.{u + 1, u} :=
  Cat.of QuadFormsOverRings.{u}

noncomputable def quadFormsOverRingsRealization :
    CategoryRealization Fibrations.QuadFormsOverRings quadFormsOverRingsCategory.{u} := {}

noncomputable def quadFormsRingDeclaration :
    quadFormsOverRingsCategory.{u} ⥤ Algebra.CommutativeRings.{u} :=
  QuadFormsOverRings.ring

noncomputable def quadFormsRingRealization :
    FunctorRealization Fibrations.QuadFormsRingExpr quadFormsOverRingsCategory.{u}
      Algebra.CommutativeRings.{u} quadFormsRingDeclaration :=
  { sourceRealization := quadFormsOverRingsRealization
    targetRealization := Algebra.CatalogueRegistration.commutativeRingsRealization }

theorem quadFormsRing_isCofibered : quadFormsRingDeclaration.{u}.IsCofibered :=
  Pseudofunctor.Grothendieck.isCofibered_forget _

end Catalogue.FibrationRegistration

normalized_registry .category
  { id := CategoryId.quadFormsOverRings,
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.quadFormsOverRingsCategory
    expression := Fibrations.QuadFormsOverRings
    realization := `CasCatalogue.Catalogue.FibrationRegistration.quadFormsOverRingsRealization }
normalized_registry .functor
  { id := FunctorId.quadFormsRing
    source := Fibrations.QuadFormsOverRings
    target := Algebra.Catalogue.Rings.CommutativeRings
    declaration := `CasCatalogue.Catalogue.FibrationRegistration.quadFormsRingDeclaration
    realization := `CasCatalogue.Catalogue.FibrationRegistration.quadFormsRingRealization
    expression := Fibrations.QuadFormsRingExpr }
normalized_registry .fibration
  { id := FibrationId.quadForms, projection := FunctorId.quadFormsRing,
    variance := .cocartesian
    evidence := `CasCatalogue.Catalogue.FibrationRegistration.quadFormsRing_isCofibered }

end CasCatalogue
