/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Syntax
public import CasCatalogue.Leaves.Modules.Expressions
public import CasCatalogue.Leaves.Algebra.Catalogue.Rings

@[expose] public section

/-!
# Stable identities and expressions of the registered fibrations (CC-FIB)

* `fib.modules`: the cartesian fibration `∫ᶜ Mod → Ring` of restriction of scalars.
* `fib.modules_ext`: the cocartesian fibration `∫ Mod → CommRing` of extension of scalars.
* `fib.bilin_forms`: the cocartesian fibration `p : Bil → ∫ Mod` of bilinear forms over
  modules over rings (FOUNDATIONS Example 31.2c), whose composite with `fib.modules_ext` is
  the projection of forms to rings.
-/

namespace CasCatalogue


namespace CategoryId
/-- `∫ Mod` over commutative rings, with extension of scalars. -/
def modulesOverRingsExt : CategoryId := ⟨"cat.modules_over_rings_ext"⟩
/-- Bilinear forms over all commutative rings and value modules. -/
def bilinFormsOverRings : CategoryId := ⟨"cat.bilin_forms_over_rings"⟩
/-- Lattices: the refinement of `Bil` by the lattice property. -/
def latticesOverRings : CategoryId := ⟨"cat.lattices_over_rings"⟩
/-- Integral forms: the pullback of `Bil` along the regular section `R ↦ (R, R)`. -/
def integralForms : CategoryId := ⟨"cat.integral_forms"⟩
/-- Integral lattices: integral forms that are lattices. -/
def integralLattices : CategoryId := ⟨"cat.integral_lattices"⟩
end CategoryId

namespace ClassifierId
/-- The lattice property on `Bil` (projective carrier, symmetric form). -/
def bilLattice : ClassifierId := ⟨"clf.bilin_forms.lattice"⟩
/-- The forms fibration `p : Bil → ∫ Mod`, as a classifier on `∫ Mod` (FOUNDATIONS Def. 5.1). -/
def bilValues : ClassifierId := ⟨"clf.bilin_forms.values"⟩
end ClassifierId

namespace FunctorId
/-- The projection `∫ᶜ Mod ⥤ Ring`. -/
def modulesProjection : FunctorId := ⟨"fun.modules.projection"⟩
/-- The projection `∫ Mod ⥤ CommRing` of the extension-of-scalars fibration. -/
def modulesExtRing : FunctorId := ⟨"fun.modules_ext.ring"⟩
/-- The projection `p : Bil ⥤ ∫ Mod` of forms to their value modules over their rings. -/
def bilinFormsValues : FunctorId := ⟨"fun.bilin_forms.values"⟩
/-- The regular section `CommRing ⥤ ∫ Mod`, `R ↦ (R, R)`. -/
def modulesExtRegularSection : FunctorId := ⟨"fun.modules_ext.regular_section"⟩
/-- The projection of the pullback `CommRing ×_{∫ Mod} Bil` to `Bil`. -/
def integralFormsToBil : FunctorId := ⟨"fun.integral_forms.to_bil"⟩
end FunctorId

namespace FibrationId
def modules : FibrationId := ⟨"fib.modules"⟩
def modulesExt : FibrationId := ⟨"fib.modules_ext"⟩
def bilinForms : FibrationId := ⟨"fib.bilin_forms"⟩
end FibrationId

namespace Fibrations

def ModulesOverRingsExt : CategoryExpr := .atom CategoryId.modulesOverRingsExt
def BilinFormsOverRings : CategoryExpr := .atom CategoryId.bilinFormsOverRings

/-- Lattices, as the refinement of `Bil` by the lattice property (audit §4). -/
def LatticesOverRings : CategoryExpr := .refine BilinFormsOverRings ClassifierId.bilLattice

/-- Integral forms: `CommRing ×_{∫ Mod} Bil` along the regular section. -/
def IntegralForms : CategoryExpr :=
  .refine Algebra.Catalogue.Rings.CommutativeRings ClassifierId.bilValues

/-- Integral lattices: the lattice refinement of integral forms, along their projection to
`Bil`. -/
def IntegralLattices : CategoryExpr := .refine IntegralForms ClassifierId.bilLattice

def IntegralFormsToBilExpr : FunctorExpr IntegralForms BilinFormsOverRings :=
  .atomic FunctorId.integralFormsToBil

def RegularSectionExpr :
    FunctorExpr Algebra.Catalogue.Rings.CommutativeRings ModulesOverRingsExt :=
  .atomic FunctorId.modulesExtRegularSection

def ModulesProjectionExpr : FunctorExpr Modules.ModulesTotal Algebra.Catalogue.Rings.Rings :=
  .atomic FunctorId.modulesProjection
def ModulesExtRingExpr :
    FunctorExpr ModulesOverRingsExt Algebra.Catalogue.Rings.CommutativeRings :=
  .atomic FunctorId.modulesExtRing
def BilinFormsValuesExpr : FunctorExpr BilinFormsOverRings ModulesOverRingsExt :=
  .atomic FunctorId.bilinFormsValues

end Fibrations

end CasCatalogue
