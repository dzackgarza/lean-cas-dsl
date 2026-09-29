/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Catalogue.Semantics.Limits.Registration
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Tactic.Ring
public meta import CasCatalogue.Leaf
public meta import LeanCategories.Catalogue.Semantics.Limits.Registration

@[expose] public section

/-!
# Formed modules with varying values, presented (specimen)

A handle of `BilWForm(ℤ)` is either free — `ℤⁿ` with a Gram form valued in `ℤ` or `ℚ`, given by
its entries — or the cokernel of a map of free ones, kept as that map: its denotation is
lean-categories' cokernel object (`BilWFormCat.cokernelObject`), so the leaf's presentation of the
registered cokernel's apex is the identity (`cokernelApex`), and the coprojection and descents are
the core's. The discriminant `L♯/L` of a lattice is such a cokernel.
-/

open CategoryTheory Limits
open LeanCategories.Modules.Bilinear.Valued

namespace CasCatalogue.Modules.Bilinear.Valued.WForms

/-- The value modules presented here: `ℤ` and `ℚ`. -/
inductive ValueRing
  | int
  | rat
  deriving DecidableEq, Repr

abbrev ValueRing.carrier : ValueRing → Type
  | .int => ℤ
  | .rat => ℚ

instance ValueRing.instCommRing : (v : ValueRing) → CommRing v.carrier
  | .int => inferInstanceAs (CommRing ℤ)
  | .rat => inferInstanceAs (CommRing ℚ)

/-- The canonical map of values `ℤ → ℤ`, `ℤ → ℚ`, `ℚ → ℚ` (`Int.cast`). -/
def ValueRing.castHom : (v w : ValueRing) → Option (v.carrier →+* w.carrier)
  | .int, .int => some (RingHom.id ℤ)
  | .int, .rat => some (Int.castRingHom ℚ)
  | .rat, .rat => some (RingHom.id ℚ)
  | .rat, .int => none

/-- `ℤⁿ` with a Gram form valued in `ℤ` or `ℚ`. -/
structure FreeWForm where
  rank : ℕ
  values : ValueRing
  gram : Fin rank → Fin rank → values.carrier

/-- The form `(x, y) ↦ Σ xᵢ yⱼ Gᵢⱼ`. -/
def FreeWForm.bilin (a : FreeWForm) : LinearMap.BilinMap ℤ (Fin a.rank → ℤ) a.values.carrier :=
  LinearMap.mk₂ ℤ (fun x y => ∑ i, ∑ j, ((x i * y j : ℤ) : a.values.carrier) * a.gram i j)
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Int.cast_add, ← Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Int.cast_add, add_mul,
      ← Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

@[simp]
theorem FreeWForm.bilin_apply (a : FreeWForm) (x y : Fin a.rank → ℤ) :
    a.bilin x y = ∑ i, ∑ j, ((x i * y j : ℤ) : a.values.carrier) * a.gram i j :=
  rfl

/-- The formed module a free handle denotes. -/
noncomputable def FreeWForm.denote (a : FreeWForm) : BilWFormCat ℤ :=
  BilWFormCat.of (ModuleCat.of ℤ (Fin a.rank → ℤ)) (ModuleCat.of ℤ a.values.carrier)
    (TensorProduct.lift a.bilin)

/-- A map of free forms: an integer matrix on carriers, the canonical map on values, preserving
the forms. -/
structure FreeHom (a b : FreeWForm) where
  matrix : Fin b.rank → Fin a.rank → ℤ
  cast : a.values.carrier →+* b.values.carrier
  cast_eq : ValueRing.castHom a.values b.values = some cast
  preserves : ∀ x y, cast (a.bilin x y) =
    b.bilin (fun i => ∑ k, matrix i k * x k) (fun i => ∑ k, matrix i k * y k)

/-- The carrier map of a map of free forms. -/
def FreeHom.carrier {a b : FreeWForm} (f : FreeHom a b) :
    (Fin a.rank → ℤ) →ₗ[ℤ] (Fin b.rank → ℤ) where
  toFun x i := ∑ k, f.matrix i k * x k
  map_add' x y := by funext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by funext i; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

@[simp]
theorem FreeHom.carrier_apply {a b : FreeWForm} (f : FreeHom a b) (x : Fin a.rank → ℤ)
    (i : Fin b.rank) : f.carrier x i = ∑ k, f.matrix i k * x k :=
  rfl

/-- The morphism of formed modules a map of free forms denotes. -/
noncomputable def FreeHom.toHom {a b : FreeWForm} (f : FreeHom a b) : a.denote ⟶ b.denote :=
  BilWFormCat.homMk f.carrier f.cast.toIntAlgHom.toLinearMap (fun x y => f.preserves x y)

/-- Presented formed modules with varying values: free ones, and cokernels of maps of free ones. -/
inductive WFormHandle
  | free (a : FreeWForm)
  | cokernel (a b : FreeWForm) (f : FreeHom a b)

noncomputable def WFormHandle.denote : WFormHandle → BilWFormCat ℤ
  | .free a => a.denote
  | .cokernel _ _ f => BilWFormCat.cokernelObject f.toHom

abbrev WFormHandles : Type := InducedCategory (BilWFormCat ℤ) WFormHandle.denote

noncomputable def wformDenotation : WFormHandles ⥤ BilWFormCat ℤ := inducedFunctor _

noncomputable def wformDenotationFullyFaithful : wformDenotation.FullyFaithful :=
  fullyFaithfulInducedFunctor _

/-- A map of free forms, as a morphism handle. -/
noncomputable def FreeHom.handle {a b : FreeWForm} (f : FreeHom a b) :
    @Quiver.Hom WFormHandles _ (.free a) (.free b) :=
  InducedCategory.homMk f.toHom

/-- The apex of the registered cokernel of a map of free forms: the cokernel handle, whose
denotation is the cokernel object itself. -/
noncomputable def cokernelApex (a b : FreeWForm) (f : FreeHom a b) :
    Σ c : WFormHandles, wformDenotation.obj c ≅
      (Limits.Registration.bilWFormCokernel f.toHom).cocone.pt :=
  ⟨.cokernel a b f, Iso.refl _⟩

end CasCatalogue.Modules.Bilinear.Valued.WForms

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .realizer
  { id := ⟨"rz.bil_wform.presented"⟩, category := CategoryId.bilWForm, backend := "lean"
    denotation := `CasCatalogue.Modules.Bilinear.Valued.WForms.wformDenotation
    fullyFaithful :=
      some `CasCatalogue.Modules.Bilinear.Valued.WForms.wformDenotationFullyFaithful },
  .limitRealization
  { id := ⟨"colimr.bil_w_form.cokernel.presented"⟩, limit := ⟨"colim.bil_w_form.cokernel"⟩
    realizer := ⟨"rz.bil_wform.presented"⟩
    realization := `CasCatalogue.Modules.Bilinear.Valued.WForms.cokernelApex }] }

end CasCatalogue
