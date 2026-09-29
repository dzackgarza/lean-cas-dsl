/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Modules.Actions
public import CasCatalogue.Semantics.Foundation.Cardinality
public import CasLeaves.Foundation.Cardinality
public import Mathlib.Data.ZMod.Basic
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Modules.Catalogue

@[expose] public section

/-!
# Lean-native realizations of modules over `ℤ/n` (CC-ACTION)

Two families of realizers of module fibres, used by the notebook surface (`cc-dsl-migration`):

* the cyclic `ℤ`-modules: a handle `n` denotes `ℤ/n` as a `ℤ`-module (`ℤ/0 = ℤ`), a morphism
  handle is a `ℤ`-linear map;
* the free `ℤ/n`-modules of finite rank: in the fibre over `ℤ/n`, a handle `k` denotes
  `(ℤ/n)ᵏ` and an `m × k` matrix over `ℤ/n` a linear map `(ℤ/n)ᵏ → (ℤ/n)ᵐ`.

Both carry actions of the registered fibre inclusion `ι_R : Mod_R ⥤ ∫ᶜ Mod` and of the underlying
set functor `U : ∫ᶜ Mod ⥤ Sets`; the underlying sets are presented as `ZMod n` and
`Fin k → ZMod n`, so `cardinality` runs through the registered actions (#53 §11: `(ℤ/2)⁴` has
cardinality 16).
-/

open CategoryTheory
open LeanCategories LeanCategories.Modules CasCatalogue.Foundation.Actions
open CasCatalogue.Modules.CatalogueRegistration

namespace CasCatalogue.Modules.Finite

/-! ### Cyclic `ℤ`-modules -/

/-- Cyclic `ℤ`-modules: `n` denotes `ℤ/n`, a morphism handle is a `ℤ`-linear map. -/
abbrev cyclicRealizer : Realizer := ⟨ℕ, fun m n => ZMod m →ₗ[ℤ] ZMod n⟩

/-- The denotation in `Mod_ℤ`. -/
noncomputable def cyclicDenotation :
    Denotation cyclicRealizer (Modules.Mathlib.ModulesOf.{0, 0} (RingCat.of ℤ)) where
  obj n := ModuleCat.of ℤ (ZMod n)
  map f := ModuleCat.ofHom f

/-- The denotation in the `ℤ`-fibre of the total module category. -/
noncomputable def totalCyclicDenotation :
    Denotation cyclicRealizer modulesTotalCategory.{0, 0} where
  obj n := (⟨RingCat.of ℤ, ModuleCat.of ℤ (ZMod n)⟩ : ModulesOverRings.{0, 0})
  map f := (modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ)).map (ModuleCat.ofHom f)

/-- The fibre inclusion `ι_ℤ` on cyclic-module handles. -/
def cyclicFibreInclusionAction :
    RealizedAction (modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ))
      cyclicDenotation totalCyclicDenotation where
  action := { obj := fun n => n, map := fun f => f }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp; rfl }

/-- The underlying set of `ℤ/n`, presented as `ZMod n`. -/
def cyclicUnderlyingAction : RealizedAction modulesUnderlyingDeclaration.{0, 0}
    totalCyclicDenotation setDenotation where
  action := { obj := fun n => .zmod n, map := fun f x => f x }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp; rfl }

/-! ### Free modules over `ℤ/n` -/

/-- Free `ℤ/n`-modules of finite rank: `k` denotes `(ℤ/n)ᵏ`, an `m × k` matrix a linear map
`(ℤ/n)ᵏ → (ℤ/n)ᵐ`. -/
abbrev freeRealizer (n : ℕ) : Realizer := ⟨ℕ, fun k m => Matrix (Fin m) (Fin k) (ZMod n)⟩

/-- The denotation in the fibre `Mod_{ℤ/n}`. -/
noncomputable def freeDenotation (n : ℕ) :
    Denotation (freeRealizer n) (Modules.Mathlib.ModulesOf.{0, 0} (RingCat.of (ZMod n))) where
  obj k := ModuleCat.of (ZMod n) (Fin k → ZMod n)
  map A := ModuleCat.ofHom (Matrix.mulVecLin A)

/-- The denotation in the `ℤ/n`-fibre of the total module category. -/
noncomputable def totalFreeDenotation (n : ℕ) :
    Denotation (freeRealizer n) modulesTotalCategory.{0, 0} where
  obj k := (⟨RingCat.of (ZMod n), ModuleCat.of (ZMod n) (Fin k → ZMod n)⟩ :
    ModulesOverRings.{0, 0})
  map A := (modulesFibreInclusionDeclaration.{0, 0} (RingCat.of (ZMod n))).map
    (ModuleCat.ofHom (Matrix.mulVecLin A))

/-- The fibre inclusion `ι_{ℤ/n}` on free-module handles. -/
def freeFibreInclusionAction (n : ℕ) :
    RealizedAction (modulesFibreInclusionDeclaration.{0, 0} (RingCat.of (ZMod n)))
      (freeDenotation n) (totalFreeDenotation n) where
  action := { obj := fun k => k, map := fun A => A }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp; rfl }

/-- The underlying set of `(ℤ/n)ᵏ`, presented as `Fin k → ZMod n`; a matrix acts by
matrix-vector multiplication. -/
def freeUnderlyingAction (n : ℕ) : RealizedAction modulesUnderlyingDeclaration.{0, 0}
    (totalFreeDenotation n) setDenotation where
  action := { obj := fun k => .zmodPow n k, map := fun A x => A.mulVec x }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp; rfl }

end CasCatalogue.Modules.Finite

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.modules.fibre_inclusion.cyclic_int"⟩
    edge := .functor FunctorId.modulesFibreInclusion
    realization := `CasCatalogue.Modules.Finite.cyclicFibreInclusionAction },
  .action
  { id := ⟨"act.modules.underlying.cyclic_int"⟩
    edge := .functor FunctorId.modulesUnderlying
    realization := `CasCatalogue.Modules.Finite.cyclicUnderlyingAction },
  .action
  { id := ⟨"act.modules.fibre_inclusion.zmod_free"⟩
    edge := .functor FunctorId.modulesFibreInclusion
    realization := `CasCatalogue.Modules.Finite.freeFibreInclusionAction },
  .action
  { id := ⟨"act.modules.underlying.zmod_free"⟩
    edge := .functor FunctorId.modulesUnderlying
    realization := `CasCatalogue.Modules.Finite.freeUnderlyingAction },
  .realizer
  { id := ⟨"rz.modules.cyclic_int"⟩, category := ⟨"cat.modules_r"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Finite.cyclicDenotation },
  .realizer
  { id := ⟨"rz.modules_total.cyclic_int"⟩, category := ⟨"cat.modules_total"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Finite.totalCyclicDenotation },
  .realizer
  { id := ⟨"rz.modules.zmod_free"⟩, category := ⟨"cat.modules_r"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Finite.freeDenotation },
  .realizer
  { id := ⟨"rz.modules_total.zmod_free"⟩, category := ⟨"cat.modules_total"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Finite.totalFreeDenotation }] }

end CasCatalogue
