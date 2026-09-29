/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Foundation.Actions
public import CasCatalogue.Semantics.Modules.CatalogueRegistration
public import Mathlib.LinearAlgebra.Matrix.ToLin
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Modules.Catalogue

@[expose] public section

/-!
# Lean-native realizations of free `ℤ`-modules (CC-ACTION)

A free `ℤ`-module of finite rank is realized by its rank `n`, denoting `ℤⁿ`; a linear map
`ℤᵐ → ℤⁿ` by an `n × m` integer matrix. The same handles realize the `ℤ`-fibre of the total
module category `∫ᶜ Mod`, with identity base maps.

Two registered functors carry actions on these handles:
* the fibre inclusion `ι_ℤ : Mod_ℤ ⥤ ∫ᶜ Mod` (`fun.modules.fibre_inclusion` at `R = ℤ`), and
* the underlying-set functor `U : ∫ᶜ Mod ⥤ Sets` (`fun.modules.underlying`), whose object action
  presents `ℤⁿ` and whose morphism action is matrix-vector multiplication.
-/

open CategoryTheory
open LeanCategories LeanCategories.Modules CasCatalogue.Foundation.Actions
open CasCatalogue.Modules.CatalogueRegistration

namespace CasCatalogue.Modules.Actions

/-- Free `ℤ`-modules of finite rank: `n` denotes `ℤⁿ`; morphisms are the linear maps between the
denotations (`InducedCategory`), built from integer matrices by `matrixHom`. -/
abbrev FreeModules : Type :=
  InducedCategory (ModuleCat.{0} (RingCat.of ℤ)) fun n : ℕ =>
    ModuleCat.of (RingCat.of ℤ) (Fin n → ℤ)

/-- The denotation in `Mod_ℤ`. -/
noncomputable def freeModuleDenotation : FreeModules ⥤ Modules.Mathlib.ModulesOf.{0, 0} (RingCat.of ℤ) :=
  inducedFunctor _

/-- The denotation in the `ℤ`-fibre of the total module category. -/
noncomputable def totalFreeModuleDenotation : FreeModules ⥤ modulesTotalCategory.{0, 0} :=
  freeModuleDenotation ⋙ modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ)

/-- The morphism handle of an `n × m` integer matrix: `x ↦ A x`. -/
def matrixHom {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ) : @Quiver.Hom FreeModules _ m n :=
  InducedCategory.homMk (ModuleCat.ofHom (Matrix.mulVecLin A))

/-- The fibre inclusion `ι_ℤ` on free-module handles: the handle is placed over the base `ℤ`. -/
noncomputable def fibreInclusionAction : RealizedAction (modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ))
    freeModuleDenotation totalFreeModuleDenotation :=
  RealizedAction.ofEq (𝟭 _) (Functor.id_comp _)

/-- The underlying-set functor on free-module handles: `ℤⁿ` is presented as `Fin n → ℤ`. -/
noncomputable def underlyingAction : RealizedAction modulesUnderlyingDeclaration.{0, 0}
    totalFreeModuleDenotation setDenotation :=
  (RealizedAction.induced
    (modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ) ⋙ modulesUnderlyingDeclaration)
    (fun n => SetHandle.intPow n) fun _ => rfl).pull

/-- Equality of two maps of free `ℤ`-modules, decided from their matrices (CC-DECIDE): equal
matrices give equal maps, and different matrices give different maps (compare on basis vectors),
so the procedure is complete and never refutes an equality that holds. -/
def decideMapEq {m n : ℕ} (A B : Matrix (Fin n) (Fin m) ℤ) :
    Decision (freeModuleDenotation.map (matrixHom A) = freeModuleDenotation.map (matrixHom B)) :=
  if h : A = B then .proved (by rw [h])
  else .refuted fun e => h <| by
    ext i j
    have := congrArg
      (fun f : freeModuleDenotation.obj m ⟶ freeModuleDenotation.obj n =>
        (ModuleCat.Hom.hom f (Pi.single j 1) : Fin n → ℤ) i) e
    change A.mulVec (Pi.single j 1) i = B.mulVec (Pi.single j 1) i at this
    simpa [Matrix.mulVec_single_one] using this

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.modules.fibre_inclusion.int_free"⟩
    edge := .functor FunctorId.modulesFibreInclusion
    realization := `CasCatalogue.Modules.Actions.fibreInclusionAction },
  .action
  { id := ⟨"act.modules.underlying.int_free"⟩
    edge := .functor FunctorId.modulesUnderlying
    realization := `CasCatalogue.Modules.Actions.underlyingAction },
  .realizer
  { id := ⟨"rz.modules.int_free"⟩, category := ⟨"cat.modules_r"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Actions.freeModuleDenotation },
  .realizer
  { id := ⟨"rz.modules_total.int_free"⟩, category := ⟨"cat.modules_total"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Actions.totalFreeModuleDenotation }] }

end CasCatalogue.Modules.Actions
