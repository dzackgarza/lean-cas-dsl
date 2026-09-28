/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Foundation.Actions
public import CasCatalogue.Leaves.Modules.CatalogueRegistration
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CasCatalogue.Decide
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Modules.Catalogue

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

/-- Free `ℤ`-modules of finite rank: `n` denotes `ℤⁿ`, an `n × m` matrix a map `ℤᵐ → ℤⁿ`. -/
abbrev freeModuleRealizer : Realizer := ⟨ℕ, fun m n => Matrix (Fin n) (Fin m) ℤ⟩

/-- The denotation in `Mod_ℤ`. -/
noncomputable def freeModuleDenotation : Denotation freeModuleRealizer (ModuleCat ℤ) where
  obj n := ModuleCat.of ℤ (Fin n → ℤ)
  map A := ModuleCat.ofHom (Matrix.mulVecLin A)

/-- The denotation in the `ℤ`-fibre of the total module category. -/
noncomputable def totalFreeModuleDenotation :
    Denotation freeModuleRealizer modulesTotalCategory.{0, 0} where
  obj n := (⟨RingCat.of ℤ, ModuleCat.of ℤ (Fin n → ℤ)⟩ : ModulesOverRings.{0, 0})
  map A := (modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ)).map
    (ModuleCat.ofHom (Matrix.mulVecLin A))

/-- The fibre inclusion `ι_ℤ` on free-module handles: the handle is placed over the base `ℤ`. -/
def fibreInclusionAction : RealizedAction (modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ))
    freeModuleDenotation totalFreeModuleDenotation where
  action := { obj := fun n => n, map := fun A => A }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp; rfl }

/-- The underlying-set functor on free-module handles: `ℤⁿ` is presented as `Fin n → ℤ` and a
matrix acts by matrix-vector multiplication. -/
def underlyingAction : RealizedAction modulesUnderlyingDeclaration.{0, 0}
    totalFreeModuleDenotation setDenotation where
  action := { obj := fun n => .intPow n, map := fun A x => A.mulVec x }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp; rfl }

/-- Equality of two maps of free `ℤ`-modules, decided from their matrices (CC-DECIDE): equal
matrices give equal maps, and different matrices give different maps (compare on basis vectors),
so the procedure is complete and never refutes an equality that holds. -/
def decideMapEq {m n : ℕ} (A B : Matrix (Fin n) (Fin m) ℤ) :
    Decision (freeModuleDenotation.map (a := m) (b := n) A = freeModuleDenotation.map B) :=
  if h : A = B then .proved (congrArg (freeModuleDenotation.map (a := m) (b := n)) h)
  else .refuted fun e => h <| by
    ext i j
    have := congrArg
      (fun f : freeModuleDenotation.obj m ⟶ freeModuleDenotation.obj n =>
        (ModuleCat.Hom.hom f (Pi.single j 1) : Fin n → ℤ) i) e
    change A.mulVec (Pi.single j 1) i = B.mulVec (Pi.single j 1) i at this
    simpa [Matrix.mulVec_single_one] using this

normalized_registry .action
  { id := ⟨"act.modules.fibre_inclusion.int_free"⟩
    edge := .functor FunctorId.modulesFibreInclusion
    realization := `CasCatalogue.Modules.Actions.fibreInclusionAction }

normalized_registry .action
  { id := ⟨"act.modules.underlying.int_free"⟩
    edge := .functor FunctorId.modulesUnderlying
    realization := `CasCatalogue.Modules.Actions.underlyingAction }

end CasCatalogue.Modules.Actions
