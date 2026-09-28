/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Modules.Actions
public import CasCatalogue.Leaves.Modules.Bilinear.Valued.CatalogueRegistration
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Modules.Bilinear.Valued.Catalogue

@[expose] public section

/-!
# Lean-native realizations of integer bilinear forms (CC-ACTION)

A `ℤ`-valued bilinear form on `ℤⁿ` is realized by its Gram matrix `G`, denoting
`(x, y) ↦ xᵀ G y`; a morphism by an integer matrix `A` with `Aᵀ G' A = G`, denoting the isometry
`x ↦ A x`. The forgetful functor `BilinModule(ℤ, ℤ) ⥤ Mod_ℤ` (`fun.bilin_module.forget`) acts by
forgetting the Gram matrix and keeping the rank and the matrix of the map.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued CasCatalogue.Modules.Actions

namespace CasCatalogue.Modules.Bilinear.Valued.Actions

/-- A `ℤ`-valued bilinear form on `ℤⁿ`, by its Gram matrix. -/
structure GramHandle where
  rank : ℕ
  gram : Matrix (Fin rank) (Fin rank) ℤ
  deriving DecidableEq, Repr

/-- The Gram handle of an `n × n` integer matrix given by its rows (the notebook's matrix
literal). -/
def GramHandle.ofRows (n : ℕ) (rows : List (List ℤ)) : GramHandle :=
  ⟨n, Matrix.of fun i j => (rows.getD i []).getD j 0⟩

/-- An isometry of Gram forms `ℤᵃ → ℤᵇ`: an integer matrix `A` with `Aᵀ G_b A = G_a`. -/
structure GramIsometry (a b : GramHandle) where
  matrix : Matrix (Fin b.rank) (Fin a.rank) ℤ
  preserves : matrix.transpose * b.gram * matrix = a.gram

/-- Integer bilinear forms by Gram matrix, with isometries. -/
abbrev gramRealizer : Realizer := ⟨GramHandle, GramIsometry⟩

/-- A matrix `A` with `Aᵀ H A = G` preserves the forms: `(A x)ᵀ H (A y) = xᵀ G y`. -/
theorem toLinearMap₂'_isometry {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (G : Matrix (Fin m) (Fin m) ℤ) (H : Matrix (Fin n) (Fin n) ℤ)
    (h : A.transpose * H * A = G) (x y : Fin m → ℤ) :
    Matrix.toLinearMap₂' ℤ H (A.mulVec x) (A.mulVec y) = Matrix.toLinearMap₂' ℤ G x y := by
  rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', ← h,
    ← Matrix.mulVec_mulVec y (A.transpose * H) A, ← Matrix.mulVec_mulVec _ A.transpose H,
    Matrix.dotProduct_mulVec x A.transpose, Matrix.vecMul_transpose]

/-- The denotation in `BilinModule(ℤ, ℤ)`: `G` denotes `(ℤⁿ, (x, y) ↦ xᵀ G y)`. -/
noncomputable def gramDenotation : Denotation gramRealizer (BilinModuleCat ℤ ℤ) where
  obj a := BilinModuleCat.ofBilinMap (Matrix.toLinearMap₂' ℤ a.gram)
  map f := BilinModuleCat.homMk (Matrix.mulVecLin f.matrix)
    (toLinearMap₂'_isometry f.matrix _ _ f.preserves)

/-- The forgetful functor on Gram handles: keep the rank and the matrix of the isometry. -/
def forgetAction : RealizedAction (forget ℤ ℤ) gramDenotation freeModuleDenotation where
  action := { obj := fun a => a.rank, map := fun f => f.matrix }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp; rfl }

normalized_registry .action
  { id := ⟨"act.bilin_module.forget.int_gram"⟩
    edge := .functor FunctorId.bilinModuleForget
    realization := `CasCatalogue.Modules.Bilinear.Valued.Actions.forgetAction }

normalized_registry .realizer
  { id := ⟨"rz.bilin_module.int_gram"⟩, category := ⟨"cat.bilin_module"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Bilinear.Valued.Actions.gramDenotation }

end CasCatalogue.Modules.Bilinear.Valued.Actions
