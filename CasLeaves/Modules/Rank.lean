/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Modules.Actions
public import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public import CasLeaves.Foundation.Cardinality
public import LeanCategories.Modules.RankFunctor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import LeanCategories.Catalogue.Semantics.Modules.Rank
public meta import CasCatalogue.Leaf
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Semantics.Modules.Expressions
public meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public meta import CasLeaves.Foundation.Cardinality
public meta import LeanCategories.Catalogue.Semantics.Modules.Rank

@[expose] public section

/-!
# Lean-native realizations for `LeanCategories.Catalogue.Semantics.Modules.Rank`

The leaf half of `LeanCategories.Catalogue.Semantics.Modules.Rank`: handles, their denotations and the actions of the registered functors on
them, contributed through `register_leaf`.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Modules.Actions CasCatalogue.Foundation.Cardinality

namespace CasCatalogue

namespace Modules.Rank

universe u

/-- The core of the free-module realization, `Core(FreeModules) ⥤ Core(Mod_ℤ)` (`Functor.core`):
morphism handles are linear isomorphisms. -/
noncomputable def coreFreeModuleDenotation : Core Modules.Actions.FreeModules ⥤ coreModulesCategory (RingCat.of ℤ) :=
  freeModuleDenotation.core

/-- Isomorphic free `ℤ`-modules of finite rank have the same rank. -/
theorem rank_eq_of_iso {m n : Modules.Actions.FreeModules} (e : m ≅ n) : (m : ℕ) = n := by
  let e' : (Fin m → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) := (freeModuleDenotation.mapIso e).toLinearEquiv
  simpa using e'.finrank_eq

/-- The rank of `ℤⁿ` is `n`, on the core. -/
def rankHandles : Core Modules.Actions.FreeModules ⥤ Discrete CardinalHandle where
  obj n := ⟨.finite n.of⟩
  map f := eqToHom (by rw [rank_eq_of_iso f.iso])

/-- The rank of `ℤⁿ` is `n`. -/
noncomputable def rankAction :
    RealizedAction (rankDeclaration (RingCat.of ℤ)) coreFreeModuleDenotation
      cardinalDenotation where
  action := rankHandles
  square := ⟨NatIso.ofComponents
    (fun n => eqToIso (congrArg Discrete.mk (rank_fin_fun (R := ℤ) n.of).symm))
    (fun _ => (Discrete.instSubsingletonDiscreteHom _ _).elim _ _)⟩

end Modules.Rank

open Modules.Rank

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.modules.rank.int_free"⟩, edge := .functor FunctorId.modulesRank
    realization := `CasCatalogue.Modules.Rank.rankAction },
  .realizer
  { id := ⟨"rz.core_modules.int_free"⟩, category := ⟨"cat.core_modules_r"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Rank.coreFreeModuleDenotation }] }

end CasCatalogue
