/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Modules.Actions
public import CasCatalogue.Semantics.Foundation.Cardinality
public import CasLeaves.Foundation.Cardinality
public import LeanCategories.Modules.RankFunctor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import CasCatalogue.Semantics.Modules.Rank
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.ConstructorCatalogue
public meta import CasCatalogue.Semantics.Modules.Expressions
public meta import CasCatalogue.Semantics.Foundation.Cardinality
public meta import CasLeaves.Foundation.Cardinality
public meta import CasCatalogue.Semantics.Modules.Rank

@[expose] public section

/-!
# Lean-native realizations for `CasCatalogue.Semantics.Modules.Rank`

The leaf half of `CasCatalogue.Semantics.Modules.Rank`: handles, their denotations and the actions of the registered functors on
them, contributed through `register_leaf`.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Modules.Actions CasCatalogue.Foundation.Cardinality

namespace CasCatalogue

namespace Modules.Rank

universe u

/-- Free `ℤ`-modules of finite rank, with their identity isomorphisms. -/
abbrev coreFreeModuleRealizer : Realizer := ⟨ℕ, fun a b => PLift (a = b)⟩

noncomputable def coreFreeModuleDenotation :
    Denotation coreFreeModuleRealizer (coreModulesCategory (RingCat.of ℤ)) where
  obj n := ⟨freeModuleDenotation.obj n⟩
  map h := eqToHom (by cases h.down; rfl)

/-- The rank of `ℤⁿ` is `n`. -/
def rankAction :
    RealizedAction (rankDeclaration (RingCat.of ℤ)) coreFreeModuleDenotation
      cardinalDenotation where
  action := { obj := fun n => .finite n, map := fun h => ⟨by cases h.down; rfl⟩ }
  realizes :=
    { obj := fun n => congrArg Discrete.mk (rank_fin_fun (R := ℤ) n).symm
      map := fun _ => ULift.ext _ _ (Subsingleton.elim _ _) }

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
