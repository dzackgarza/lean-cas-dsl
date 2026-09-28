/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Modules.Actions
public import CasCatalogue.Leaves.Foundation.Cardinality
public import LeanCategories.Modules.RankFunctor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.ConstructorCatalogue
public meta import CasCatalogue.Leaves.Modules.Expressions
public meta import CasCatalogue.Leaves.Foundation.Cardinality

@[expose] public section

/-!
# Rank: the one semantic rank method

`rank : Core(Mod_R) ⥤ Disc(Card)` (`LeanCategories.Modules.rankFunctor`) is registered once, as
`fun.modules.rank`, and presented as the iso-invariant method `rank` owned by `Mod_R`. Formed
modules, lattices and any leaf with a structural route to modules inherit it. Its Lean-native
action on free `ℤ`-modules is `ℤⁿ ↦ n`.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Modules.Actions CasCatalogue.Foundation.Cardinality

namespace CasCatalogue

namespace CategoryId
def coreModules : CategoryId := ⟨"cat.core_modules_r"⟩
end CategoryId

namespace FunctorId
def modulesRank : FunctorId := ⟨"fun.modules.rank"⟩
end FunctorId

namespace Modules.Rank

universe u

def CoreModules : CategoryExpr := .construct ConstructorId.core #[.category Modules.Modules]
def RankExpr : FunctorExpr CoreModules Foundation.Cardinality.Cardinals :=
  .atomic FunctorId.modulesRank

noncomputable section

def coreModulesCategory (R : RingCat.{u}) :=
  Constructors.core (Modules.Mathlib.ModulesOf.{u, u} R)
def coreModulesRealization (R : RingCat.{u}) :
    CategoryRealization CoreModules (coreModulesCategory R) := {}

/-- `rank : Core(Mod_R) ⥤ Disc(Card)`. -/
def rankDeclaration (R : RingCat.{u}) : coreModulesCategory R ⥤ cardinalsCategory.{u} :=
  Modules.rankFunctor R
def rankRealization (R : RingCat.{u}) :
    FunctorRealization RankExpr (coreModulesCategory R) cardinalsCategory.{u}
      (rankDeclaration R) :=
  { sourceRealization := coreModulesRealization R, targetRealization := cardinalsRealization }

end

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

normalized_registry .category
  { id := CategoryId.coreModules
    declaration := `CasCatalogue.Modules.Rank.coreModulesCategory
    expression := CoreModules
    realization := `CasCatalogue.Modules.Rank.coreModulesRealization }
normalized_registry .functor
  { id := FunctorId.modulesRank, source := CoreModules, target := Foundation.Cardinality.Cardinals
    declaration := `CasCatalogue.Modules.Rank.rankDeclaration
    realization := `CasCatalogue.Modules.Rank.rankRealization
    expression := RankExpr }
normalized_registry .method
  { id := ⟨"meth.rank"⟩, name := "rank", owner := Modules.Modules
    functor := FunctorId.modulesRank, shape := .isoInvariant }
normalized_registry .action
  { id := ⟨"act.modules.rank.int_free"⟩, edge := .functor FunctorId.modulesRank
    realization := `CasCatalogue.Modules.Rank.rankAction }

normalized_registry .realizer
  { id := ⟨"rz.core_modules.int_free"⟩, category := ⟨"cat.core_modules_r"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Rank.coreFreeModuleDenotation }

end CasCatalogue
