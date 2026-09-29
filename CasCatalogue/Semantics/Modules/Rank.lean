/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Modules.CatalogueRegistration
public import CasCatalogue.Semantics.Foundation.Cardinality
public import LeanCategories.Modules.RankFunctor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.ConstructorCatalogue
public meta import CasCatalogue.Semantics.Modules.Expressions
public meta import CasCatalogue.Semantics.Foundation.Cardinality

@[expose] public section

/-!
# Rank: the one semantic rank method

`rank : Core(Mod_R) ⥤ Disc(Card)` (`LeanCategories.Modules.rankFunctor`) is registered once, as
`fun.modules.rank`, and presented as the iso-invariant method `rank` owned by `Mod_R`. Formed
modules, lattices and any leaf with a structural route to modules inherit it. Its Lean-native
action on free `ℤ`-modules is `ℤⁿ ↦ n`.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Foundation.Cardinality

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

end CasCatalogue
