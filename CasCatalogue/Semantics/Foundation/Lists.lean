/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Foundation.CatalogueRegistration
public import LeanCategories.Foundation.ListFunctor
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.Foundation.Expressions

@[expose] public section

/-!
# The list monad on sets, and its cells (CC-CALC)

The list functor `L : Sets ⥤ Sets` (`LeanCategories.Foundation.listFunctor`, Mathlib's
`ofTypeMonad List`) is registered as a functor that is not structural: a list of elements of `X`
is not an element of `X`, so nothing is inherited along it. Its cells are registered from
`lean-categories`:

* `cell.sets.list.unit : 𝟭 ⟶ L`, `x ↦ [x]`;
* `cell.sets.list.join : L ⋙ L ⟶ L`, concatenation;
* `cell.sets.list.reverse : L ≅ L`, reversal, an invertible cell.
-/

open CategoryTheory

namespace CasCatalogue

namespace FunctorId
def setsList : FunctorId := ⟨"fun.sets.list"⟩
end FunctorId

namespace NaturalTransformationId
def listUnit : NaturalTransformationId := ⟨"cell.sets.list.unit"⟩
def listJoin : NaturalTransformationId := ⟨"cell.sets.list.join"⟩
def listReverse : NaturalTransformationId := ⟨"cell.sets.list.reverse"⟩
end NaturalTransformationId

namespace Foundation.Lists

universe u

def ListExpr : FunctorExpr Foundation.Sets Foundation.Sets := .atomic FunctorId.setsList

/-- `L : Sets ⥤ Sets`. -/
def listDeclaration : LeanCategories.Foundation.Mathlib.Sets.{u} ⥤
    LeanCategories.Foundation.Mathlib.Sets.{u} :=
  LeanCategories.Foundation.listFunctor

noncomputable def listRealization :
    FunctorRealization ListExpr LeanCategories.Foundation.Mathlib.Sets.{u}
      LeanCategories.Foundation.Mathlib.Sets.{u} listDeclaration :=
  { sourceRealization := Foundation.CatalogueRegistration.setsRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

/-- `η : 𝟭 ⟶ L`, on the registered functors. -/
def listUnitCell : 𝟭 LeanCategories.Foundation.Mathlib.Sets.{u} ⟶ listDeclaration.{u} :=
  LeanCategories.Foundation.listUnit

/-- `μ : L ⋙ L ⟶ L`, on the registered functors. -/
def listJoinCell : listDeclaration.{u} ⋙ listDeclaration.{u} ⟶ listDeclaration.{u} :=
  LeanCategories.Foundation.listJoin

/-- `ρ : L ≅ L`, on the registered functors. -/
def listReverseCell : listDeclaration.{u} ≅ listDeclaration.{u} :=
  LeanCategories.Foundation.listReverse

end Foundation.Lists

open Foundation.Lists

normalized_registry .functor
  { id := FunctorId.setsList
    source := Foundation.Sets
    target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.Lists.listDeclaration
    realization := `CasCatalogue.Foundation.Lists.listRealization
    expression := ListExpr }

normalized_registry .cell
  { id := NaturalTransformationId.listUnit, source := Foundation.Sets, target := Foundation.Sets
    left := #[], right := #[.functor FunctorId.setsList]
    declaration := `CasCatalogue.Foundation.Lists.listUnitCell }

normalized_registry .cell
  { id := NaturalTransformationId.listJoin, source := Foundation.Sets, target := Foundation.Sets
    left := #[.functor FunctorId.setsList, .functor FunctorId.setsList]
    right := #[.functor FunctorId.setsList]
    declaration := `CasCatalogue.Foundation.Lists.listJoinCell }

normalized_registry .cell
  { id := NaturalTransformationId.listReverse, source := Foundation.Sets
    target := Foundation.Sets
    left := #[.functor FunctorId.setsList], right := #[.functor FunctorId.setsList]
    declaration := `CasCatalogue.Foundation.Lists.listReverseCell, invertible := true }

end CasCatalogue
