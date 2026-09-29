/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.ConstructorRegistration
public import LeanCategories.Foundation.Cardinality
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.ZMod.Basic
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.ConstructorCatalogue

@[expose] public section

/-!
# Cardinality: the one semantic cardinality method (#53 §11)

`card : Core(Sets) ⥤ Disc(Card)` (`LeanCategories.Foundation.cardinality`) is registered once, as
the functor `fun.sets.cardinality`, and presented as the iso-invariant method `cardinality` owned
by `Sets`. Every other category reaches it through structural functors; nothing else declares a
cardinality.

Its Lean-native action runs on presented sets: `ℤ⁰` has one element and `ℤⁿ⁺¹` is countably
infinite.
-/

open CategoryTheory
open LeanCategories
open CasCatalogue.Catalogue.ConstructorRegistration

namespace CasCatalogue

namespace CategoryId
def cardinals : CategoryId := ⟨"cat.cardinals"⟩
end CategoryId

namespace FunctorId
def setsCardinality : FunctorId := ⟨"fun.sets.cardinality"⟩
end FunctorId

namespace Foundation.Cardinality

universe u

def Cardinals : CategoryExpr := .atom CategoryId.cardinals
def SetsCardinalityExpr : FunctorExpr Constructed.CoreSets Cardinals :=
  .atomic FunctorId.setsCardinality

/-- Cardinal numbers, as a discrete category. -/
abbrev cardinalsCategory : ObjCat.{u + 1, u + 1} := Cat.of (Discrete Cardinal.{u})
noncomputable def cardinalsRealization : CategoryRealization Cardinals cardinalsCategory.{u} :=
  { familyFibre := none }

/-- `card : Core(Sets) ⥤ Disc(Card)`. -/
def setsCardinality : coreSetsCategory.{u} ⥤ cardinalsCategory.{u} :=
  LeanCategories.Foundation.cardinality
noncomputable def setsCardinalityRealization :
    FunctorRealization SetsCardinalityExpr coreSetsCategory.{u} cardinalsCategory.{u}
      setsCardinality :=
  { sourceRealization := coreSetsRealization, targetRealization := cardinalsRealization }

end Foundation.Cardinality

normalized_registry .category
  { id := CategoryId.cardinals,
    declaration := `CasCatalogue.Foundation.Cardinality.cardinalsCategory
    expression := Foundation.Cardinality.Cardinals
    realization := `CasCatalogue.Foundation.Cardinality.cardinalsRealization }
normalized_registry .functor
  { id := FunctorId.setsCardinality, source := Constructed.CoreSets
    target := Foundation.Cardinality.Cardinals
    declaration := `CasCatalogue.Foundation.Cardinality.setsCardinality
    realization := `CasCatalogue.Foundation.Cardinality.setsCardinalityRealization
    expression := Foundation.Cardinality.SetsCardinalityExpr }
normalized_registry .method
  { id := ⟨"meth.cardinality"⟩, name := "cardinality", owner := Foundation.Sets
    functor := FunctorId.setsCardinality, shape := .isoInvariant }

end CasCatalogue
