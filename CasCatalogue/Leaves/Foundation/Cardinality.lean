/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.ConstructorRegistration
public import CasCatalogue.Leaves.Foundation.Actions
public import LeanCategories.Foundation.Cardinality
public import Mathlib.SetTheory.Cardinal.Arithmetic
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.ConstructorCatalogue

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
open LeanCategories CasCatalogue.Foundation.Actions
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

/-! ### Lean-native realization -/

/-- Presented sets with their identity isomorphisms: a realizer of `Core(Sets)`. -/
abbrev coreSetRealizer : Realizer := ⟨SetHandle, fun a b => PLift (a = b)⟩

/-- A presented set, as an object of `Core(Sets)`. -/
noncomputable def coreSetDenotation : Denotation coreSetRealizer coreSetsCategory.{0} where
  obj a := ⟨setDenotation.obj a⟩
  map h := eqToHom (by cases h.down; rfl)

/-- Executable cardinals: finite ones and `ℵ₀`. -/
inductive CardinalHandle
  | finite (n : ℕ)
  | aleph0
  deriving DecidableEq, Repr

/-- Cardinal handles, with equalities as morphisms: a realizer of `Disc(Card)`. -/
abbrev cardinalRealizer : Realizer := ⟨CardinalHandle, fun a b => PLift (a = b)⟩

/-- The cardinal a handle denotes. -/
def CardinalHandle.denote : CardinalHandle → Cardinal.{0}
  | .finite n => n
  | .aleph0 => Cardinal.aleph0

noncomputable def cardinalDenotation : Denotation cardinalRealizer cardinalsCategory.{0} where
  obj a := Discrete.mk a.denote
  map h := eqToHom (by cases h.down; rfl)

/-- The cardinality of a presented set. -/
def cardinalityOf : SetHandle → CardinalHandle
  | .intPow 0 => .finite 1
  | .intPow (_ + 1) => .aleph0

theorem cardinalityOf_denote (a : SetHandle) :
    (cardinalityOf a).denote = Cardinal.mk a.carrier := by
  rcases a with ⟨_ | n⟩
  · simp [cardinalityOf, CardinalHandle.denote]
  · exact (Cardinal.mk_eq_aleph0 (Fin (n + 1) → ℤ)).symm

/-- The cardinality action on presented sets. -/
def cardinalityAction :
    RealizedAction setsCardinality.{0} coreSetDenotation cardinalDenotation where
  action := { obj := cardinalityOf, map := fun h => ⟨by cases h.down; rfl⟩ }
  realizes :=
    { obj := fun a => congrArg Discrete.mk (cardinalityOf_denote a)
      map := fun _ => ULift.ext _ _ (Subsingleton.elim _ _) }

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
normalized_registry .action
  { id := ⟨"act.sets.cardinality.presented"⟩, edge := .functor FunctorId.setsCardinality
    realization := `CasCatalogue.Foundation.Cardinality.cardinalityAction }

end CasCatalogue
