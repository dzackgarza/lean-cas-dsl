/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Foundation.Mathlib
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.ZMod.Defs
public meta import CasCatalogue.Leaf

@[expose] public section

/-!
# Lean-native realizations of sets

A set handle is an executable presentation of a set; a morphism handle between two set handles
is an ordinary Lean function between the sets they present. The denotation of a handle is the
set itself, an object of `Sets = Type`.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.Actions

/-- Executable presentations of sets. -/
inductive SetHandle
  /-- The set `ℤⁿ`, as functions `Fin n → ℤ`. -/
  | intPow (n : ℕ)
  /-- The finite set `{0, …, n-1}`, as `Fin n`. -/
  | finite (n : ℕ)
  /-- The set `ℤ/n`, as `ZMod n` (`ℤ` itself when `n = 0`). -/
  | zmod (n : ℕ)
  /-- The set `(ℤ/n)ᵏ`, as functions `Fin k → ZMod n`. -/
  | zmodPow (n k : ℕ)
  /-- The set of finite lists of elements of a presented set: the image under `L = List`. -/
  | list (a : SetHandle)
  deriving DecidableEq, Repr, Hashable

/-- The set a handle presents. -/
abbrev SetHandle.carrier : SetHandle → Type
  | .intPow n => Fin n → ℤ
  | .finite n => Fin n
  | .zmod n => ZMod n
  | .zmodPow n k => Fin k → ZMod n
  | .list a => List a.carrier

/-- Presented sets: the full subcategory of `Sets` on the presented carriers
(`InducedCategory`), so a morphism handle is a function between the presented sets. -/
abbrev SetHandles : Type := InducedCategory (Type) SetHandle.carrier

/-- Handles are compared as presentations (not as sets: that is a decision about denotations). -/
instance : DecidableEq SetHandles := inferInstanceAs (DecidableEq SetHandle)
instance : Repr SetHandles := inferInstanceAs (Repr SetHandle)

/-- A set handle denotes the set it presents, a function the function. -/
def setDenotation : SetHandles ⥤ LeanCategories.Foundation.Mathlib.Sets.{0} :=
  inducedFunctor SetHandle.carrier

/-- The elements of a presented set. -/
instance : ElementAction SetHandles := ⟨setDenotation⟩

/-- Induced realizations are fully faithful (`fullyFaithfulInducedFunctor`): cells are realized
on presented sets as preimages. -/
def setDenotationFullyFaithful : setDenotation.FullyFaithful :=
  fullyFaithfulInducedFunctor SetHandle.carrier

end CasCatalogue.Foundation.Actions
