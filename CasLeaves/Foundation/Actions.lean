/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Foundation.Mathlib
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
  deriving DecidableEq, Repr, Hashable

/-- The set a handle presents. -/
abbrev SetHandle.carrier : SetHandle → Type
  | .intPow n => Fin n → ℤ
  | .finite n => Fin n
  | .zmod n => ZMod n
  | .zmodPow n k => Fin k → ZMod n

/-- Sets by presentation; a morphism is a Lean function between the presented sets. -/
abbrev setRealizer : Realizer := ⟨SetHandle, fun a b => a.carrier → b.carrier⟩

/-- A set handle denotes the set it presents, a function the function. -/
noncomputable def setDenotation : Denotation setRealizer LeanCategories.Foundation.Mathlib.Sets.{0} where
  obj a := a.carrier
  map f := TypeCat.ofHom f

end CasCatalogue.Foundation.Actions
