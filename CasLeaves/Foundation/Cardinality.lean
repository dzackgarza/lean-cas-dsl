/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasCatalogue.Semantics.ConstructorRegistration
public import CasLeaves.Foundation.Actions
public import LeanCategories.Foundation.Cardinality
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.ZMod.Basic
public import CasCatalogue.Semantics.Foundation.Cardinality
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.ConstructorCatalogue
public meta import CasCatalogue.Semantics.Foundation.Cardinality

@[expose] public section

/-!
# Lean-native realizations for `CasCatalogue.Semantics.Foundation.Cardinality`

The leaf half of `CasCatalogue.Semantics.Foundation.Cardinality`: handles, their denotations and the actions of the registered functors on
them, contributed through `register_leaf`.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Foundation.Actions
open CasCatalogue.Catalogue.ConstructorRegistration

namespace CasCatalogue

namespace Foundation.Cardinality

universe u

/-! ### Lean-native realization -/

/-- The core of the realization of sets, `Core(SetHandles) ⥤ Core(Sets)` (`Functor.core`): a
realization of `Core(Sets)`, whose morphism handles are bijections of presented sets. -/
def coreSetDenotation : Core SetHandles ⥤ coreSetsCategory.{0} := setDenotation.core

/-- Executable cardinals: finite ones and `ℵ₀`. -/
inductive CardinalHandle
  | finite (n : ℕ)
  | aleph0
  deriving DecidableEq, Repr

/-- The cardinal a handle denotes. -/
def CardinalHandle.denote : CardinalHandle → Cardinal.{0}
  | .finite n => n
  | .aleph0 => Cardinal.aleph0

/-- Cardinal handles, `Discrete CardinalHandle`, denote cardinals in `Disc(Card)`. -/
noncomputable def cardinalDenotation : Discrete CardinalHandle ⥤ cardinalsCategory.{0} :=
  Discrete.functor fun a => Discrete.mk a.denote

/-- The cardinality of a presented set. -/
def cardinalityOf : SetHandle → CardinalHandle
  | .intPow 0 => .finite 1
  | .intPow (_ + 1) => .aleph0
  | .finite n => .finite n
  | .zmod 0 => .aleph0
  | .zmod (n + 1) => .finite (n + 1)
  | .zmodPow _ 0 => .finite 1
  | .zmodPow 0 (_ + 1) => .aleph0
  | .zmodPow (n + 1) k => .finite ((n + 1) ^ k)

theorem CardinalHandle.denote_injective : Function.Injective CardinalHandle.denote := by
  rintro (m | _) (n | _) h <;> simp only [CardinalHandle.denote] at h
  · exact congrArg _ (Nat.cast_injective h)
  · exact absurd h (Cardinal.nat_lt_aleph0 m).ne
  · exact absurd h.symm (Cardinal.nat_lt_aleph0 n).ne
  · rfl

theorem cardinalityOf_denote (a : SetHandle) :
    (cardinalityOf a).denote = Cardinal.mk a.carrier := by
  rcases a with ⟨_ | n⟩ | n | ⟨_ | n⟩ | ⟨n, _ | k⟩
  · simp [cardinalityOf, CardinalHandle.denote]
  · exact (Cardinal.mk_eq_aleph0 (Fin (n + 1) → ℤ)).symm
  · simp [cardinalityOf, CardinalHandle.denote]
  · exact (Cardinal.mk_eq_aleph0 ℤ).symm
  · simp [cardinalityOf, CardinalHandle.denote, SetHandle.carrier, ZMod.card]
  · simp [cardinalityOf, CardinalHandle.denote]
  · rcases n with _ | n
    · exact (Cardinal.mk_eq_aleph0 (Fin (k + 1) → ℤ)).symm
    · simp [cardinalityOf, CardinalHandle.denote, SetHandle.carrier, ZMod.card]

/-- The cardinality action on presented sets. -/
theorem cardinalityOf_iso {a b : SetHandles} (e : a ≅ b) : cardinalityOf a = cardinalityOf b :=
  CardinalHandle.denote_injective <| by
    rw [cardinalityOf_denote, cardinalityOf_denote]
    exact Cardinal.mk_congr ((setDenotation.mapIso e).toEquiv)

/-- The cardinality of a presented set, on the core: isomorphic sets have one cardinality. -/
def cardinalityHandles : Core SetHandles ⥤ Discrete CardinalHandle where
  obj a := ⟨cardinalityOf a.of⟩
  map f := eqToHom (congrArg Discrete.mk (cardinalityOf_iso f.iso))

noncomputable def cardinalityAction :
    RealizedAction setsCardinality.{0} coreSetDenotation cardinalDenotation where
  action := cardinalityHandles
  square := ⟨NatIso.ofComponents
    (fun a => eqToIso (congrArg Discrete.mk (cardinalityOf_denote a.of)))
    (fun _ => (Discrete.instSubsingletonDiscreteHom _ _).elim _ _)⟩

end Foundation.Cardinality

open Foundation.Cardinality

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.sets.cardinality.presented"⟩, edge := .functor FunctorId.setsCardinality
    realization := `CasCatalogue.Foundation.Cardinality.cardinalityAction },
  .realizer
  { id := ⟨"rz.sets.presented"⟩, category := ⟨"cat.sets"⟩, backend := "lean"
    denotation := `CasCatalogue.Foundation.Actions.setDenotation },
  .realizer
  { id := ⟨"rz.core_sets.presented"⟩, category := ⟨"cat.core_sets"⟩, backend := "lean"
    denotation := `CasCatalogue.Foundation.Cardinality.coreSetDenotation },
  .realizer
  { id := ⟨"rz.cardinals.handles"⟩, category := ⟨"cat.cardinals"⟩, backend := "lean"
    denotation := `CasCatalogue.Foundation.Cardinality.cardinalDenotation }] }

end CasCatalogue
