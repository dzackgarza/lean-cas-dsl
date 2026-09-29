/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import CasLeaves.Foundation.Actions
public import LeanCategories.Foundation.Cardinality
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.ZMod.Basic
public import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public meta import CasCatalogue.Leaf
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality

@[expose] public section

/-!
# Lean-native realizations for `LeanCategories.Catalogue.Semantics.Foundation.Cardinality`

The leaf half of `LeanCategories.Catalogue.Semantics.Foundation.Cardinality`: handles, their denotations and the actions of the registered functors on
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
  | .list a => match cardinalityOf a with
    | .finite 0 => .finite 1
    | _ => .aleph0
  | .prod a b => match cardinalityOf a, cardinalityOf b with
    | .finite m, .finite n => .finite (m * n)
    | .finite 0, .aleph0 => .finite 0
    | .aleph0, .finite 0 => .finite 0
    | _, _ => .aleph0

/-- Every presented set is countable. -/
theorem _root_.CasCatalogue.Foundation.Actions.SetHandle.countable :
    ∀ a : SetHandle, Countable a.carrier
  | .intPow _ | .finite _ => inferInstance
  | .zmod 0 => inferInstanceAs (Countable ℤ)
  | .zmod (_ + 1) => inferInstance
  | .zmodPow 0 _ => inferInstanceAs (Countable (Fin _ → ℤ))
  | .zmodPow (_ + 1) _ => inferInstance
  | .list a => haveI := a.countable; inferInstanceAs (Countable (List a.carrier))
  | .prod a b =>
      haveI := a.countable; haveI := b.countable; inferInstanceAs (Countable (a.carrier × b.carrier))

theorem CardinalHandle.denote_injective : Function.Injective CardinalHandle.denote := by
  rintro (m | _) (n | _) h <;> simp only [CardinalHandle.denote] at h
  · exact congrArg _ (Nat.cast_injective h)
  · exact absurd h (Cardinal.natCast_lt_aleph0 (n := m)).ne
  · exact absurd h.symm (Cardinal.natCast_lt_aleph0 (n := n)).ne
  · rfl

theorem cardinalityOf_denote : ∀ a : SetHandle,
    (cardinalityOf a).denote = Cardinal.mk a.carrier
  | .intPow 0 => by simp [cardinalityOf, CardinalHandle.denote]
  | .intPow (n + 1) => (Cardinal.mk_eq_aleph0 (Fin (n + 1) → ℤ)).symm
  | .finite n => by simp [cardinalityOf, CardinalHandle.denote]
  | .zmod 0 => (Cardinal.mk_eq_aleph0 ℤ).symm
  | .zmod (n + 1) => by simp [cardinalityOf, CardinalHandle.denote, SetHandle.carrier, ZMod.card]
  | .zmodPow n 0 => by simp [cardinalityOf, CardinalHandle.denote]
  | .zmodPow 0 (k + 1) => (Cardinal.mk_eq_aleph0 (Fin (k + 1) → ℤ)).symm
  | .zmodPow (n + 1) (k + 1) => by
      simp [cardinalityOf, CardinalHandle.denote, SetHandle.carrier, ZMod.card]
  | .list a => by
      haveI := a.countable
      have ha := cardinalityOf_denote a
      rcases h : cardinalityOf a with (_ | n) | _
      · -- the empty set: its only list is `[]`
        rw [h] at ha
        haveI : IsEmpty a.carrier := Cardinal.mk_eq_zero_iff.mp (by simpa [CardinalHandle.denote]
          using ha.symm)
        haveI : Unique (List a.carrier) := ⟨⟨[]⟩, fun l => by cases l with
          | nil => rfl
          | cons x _ => exact isEmptyElim x⟩
        have : Cardinal.mk (List a.carrier) = 1 := Cardinal.mk_eq_one _
        simp [cardinalityOf, h, CardinalHandle.denote, SetHandle.carrier, this]
      · rw [h] at ha
        haveI : Nonempty a.carrier := Cardinal.mk_ne_zero_iff.mp (by
          rw [← ha]; simp [CardinalHandle.denote])
        simp [cardinalityOf, h, CardinalHandle.denote, SetHandle.carrier,
          Cardinal.mk_list_eq_aleph0]
      · rw [h] at ha
        haveI : Nonempty a.carrier := Cardinal.mk_ne_zero_iff.mp (by
          rw [← ha]; exact Cardinal.aleph0_ne_zero)
        simp [cardinalityOf, h, CardinalHandle.denote, SetHandle.carrier,
          Cardinal.mk_list_eq_aleph0]
  | .prod a b => by
      have hp : Cardinal.mk (SetHandle.prod a b).carrier =
          Cardinal.mk a.carrier * Cardinal.mk b.carrier := by
        simp [SetHandle.carrier, Cardinal.mk_prod]
      rw [hp, ← cardinalityOf_denote a, ← cardinalityOf_denote b]
      simp only [cardinalityOf]
      rcases cardinalityOf a with (_ | m) | _ <;> rcases cardinalityOf b with (_ | n) | _ <;>
        simp [CardinalHandle.denote]
      all_goals first
        | rw [← Nat.cast_succ, Cardinal.nat_mul_aleph0 (Nat.succ_ne_zero _)]
        | rw [← Nat.cast_succ, Cardinal.aleph0_mul_nat (Nat.succ_ne_zero _)]

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

/-- A cardinal handle, read as the literal it denotes. -/
def observeCardinal (h : Discrete CardinalHandle) :
    { l : CardinalLiteral // cardinalDenotation.obj h = CardinalLiteral.denote l } :=
  match h with
  | ⟨.finite n⟩ => ⟨.finite n, rfl⟩
  | ⟨.aleph0⟩ => ⟨.aleph0, rfl⟩

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
    denotation := `CasCatalogue.Foundation.Actions.setDenotation
    fullyFaithful := some `CasCatalogue.Foundation.Actions.setDenotationFullyFaithful },
  .realizer
  { id := ⟨"rz.core_sets.presented"⟩, category := ⟨"cat.core_sets"⟩, backend := "lean"
    denotation := `CasCatalogue.Foundation.Cardinality.coreSetDenotation },
  .realizer
  { id := ⟨"rz.cardinals.handles"⟩, category := ⟨"cat.cardinals"⟩, backend := "lean"
    denotation := `CasCatalogue.Foundation.Cardinality.cardinalDenotation },
  .observation
  { id := ⟨"obs.cardinals.handles"⟩, realizer := ⟨"rz.cardinals.handles"⟩
    literal := ⟨"lit.cardinals"⟩
    observe := `CasCatalogue.Foundation.Cardinality.observeCardinal }] }

end CasCatalogue
