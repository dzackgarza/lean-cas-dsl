/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Foundation.Actions
public import CasLeaves.Foundation.Cardinality
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs
public meta import CasCatalogue.Leaf

@[expose] public section

/-!
# Equality of maps of presented sets

Two maps of presented sets are equal iff they agree at every element (`funext`). The decision
enumerates the domain when it is presented finitely (`SetHandle.fintype?`) and compares values
in the codomain (`SetHandle.decEq`); on a domain it does not enumerate it is undecided, never
refuted.
-/

open CategoryTheory
open CasCatalogue.Foundation.Actions

namespace CasCatalogue.Foundation.Equality

/-- Equality of elements of a presented set is decidable. -/
def decEq : (a : SetHandle) → DecidableEq a.carrier
  | .intPow n => inferInstanceAs (DecidableEq (Fin n → ℤ))
  | .finite n => inferInstanceAs (DecidableEq (Fin n))
  | .zmod n => inferInstanceAs (DecidableEq (ZMod n))
  | .zmodPow n k => inferInstanceAs (DecidableEq (Fin k → ZMod n))
  | .list a => haveI := decEq a; inferInstanceAs (DecidableEq (List a.carrier))
  | .prod a b => haveI := decEq a; haveI := decEq b;
      inferInstanceAs (DecidableEq (a.carrier × b.carrier))

/-- An enumeration of a presented set, when its presentation is finite. -/
def fintype? : (a : SetHandle) → Option (Fintype a.carrier)
  | .finite n => some (inferInstanceAs (Fintype (Fin n)))
  | .zmod (n + 1) => some (inferInstanceAs (Fintype (Fin (n + 1))))
  | .zmodPow (n + 1) k => some (inferInstanceAs (Fintype (Fin k → Fin (n + 1))))
  | .prod a b => match fintype? a, fintype? b with
    | some _, some _ => some inferInstance
    | _, _ => none
  | _ => none

/-- Maps of presented sets are equal iff they agree pointwise. -/
theorem map_eq_iff {a b : SetHandles} (f g : a ⟶ b) :
    (∀ x, f.hom x = g.hom x) ↔ setDenotation.map f = setDenotation.map g :=
  ⟨fun h => TypeCat.Hom.ext (TypeCat.Fun.ext (funext h)), fun h x =>
    have h' : f.hom = g.hom := h
    ConcreteCategory.congr_hom h' x⟩

/-- The equality of `Sets`, decided on presented sets. -/
def setEquality : HomEquality setDenotation where
  decide {a b} f g :=
    match fintype? a with
    | some _ =>
        letI := decEq b
        (Decision.ofDecidable (∀ x, f.hom x = g.hom x)).map (map_eq_iff f g)
    | none => .undecided

end CasCatalogue.Foundation.Equality

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .equality
  { id := ⟨"eq.sets.presented"⟩, realizer := ⟨"rz.sets.presented"⟩
    realization := `CasCatalogue.Foundation.Equality.setEquality }] }

end CasCatalogue
