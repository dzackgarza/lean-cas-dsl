/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-refine` (CC-PROP, CC-DECIDE)

* `is_finite` of the presented set `Fin 2 × ℤ/3` is proved by the registered decider; the proof
  re-types it into finite sets as the same handle (`refine`), and the methods of finite sets
  resolve on it (`cardinality`, along the forgetful functor of finite sets), with the value they
  have on the original set.
* `is_finite` of `ℤ` is refuted, and an undecided decision places nothing: neither is re-typed.
* A refined handle follows containment of refinements (`Finite ≤ Countable`, `ιOfLE`).
* The equality of `Sets` on presented sets (`eq.sets.presented`): two differently constructed equal
  maps (`rev ∘ rev` and the identity of `Fin 4`) are decided equal, distinct ones unequal, and on a
  domain that is not enumerated (`ℤ`) the decision is undecided, never `false`.
-/

open CategoryTheory Lean Meta Elab Command
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.Cardinality
open CasCatalogue.Foundation.FinitenessActions CasCatalogue.Foundation.Finiteness

namespace CasCatalogue.RefineProbes

/-- `Fin 2 × ℤ/3`, presented. -/
def a : SetHandles := SetHandle.prod (.finite 2) (.zmod 3)

/-- `ℤ`, presented. -/
def z : SetHandles := SetHandle.zmod 0

#guard (ask% is_finite (a) in "cat.sets").answer == some true
#guard (ask% is_finite (z) in "cat.sets").answer == some false

/-- The registered decision, as a decision of finiteness. -/
def decideIsFinite (x : SetHandles) : Decision (IsFinite (setDenotation.obj x)) :=
  (finiteDecider.decide x).map (finiteHolds_iff _)

/-- `a`, re-typed after its proved decision. -/
def r? : Option (Refined setDenotation IsFinite) := refine a (decideIsFinite a)

#guard r?.isSome
#guard (refine% (a) in "cat.sets" to "cat.finite_sets").isSome
#guard (refine% (z) in "cat.sets" to "cat.finite_sets").isNone
#guard (refine z (decideIsFinite z)).isNone
#guard (refine (d := setDenotation) (P := IsFinite) a .undecided).isNone

def r : Refined setDenotation IsFinite := r?.get (by decide)

/-- The re-typed handle is the same handle. -/
theorem r_same : (finiteRefinedForget).obj r = a := refine_eq_some (Option.some_get _).symm

/- The methods of finite sets resolve on it, with their value on the original set. -/
#guard method% cardinality (r) in "cat.finite_sets" == ⟨CardinalHandle.finite 6⟩
#guard method% cardinality (r) in "cat.finite_sets" == method% cardinality (a) in "cat.sets"

/-- Containment `Finite ≤ Countable`: the refined handle is a countable one, over `ιOfLE`. -/
theorem finite_le_countable :
    IsFinite ≤ (fun X : LeanCategories.Foundation.Mathlib.Sets.{0} => Countable X) :=
  fun _ h => @Finite.to_countable _ h

#guard (refineLE finite_le_countable r).obj == a

/-! ### Equality -/

def finHom {m n : ℕ} (h : Fin m → Fin n) :
    @Quiver.Hom SetHandles _ (SetHandle.finite m) (SetHandle.finite n) :=
  InducedCategory.homMk (TypeCat.ofHom h)

def fin4 : SetHandles := SetHandle.finite 4

/-- `rev ∘ rev` and the identity of `Fin 4`: equal, differently constructed. -/
def revRev : @Quiver.Hom SetHandles _ (SetHandle.finite 4) (SetHandle.finite 4) :=
  finHom Fin.rev ≫ finHom Fin.rev

#guard (eq% (revRev) (𝟙 fin4) in "cat.sets").answer == some true
#guard (eq% (finHom (Fin.rev : Fin 4 → Fin 4)) (𝟙 fin4) in "cat.sets").answer ==
  some false

/-- `v ↦ -(-v)` and the identity of `ℤ`: equal, on a domain that is not enumerated. -/
def negNeg : @Quiver.Hom SetHandles _ z z :=
  InducedCategory.homMk (TypeCat.ofHom fun v : ℤ => -(-v))

#guard (eq% (negNeg) (𝟙 z) in "cat.sets").answer == none

/-- Equal morphisms are never decided unequal. -/
theorem never_false :
    (Foundation.Equality.setEquality.decide negNeg (𝟙 z)).answer ≠ some false :=
  Decision.answer_ne_false_of <|
    (Foundation.Equality.map_eq_iff _ _).mp fun v => neg_neg (G := ℤ) v

end CasCatalogue.RefineProbes
