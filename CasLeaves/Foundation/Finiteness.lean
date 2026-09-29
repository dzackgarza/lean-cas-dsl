/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
public import CasLeaves.Foundation.Cardinality
public import CasLeaves.Foundation.FiniteSets
public meta import CasCatalogue.Leaf
public meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness

@[expose] public section

/-!
# Deciding finiteness of presented sets; presented sets proved finite

* The decider of `clf.sets.finite` on presented sets reads the executable cardinality: finite
  cardinals are proved finite, `ℵ₀` is refuted, with evidence (`cardinalityOf_denote`).
* A presented set proved finite is re-typed by the core into finite sets as the same handle
  (`CasCatalogue.Refined`): this realizes `cat.finite_sets`, and its forgetful functor to sets is
  realized by forgetting the proof (`refinedInclusion`).
-/

open CategoryTheory
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.Cardinality
open CasCatalogue.Foundation.Finiteness

namespace CasCatalogue.Foundation.FinitenessActions

/-- Finiteness of the denotation of a presented set, decided from its cardinality. -/
def decideFinite (a : SetHandle) : Decision (Finite a.carrier) :=
  match h : cardinalityOf a with
  | .finite _ => .proved <| Cardinal.lt_aleph0_iff_finite.mp <| by
      rw [← cardinalityOf_denote, h]; exact Cardinal.nat_lt_aleph0 _
  | .aleph0 => .refuted fun hf => (Cardinal.lt_aleph0_iff_finite.mpr hf).ne <| by
      rw [← cardinalityOf_denote, h]; rfl

/-- The decider of `clf.sets.finite` on presented sets. -/
def finiteDecider : Decider LeanCategories.Foundation.Mathlib.finite setDenotation where
  decide a := (decideFinite a).map (finiteHolds_iff _).symm

/-- Finiteness, as a property of sets. -/
abbrev IsFinite : ObjectProperty LeanCategories.Foundation.Mathlib.Sets.{0} := fun X => Finite X

/-- Presented sets proved finite, as finite sets. -/
def finiteRefinedDenotation :
    Refined setDenotation IsFinite ⥤ LeanCategories.Foundation.Mathlib.FiniteSets.{0} :=
  refinedDenotation setDenotation IsFinite

def finiteRefinedDenotationFullyFaithful : finiteRefinedDenotation.FullyFaithful :=
  refinedDenotationFullyFaithful setDenotationFullyFaithful IsFinite

/-- The forgetful functor of finite sets, on presented sets proved finite: forget the proof. -/
def finiteRefinedForget :
    RealizedAction (forget FintypeCat.{0}) finiteRefinedDenotation setDenotation :=
  refinedInclusion setDenotation IsFinite

end CasCatalogue.Foundation.FinitenessActions

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .decider
  { id := ⟨"dec.sets.finite.presented"⟩, classifier := ClassifierId.setsFinite
    realization := `CasCatalogue.Foundation.FinitenessActions.finiteDecider },
  .realizer
  { id := ⟨"rz.finite_sets.refined"⟩, category := CategoryId.finiteSets, backend := "lean"
    denotation := `CasCatalogue.Foundation.FinitenessActions.finiteRefinedDenotation
    fullyFaithful :=
      some `CasCatalogue.Foundation.FinitenessActions.finiteRefinedDenotationFullyFaithful },
  .action
  { id := ⟨"act.finite_sets.forget.refined"⟩, edge := .classifierForget ClassifierId.setsFinite
    realization := `CasCatalogue.Foundation.FinitenessActions.finiteRefinedForget }] }

end CasCatalogue
