/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasCatalogue.Semantics.Limits.Lifts
public import CasLeaves.Foundation.Pullbacks
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Limits.Lifts

@[expose] public section

/-!
# Presented finite sets

A finite-set handle is a natural number `n`, presenting `Fin n` in `FintypeCat`; the realization is
induced, hence fully faithful. The pullback of presented finite sets is the leaf's enumeration of
Mathlib's explicit pullback of sets (`CasLeaves.Foundation.Pullbacks`), presented as a finite set:
the limit is computed in `Sets` and returned to finite sets along the registered creation lift
`lift.finite_sets.pullbacks`. The legs and mediators are the core's.
-/

open CategoryTheory Limits
open CasCatalogue.Foundation.Pullbacks

namespace CasCatalogue.Foundation.FiniteSets

/-- Presented finite sets: `n` presents `Fin n`. -/
abbrev FiniteHandles : Type := InducedCategory FintypeCat.{0} fun n : ℕ => FintypeCat.of (Fin n)

def finiteDenotation : FiniteHandles ⥤ LeanCategories.Foundation.Mathlib.FiniteSets.{0} :=
  inducedFunctor _

def finiteDenotationFullyFaithful : finiteDenotation.FullyFaithful :=
  fullyFaithfulInducedFunctor _

/-- The apex of the pullback of presented finite sets, computed in `Sets` and presented as a
finite set, with the identification of its underlying set with the pullback of sets. -/
def finitePullbackReturned (m n p : ℕ) (f : Fin m → Fin p) (g : Fin n → Fin p) :
    Σ a : FiniteHandles, (forget FintypeCat).obj (finiteDenotation.obj a) ≅
      (Limits.Registration.setsPullback (TypeCat.ofHom f) (TypeCat.ofHom g)).cone.pt :=
  ⟨(pullbackList f g).length, by exact (pullbackEquiv f g).toIso⟩

end CasCatalogue.Foundation.FiniteSets

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .realizer
  { id := ⟨"rz.finite_sets.presented"⟩, category := CategoryId.finiteSets, backend := "lean"
    denotation := `CasCatalogue.Foundation.FiniteSets.finiteDenotation
    fullyFaithful := some `CasCatalogue.Foundation.FiniteSets.finiteDenotationFullyFaithful },
  .limitRealization
  { id := ⟨"limr.finite_sets.pullback.returned"⟩, limit := ⟨"lim.sets.pullback"⟩
    realizer := ⟨"rz.finite_sets.presented"⟩
    realization := `CasCatalogue.Foundation.FiniteSets.finitePullbackReturned
    lift := some LiftId.finiteSetsPullbacks }] }

end CasCatalogue
