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
# Acceptance for `cc-lift-general` (CC-LIFT, CC-UNIV)

A pullback of finite sets is computed downstairs, in `Sets` (the registered `lim.sets.pullback`),
and returned to finite sets along the registered creation lift `lift.finite_sets.pullbacks`
(Mathlib: the forgetful functor `FintypeCat ⥤ Sets` creates finite limits):

* `resolveLimit` finds no pullback registered in finite sets and names the lift it returns the
  pullback of sets along; in `Sets` itself it uses no lift;
* the returned limit of `Fin 3 → Fin 2 ← Fin 2` in presented finite sets is the finite set of the
  three pairs, with its legs, lying over the legs of the pullback of sets; the mediator of a
  competing cone factors it and is unique;
* lift rows whose evidence creates limits of another shape, or along another step, are rejected, as
  is a returned limit realization on a realizer of another category.
-/

open CategoryTheory Limits Lean Meta Elab Term Command
open CasCatalogue.Foundation.FiniteSets

namespace CasCatalogue.LiftLimitProbes

def f : Fin 3 → Fin 2 := ![0, 1, 1]
def g : Fin 2 → Fin 2 := ![1, 0]

/-- A morphism of presented finite sets. -/
def finHom {a b : ℕ} (h : Fin a → Fin b) : @Quiver.Hom FiniteHandles _ a b :=
  InducedCategory.homMk (FintypeCat.homMk h)

abbrev D : WalkingCospan ⥤ FiniteHandles := cospan (finHom f) (finHom g)

/-- The pullback of the underlying sets: the registered presentation in `Sets`. -/
noncomputable def L : LimitCone ((D ⋙ finiteDenotation) ⋙ forget FintypeCat) :=
  limitConeOfIso (diagramIsoCospan _) (Limits.Registration.setsPullback _ _)

def apex := finitePullbackReturned 3 2 2 f g

/-- The pullback in finite sets, returned along the forgetful functor. -/
noncomputable def P : LimitCone D :=
  realizedReturnedLimitCone finiteDenotationFullyFaithful (ObjectProperty.fullyFaithfulι _) L
    apex.1 apex.2

#guard (show ℕ from exec% P.cone.pt) == 3
#guard (List.finRange 3).map (fun i => (show Fin 3 from
  (exec% (P.cone.π.app WalkingCospan.left)).hom.hom i)) == [0, 1, 2]
#guard (List.finRange 3).map (fun i => (show Fin 2 from
  (exec% (P.cone.π.app WalkingCospan.right)).hom.hom i)) == [1, 0, 0]

/-- Its legs lie over the legs of the pullback of sets. -/
theorem leg_over (j : WalkingCospan) :
    (forget FintypeCat).map (finiteDenotation.map (P.cone.π.app j)) =
      apex.2.hom ≫ L.cone.π.app j :=
  realizedReturnedLimitCone_leg _ _ L apex.1 apex.2 j

/-- A competing cone from the one-point set, sent to `(2, 0)`. -/
def s : PullbackCone (finHom f) (finHom g) :=
  PullbackCone.mk (finHom (a := 1) ![2]) (finHom (a := 1) ![0]) <| by
    apply InducedCategory.hom_ext
    apply FintypeCat.hom_ext
    intro x; fin_cases x; rfl

noncomputable def mediator : @Quiver.Hom FiniteHandles _ (1 : ℕ) P.cone.pt := P.isLimit.lift s

#guard (show Fin 3 from (exec% mediator).hom.hom 0) == 2

theorem mediator_unique (m : @Quiver.Hom FiniteHandles _ (1 : ℕ) P.cone.pt)
    (h₁ : m ≫ P.cone.π.app WalkingCospan.left = s.fst)
    (h₂ : m ≫ P.cone.π.app WalkingCospan.right = s.snd) : m = mediator :=
  PullbackCone.IsLimit.hom_ext (t := (P.cone : PullbackCone _ _)) P.isLimit
    (h₁.trans (P.isLimit.fac s WalkingCospan.left).symm)
    (h₂.trans (P.isLimit.fac s WalkingCospan.right).symm)

/-! ### The registry names the lift -/

run_cmd liftTermElabM do
  let state ← registryState
  match state.resolveLimit CategoryId.finiteSets "pullback" with
  | .ok r =>
      unless r == { limit := ⟨"lim.sets.pullback"⟩, lift := some LiftId.finiteSetsPullbacks } do
        throwError "pullbacks of finite sets resolved to {repr r}"
  | .error e => throwError e
  match state.resolveLimit CategoryId.sets "pullback" with
  | .ok r => unless r == { limit := ⟨"lim.sets.pullback"⟩ } do
      throwError "pullbacks of sets resolved to {repr r}"
  | .error e => throwError e
  -- A shape with no registered limit and no lift is reported, not guessed.
  if let .ok r := state.resolveLimit CategoryId.finiteSets "kernel" then
    throwError "kernels of finite sets resolved to {repr r}"
  let some lift := state.lifts.find? (·.id == LiftId.finiteSetsPullbacks)
    | throwError "lift.finite_sets.pullbacks is not registered"
  let rejects (entry : RegistryEntry) : MetaM Bool := do
    try validateRegistryEntryDeclaration entry; pure false catch _ => pure true
  unless ← rejects
      (.lift { lift with id := ⟨"lift.probe.shape"⟩, kind := .createsLimits "kernel" }) do
    throwError "a creation of pullbacks was accepted as a creation of kernels"
  unless ← rejects
      (.lift { lift with id := ⟨"lift.probe.step"⟩, edge := .functor FunctorId.setsList }) do
    throwError "a creation along the forgetful functor was accepted along another step"
  let some returned := state.limitRealizations.find? (·.lift == some LiftId.finiteSetsPullbacks)
    | throwError "no limit realization is returned along the lift"
  unless ← rejects (.limitRealization
      { returned with id := ⟨"limr.probe.realizer"⟩, realizer := ⟨"rz.sets.presented"⟩ }) do
    throwError "a returned limit was accepted on a realizer of the lift's target"

end CasCatalogue.LiftLimitProbes
