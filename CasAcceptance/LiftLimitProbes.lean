/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.Semantic
public meta import CasAcceptance.Standard
public meta import CasCatalogue.Semantic

@[expose] public section

/-!
# Acceptance for `cc-lift-general` (CC-LIFT, CC-UNIV)

A pullback of finite sets is computed downstairs, in `Sets` (the registered `lim.sets.pullback`),
and returned to finite sets along the registered creation lift `lift.finite_sets.pullbacks`
(Mathlib: the forgetful functor `FintypeCat ⥤ Sets` creates finite limits):

* `resolveLimit` finds no pullback registered in finite sets and names the lift it returns the
  pullback of sets along; in `Sets` itself it uses no lift;
* the semantic reading of a pullback in finite sets is the pullback of sets lifted along the
  creation lift (`liftedLimitCone`), a limit cone of the diagram of finite sets;
* lift rows whose evidence creates limits of another shape, or along another step, are rejected.

What the returned pullback's apex is, is a statement of the language, decided through the
admitted registrations.
-/

open CategoryTheory Limits Lean Meta Elab Term Command

namespace CasCatalogue.LiftLimitProbes

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
  -- The semantic reading of a pullback in finite sets: the pullback of sets, lifted.
  let some fin := state.objects.find? (·.id.raw == "obj.finite_sets.fin")
    | throwError "obj.finite_sets.fin is not registered"
  let some finiteSets := state.categories.find? (·.id == CategoryId.finiteSets)
    | throwError "cat.finite_sets is not registered"
  let two ← Semantic.object fin #[Syntax.mkNumLit "2"]
  let idTwo ← Semantic.hom (← `(CategoryTheory.CategoryStruct.id _)) two two
  let diagram ← instantiateMVars (← elabTermAndSynthesize
    (← `(CategoryTheory.Limits.cospan $(← exprToSyntax idTwo) $(← exprToSyntax idTwo))) none)
  let trace ← (Trace.new : IO _)
  let cone ← Semantic.limit false "pullback" diagram finiteSets.id.raw (some trace)
  let type ← whnfR (← inferType cone)
  unless type.isAppOf ``CategoryTheory.Limits.LimitCone do
    throwError "the returned pullback is not a limit cone"
  unless (cone.find? (·.isConstOf ``CasCatalogue.liftedLimitCone)).isSome do
    throwError "the pullback of finite sets is not returned along the lift"
  let some (.limit id _) ← (trace.node? cone : IO _)
    | throwError "the pullback is not recorded as a registered limit"
  unless id.raw == "lim.sets.pullback" do throwError "recorded as {id.raw}"

end CasCatalogue.LiftLimitProbes
