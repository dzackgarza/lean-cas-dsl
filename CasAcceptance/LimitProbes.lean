/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.Semantic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
public meta import CasAcceptance.Standard
public meta import CasCatalogue.Semantic

@[expose] public section

/-!
# Acceptance for `cc-limits` (CC-UNIV, CC-CALC)

* The registered presentations are the catalogue's: `lim.sets.pullback` is Mathlib's explicit
  pullback of sets and `lim.groups.kernel` its kernel of groups, each a family of `LimitCone`s in
  its category.
* The semantic reading forms a pullback in sets as the registered presentation at the diagram:
  at a diagram in standard form (`cospan f g`), the registered family at its data, with no
  identification (`limitConeOfIso`); a `LimitCone` of the diagram, whose apex, legs and mediator
  are Mathlib's; its cardinality (`3` for the pullback of
  `[0, 1, 1]` and `[1, 0]`) is a statement of the language, decided through the admitted
  registrations.
* The pushout in `Setsᵒᵖ` is the opposite of the pullback (`PullbackCone.isLimitEquivIsColimitOp`):
  Mathlib's duality, which the kernel never restates.
-/

open CategoryTheory Limits Lean Meta Elab Term Command

namespace CasCatalogue.LimitProbes

run_cmd liftTermElabM do
  let state ← registryState
  let expect (limit declaration : String) : MetaM Unit := do
    let some l := state.limits.find? (·.id.raw == limit) | throwError "{limit} is not registered"
    unless l.declaration.toString == declaration do throwError "{limit} names another limit"
  expect "lim.sets.pullback" "CasCatalogue.Limits.Registration.setsPullback"
  expect "lim.groups.kernel" "CasCatalogue.Limits.Registration.groupsKernel"
  -- The semantic reading of a pullback in sets: the registered presentation at the diagram.
  let some fin := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "obj.sets.fin is not registered"
  let two ← Semantic.object fin #[Syntax.mkNumLit "2"]
  let idTwo ← Semantic.hom (← `(CategoryTheory.CategoryStruct.id _)) two two
  let diagram ← instantiateMVars (← elabTermAndSynthesize
    (← `(CategoryTheory.Limits.cospan $(← exprToSyntax idTwo) $(← exprToSyntax idTwo))) none)
  let trace ← (Trace.new : IO _)
  let cone ← Semantic.limit false "pullback" diagram "cat.sets" (some trace)
  unless (← whnfR (← inferType cone)).isAppOf ``CategoryTheory.Limits.LimitCone do
    throwError "the pullback is not a limit cone"
  unless (cone.find? (·.isConstOf `CasCatalogue.Limits.Registration.setsPullback)).isSome do
    throwError "the pullback is not the registered presentation"
  if (cone.find? (·.isConstOf ``CasCatalogue.limitConeOfIso)).isSome then
    throwError "the pullback at a diagram in standard form is identified through an isomorphism"
  let some (.limit id _ lift) ← (trace.node? cone : IO _)
    | throwError "the pullback is not recorded as a registered limit"
  unless id.raw == "lim.sets.pullback" do throwError "recorded as {id.raw}"
  if let some lift := lift then throwError "the pullback in sets is recorded along {lift.raw}"
  -- No equalizer is registered in sets, nor returned to it along a lift: invalid.
  let stratum ← try
      discard <| Semantic.limit false "equalizer"
        (← instantiateMVars (← elabTermAndSynthesize
          (← `(CategoryTheory.Limits.parallelPair $(← exprToSyntax idTwo) $(← exprToSyntax idTwo)))
          none)) "cat.sets"
      pure none
    catch e => pure (Exception.stratum? e)
  unless stratum == some .invalid do
    throwError "an unregistered equalizer fails as {repr stratum}, not as invalid"

end CasCatalogue.LimitProbes
