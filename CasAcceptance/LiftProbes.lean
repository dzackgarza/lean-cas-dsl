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
# Acceptance for `cc-lift` (CC-LIFT)

`kernel` is owned by modules and returns a subobject of the underlying module. On a morphism of
formed modules it resolves along `Arr(BilinModule) → Arr(Mod_R)` and is lifted back by the
registered restriction of forms (`lift.bilin_module.restrict`): the result is a formed submodule
(`formedKernel`, whose form is the restriction and whose elements `f` kills). With that row
removed, the same call reports the missing lift instead of returning the module kernel. A lift row
is accepted only for the route step whose functor is its evidence's functor on arrows.
-/

open Lean Meta Elab Term Command

namespace CasCatalogue.LiftProbes

#resolve kernel in "cat.arrows_bilin_module"
#resolve kernel in "cat.arrows_modules_r"

run_cmd liftTermElabM do
  let state ← registryState
  let category (id : String) : TermElabM CategoryExpr := do
    let some entry := state.categories.find? (·.id.raw == id)
      | throwError "{id} is not registered"
    pure entry.expression
  let arrowsBilin ← category "cat.arrows_bilin_module"
  let arrowsModules ← category "cat.arrows_modules_r"
  -- `Arr(U)` for the forgetful functor `U` of formed modules: a derived edge.
  let arrowForget : EdgeRef := .constructMap ConstructorId.arrow (.functor FunctorId.bilinModuleForget)
  -- On formed modules the kernel is lifted back by the registered restriction of forms.
  match state.resolveMethod arrowsBilin "kernel" with
  | .ok r =>
      unless r.route.refs == #[arrowForget] &&
          r.lifts.map (·.raw) == #["lift.bilin_module.restrict"] do
        throwError "unexpected: {state.renderResolution r}"
  | .error e => throwError e.render state
  -- On modules no lift is needed.
  match state.resolveMethod arrowsModules "kernel" with
  | .ok r => unless r.lifts.isEmpty do throwError "a lift was used on the owner itself"
  | .error e => throwError e.render state
  -- Without the lift, the call reports it, and does not return the module kernel.
  let unlifted := { state with lifts := #[] }
  match unlifted.resolveMethod arrowsBilin "kernel" with
  | .error (.missingLift _ _ step) =>
      unless step == arrowForget do
        throwError "the missing lift names the wrong step: {step.label}"
  | .ok r => throwError "the kernel resolved without a lift: {state.renderResolution r}"
  | .error e => throwError "unexpected: {e.render state}"
  -- A lift row is accepted only for the step it lifts along.
  let rejects (entry : RegistryEntry) : MetaM Bool := do
    try validateRegistryEntryDeclaration entry; pure false
    catch _ => pure true
  let lift (id : String) (edge : EdgeRef) (evidence : Name) : RegistryEntry :=
    .lift
      { id := ⟨id⟩
        edge := edge
        evidence := evidence }
  unless ← rejects (lift "lift.probe.wrong_step" (.functor FunctorId.arrowsModulesKernel)
      `CasCatalogue.Modules.Bilinear.Valued.Kernels.forgetMonoLift) do
    throwError "a lift was accepted for a step it does not lift along"
  unless ← rejects (lift "lift.probe.not_a_lift" arrowForget
      `CasCatalogue.Modules.Bilinear.Valued.Kernels.kernelDeclaration) do
    throwError "a non-lift was accepted as a lift"
  for lift in state.lifts do
    if ← rejects (.lift lift) then throwError "registered lift {lift.id.raw} fails re-validation"

end CasCatalogue.LiftProbes
