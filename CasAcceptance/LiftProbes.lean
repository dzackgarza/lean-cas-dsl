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
  | .error (.missingReturn _ requirements) =>
      let some (_, steps) := requirements.find? (·.1.route.refs == #[arrowForget])
        | throwError "the missing return report discarded the direct carrier route"
      unless steps == #[arrowForget] do
        throwError "the missing direct return names the wrong steps"
      unless requirements.all (fun (_, missing) => !missing.isEmpty) do
        throwError "a complete return was reported as missing"
  | .ok r => throwError "the kernel resolved without a lift: {state.renderResolution r}"
  | .error e => throwError "unexpected: {e.render state}"
  -- Availability of return data cannot identify mathematically unrelated forward routes.
  let withoutComparison := { state with
    cells := state.cells.filter (·.id.raw != "cell.bilin_module.carrier_routes") }
  match withoutComparison.resolveMethod arrowsBilin "kernel" with
  | .error (.ambiguous _ _) => pure ()
  | _ => throwError "a unique return implementation replaced the required forward comparison"
  -- The unique complete return chain is independent of every registry row ordering.
  let reordered := { state with
    methods := state.methods.reverse, functors := state.functors.reverse
    classifiers := state.classifiers.reverse, constructors := state.constructors.reverse
    cells := state.cells.reverse, lifts := state.lifts.reverse }
  match reordered.resolveMethod arrowsBilin "kernel" with
  | .ok r =>
      unless r.route.refs == #[arrowForget] &&
          r.lifts.map (·.raw) == #["lift.bilin_module.restrict"] &&
          r.comparisonWitnesses.any (·.cell.raw == "cell.bilin_module.carrier_routes") do
        throwError "registry order changed the complete return or lost its comparison"
  | .error e => throwError e.render reordered
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
  -- Two separately registered complete lift chains are not identified by a comparison of
  -- forward functors, even when both lift rows satisfy the same accepted typed interface.
  let some original := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "the formed-module restriction is absent"
  let alternative := { original with id := ⟨"lift.probe.alternative_restriction"⟩ }
  if ← rejects (.lift alternative) then throwError "the independent typed lift was rejected"
  let competing := { state with lifts := state.lifts.push alternative }
  let reorderedCompeting := { competing with
    lifts := competing.lifts.reverse
    functors := competing.functors.reverse
    cells := competing.cells.reverse }
  for candidate in #[competing, reorderedCompeting] do
    match candidate.resolveMethod arrowsBilin "kernel" with
    | .error (.ambiguousReturn _ constructions) =>
        unless constructions.size == 2 &&
            constructions.all (·.route.refs == #[arrowForget]) &&
            constructions.any (·.lifts == #[original.id]) &&
            constructions.any (·.lifts == #[alternative.id]) do
          throwError "the complete-return ambiguity discarded a registered chain"
    | _ => throwError "competing complete returns were selected by registry order"

end CasCatalogue.LiftProbes
