module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import Mathlib.Algebra.Ring.TransferInstance

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Engineering use of the complete published module product interface.
No registry extension, leaf, fixed assertion or resource override is added. -/
run_elab do
  let state ← registryState
  let some regular := state.objects.find? (·.id.raw == "obj.modules.regular")
    | throwError "the public regular module interface is absent"
  let some product := state.limits.find? (·.id.raw == "lim.modules.product")
    | throwError "the exact new public module product interface is absent"
  let standard ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let changed ← elabTermAndSynthesize (← `(@RingCat.of ℚ (Equiv.neg ℚ).ring)) none
  for selected in #[standard, changed] do
    let component ← ObjectPresentation.applyParameters regular.declaration #[selected]
    let declared ← ObjectPresentation.applyParameters product.declaration
      #[selected, component, component]
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[declared]
    let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    let actual ← withTransparency .all <| whnf apex
    unless FunctorActionData.closedParameter actual && (← isTypeCorrect actual) do
      throwError "the reduced product is not a closed complete module object"
    let trace ← Trace.new
    unless ← recordCompleteUniversalObject trace actual do
      throwError "the reduced full module product lost its accepted universal presentation"
    let some (.limit id diagram none) ← trace.node? actual
      | throwError "the original full module product lost its exact trace key"
    unless id == product.id && FunctorActionData.closedParameter diagram do
      throwError "whole-object recovery changed the complete module product owner or diagram"
    let accepted ← Semantic.limitPresentation product diagram
    unless FunctorActionData.closedParameter accepted &&
        (← withTransparency .all <| isDefEq (← inferType accepted) (← inferType declared) <&&>
          isDefEq accepted declared) do
      throwError "the product recovery changed its complete selected ring or module parameters"
    let actualCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[accepted]
    let actualApex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[actualCone]
    unless ← Decide.kernelAccepts (← mkEq actualApex actual) (← mkEqRefl actualApex) do
      throwError "the reconstructed complete product differs from the original actual object"
