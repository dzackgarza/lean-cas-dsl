module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import Mathlib.Algebra.Ring.TransferInstance

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Engineering controls use existing mathematical objects and their full types.
They add no registry row, mathematical assertion, backend, or resource override. -/

run_elab do
  let state ← registryState
  let some regular := state.objects.find? (·.id.raw == "obj.modules.regular")
    | throwError "the existing regular module interface is absent"
  let standard ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let changed ← elabTermAndSynthesize (← `(@RingCat.of ℚ (Equiv.neg ℚ).ring)) none
  unless (← withTransparency .all <| isDefEq
      (← mkAppM ``RingCat.carrier #[standard]) (← mkAppM ``RingCat.carrier #[changed])) &&
      !(← withTransparency .all <| isDefEq standard changed) do
    throwError "the control must distinguish complete rings on one carrier"
  for selected in #[standard, changed] do
    let declared ← ObjectPresentation.applyParameters regular.declaration #[selected]
    let actual ← withTransparency .all <| whnf declared
    unless actual.getAppFn.constName? != some regular.declaration &&
        FunctorActionData.closedParameter actual do
      throwError "the reduced complete module did not exercise hidden bundled parameters"
    let candidates ← completeNamedObjectPresentations actual
    let #[(_, #[parameter])] := candidates.filter (·.1.id == regular.id)
      | throwError "the reduced complete module lost its selected ring parameter"
    unless FunctorActionData.closedParameter parameter &&
        (← withTransparency .all <| isDefEq (← inferType parameter) (← inferType selected) <&&>
          isDefEq parameter selected) do
      throwError "whole-object recovery replaced a selected ring by an equal-carrier structure"
    let reconstructed ← ObjectPresentation.applyParameters regular.declaration #[parameter]
    unless (← isTypeCorrect reconstructed) &&
        (← withTransparency .all <| isDefEq (← inferType reconstructed) (← inferType actual) <&&>
          isDefEq reconstructed actual) do
      throwError "the recovered parameters do not reconstruct the complete requested module"
    let trace ← Trace.new
    unless ← recordCompleteNamedObject trace actual do
      throwError "the unique full presentation could not be retained at its original value"
    let some (.object id #[retained]) ← trace.node? actual
      | throwError "the retained presentation changed its original complete trace role"
    unless id == regular.id &&
        (← withTransparency .all <| isDefEq retained selected) do
      throwError "the retained presentation lost its complete selected parameter"
  let openApplication ← instantiateFresh regular.declaration
  unless openApplication.hasMVar do throwError "the missing-parameter control is already closed"
  unless (← completeNamedObjectPresentations openApplication).isEmpty do
    throwError "whole-object recovery chose a missing parameter"

run_elab do
  let source ← elabTermAndSynthesize (← `(Nat × Bool)) none
  let trace ← Trace.new
  unless ← recordCompleteUniversalObject trace source do
    throwError "the exact product lacks its complete accepted universal presentation"
  let some (.limit id diagram none) ← trace.node? source
    | throwError "the public universal object lost its exact original trace key"
  unless id.raw == "lim.sets.product" && FunctorActionData.closedParameter diagram do
    throwError "the product presentation changed the complete selected diagram"
  let state ← registryState
  let some row := state.limits.find? (·.id == id)
    | throwError "the recovered product is not an accepted universal construction"
  let accepted ← Semantic.limitPresentation row diagram
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[accepted]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  unless ← withTransparency .all <| isDefEq apex source do
    throwError "the public universal presentation changed the complete original apex"
  let unknown ← mkFreshExprMVar (some (← inferType source))
  unless !(← recordCompleteUniversalObject trace unknown) do
    throwError "a universal presentation filled an unspecified original object"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the cached source control has no Sets category"
  let packet := Json.mkObj [("ctor",toJson "opaqueData"),
    ("args",Json.arr #[toJson "the actual original object"])]
  let actual : Wire := {
    form := .diagrams sets
    payload := .computed source (.owned "original-object-provider" 901 packet) }
  let harness ← Harness.empty
  harness.results.modify (·.insert source actual)
  let retained ← realize harness trace "the already computed full original object" source
  unless retained.fragment == actual.fragment && retained.value == source &&
      retained.owner? == actual.owner? do
    throwError "a public universal presentation replaced the actual computed object or supplier"
