/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Ring.TransferInstance

/-! Optional engineering controls for complete inherited component presentations.
The fixture is independently supplied; no mathematical assertion is admitted here. -/

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.bilinModule)
    | throwError "the component control has no existing formed-object category"
  let actual ← instantiateMVars (← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.zeroSource)) none)
  let original := Value.object actual category none none none
  for tracing in #[false, true] do
    let trace ← if tracing then some <$> Trace.new else pure none
    let context : Ctx := { trace := trace }
    let (carrier, route, applications) ← (carrierObjectWithAction original).run context
    unless route.size > 1 && route.size == applications.size do
      throwError "the component control has no complete intermediate carrier action"
    let some presented ← (refinedComponentPresentation? carrier).run context
      | throwError "the actual structural image lost its complete component presentation"
    let .object handle _ (some (base, _)) (some selected) _ := presented
      | throwError "the inherited presentation lost its actual coordinate or selected owner"
    unless base.components.isSome && selected.sameSource original &&
        (sourceParameterValues presented).any (·.sameSource carrier) do
      throwError "the component presentation replaced its original whole source"
    let originalHandle ← (semanticObject carrier).run context
    unless Expr.equal handle originalHandle do
      throwError "the component presentation replaced its original carrier expression"
    let retainedArguments := (sourceParameterValues presented).flatMap fun value =>
      match value with
      | .object _ _ _ _ (some (_, _, _, _, arguments)) => arguments
      | _ => #[]
    for (edge, application) in route.zip applications do
      unless retainedArguments.any (fun (retainedEdge, arguments) =>
          retainedEdge == edge && arguments == application.getAppArgs) do
        throwError "an original complete carrier application disappeared"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the action control has no existing module category"
  let actual ← instantiateMVars (← elabTermAndSynthesize
    (← `(ModuleCat.of ℚ (Fin 2 → ℚ))) none)
  let source := Value.object actual category none none none
  let context : Ctx := {}
  let (carrier, route, applications) ← (carrierObjectWithAction source).run context
  unless (← (directComponentPresentation? carrier (some (route, applications))).run context).isSome do
    throwError "the exact complete component action was not available"
  let standard ← instantiateMVars (← elabTermAndSynthesize (← `(RingCat.of ℚ)) none)
  let other ← instantiateMVars (← elabTermAndSynthesize
    (← `(@RingCat.of ℚ (Equiv.neg ℚ).ring)) none)
  unless !(← withTransparency .all <| isDefEq standard other) do
    throwError "the action control has no distinct complete scalar structures"
  let expected ← inferType standard
  let mut changed := applications
  let mut replaced := false
  for h : index in [:applications.size] do
    let application := applications[index]
    let arguments := application.getAppArgs
    for k : parameter in [:arguments.size] do
      let argument := arguments[parameter]
      let compatible ← withoutModifyingState do
        withTransparency .all <|
          isDefEq (← inferType argument) expected <&&> isDefEq argument standard
      if compatible then
        let candidate := mkAppN application.getAppFn (arguments.set! parameter other)
        unless ← isTypeCorrect candidate do
          throwError "the alternative complete action is not a typed fixture"
        changed := changed.set! index candidate
        replaced := true
        break
    if replaced then break
  unless replaced do throwError "the actual carrier action has no complete scalar parameter"
  if (← (directComponentPresentation? carrier (some (route, changed))).run context).isSome then
    throwError "equal route references erased a different full carrier application"
  -- A changed scalar action on the same function carrier is still a different
  -- whole module. It cannot acquire a canonical module-component presentation.
  let arguments := actual.getAppArgs
  let some dictionary := arguments.back?
    | throwError "the complete module fixture omitted its scalar action"
  withLocalDeclD `originalScalarAction (← inferType dictionary) fun supplied => do
    let altered := mkAppN actual.getAppFn (arguments.set! (arguments.size - 1) supplied)
    unless ← isTypeCorrect altered do
      throwError "the original opaque scalar action is not a typed fixture"
    let alteredSource := Value.object altered category none none none
    let alteredCarrier ← (carrierObject alteredSource).run context
    let before ← (semanticObject carrier).run context
    let after ← (semanticObject alteredCarrier).run context
    unless ← withTransparency .all <| isDefEq before after do
      throwError "the opaque-action control changed its underlying function carrier"
    if (← (directComponentPresentation? alteredCarrier).run context).isSome then
      throwError "the component lookup replaced an actual opaque scalar action"
