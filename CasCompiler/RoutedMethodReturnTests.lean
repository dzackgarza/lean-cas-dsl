module

import CasCompiler.RoutedMethodFamily
import CasCompiler.SourceMethod
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public meta import Lean.Elab.Command
meta import CasCompiler.RoutedMethodFamily
meta import CasCompiler.SourceMethod
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels

open Lean Meta Elab Command CasCompiler CasCatalogue

private def mustReject (action : MetaM Unit) (detail : String) : MetaM Unit := do
  let rejected ← withoutModifyingState do
    try
      action
      pure false
    catch error =>
      unless ((← error.toMessageData.toString).splitOn detail).length > 1 do throw error
      pure true
  unless rejected do throwError "the returning-method negative control was admitted"

/- The original formed-module kernel supplies independent mathematical return
data at arbitrary complete R/W parameters. Check its own published formedKernel,
not a reconstructed expected value from the new reader. -/
run_cmd liftTermElabM do
  let state ← semanticState
  let #[method] := state.methods.filter (·.id.raw == "meth.kernel")
    | throwError "the original kernel method is absent"
  let query ← SourceRoutes.forMethod Modules.Bilinear.Valued.Kernels.ArrowsBilin "kernel"
  let some routes ← query.finiteRoutes
    | throwError "the original kernel route requires unavailable uniform data"
  let candidates := routes.filter (fun route =>
      !route.refs.isEmpty && route.target.syntacticEq method.owner)
  -- The original registry supplies two distinct first-hit carrier routes.
  -- Find the independently supplied restriction row, not the first route.
  unless candidates.size == 2 do
    throwError "the original kernel lost a full first-hit source route"
  let #[route] := candidates.filter (fun route => (methodReturnRows? state route).isSome)
    | throwError "the original kernel lost its independently supplied return route"
  let #[alternate] := candidates.filter (fun candidate => candidate.refs != route.refs)
    | throwError "the alternative whole transport was lost"
  let #[rows] ← methodReturnRows state route
    | throwError "the original kernel lost its independently selected return data"
  let family ← RoutedMethodFamily.forRouteWithReturns route method rows
  let compared ← RoutedMethodFamily.forComparedReturn alternate method route rows
  let some comparedReturn := compared.returns
    | throwError "the compared method lost its actual return plan"
  unless compared.route.refs == alternate.refs &&
      comparedReturn.route.refs == route.refs &&
      compared.returnIdentities == rows.map (·.id.raw) &&
      comparedReturn.agreement.isSome do
    throwError "the compared method replaced a selected forward or return route"
  let families ← RoutedMethodFamily.atSource route.source method.name
  unless families.size == candidates.size &&
      families.any (fun actual => actual.route.refs == alternate.refs &&
        actual.returns.any (fun returned => returned.agreement.isSome)) do
    throwError "ordinary method discovery erased an actual first-hit reading"
  let agreements ← family.agreementsWith families #[]
  unless !agreements.isEmpty do
    throwError "ordinary returning methods did not check their complete family agreement"
  for proof in agreements do checkWithKernel proof
  let some returned := family.returns
    | throwError "the inherited kernel discarded its actual return plan"
  unless family.resultCategory.syntacticEq Modules.Bilinear.Valued.Kernels.SubobjectsBilin &&
      family.returnIdentities == rows.map (·.id.raw) do
    throwError "the inherited kernel changed its full result category or selected lift"
  for expression in #[family.categoryFamily, family.functorFamily, family.family,
      returned.categoryFamily, returned.resultFamily] ++ family.actions ++ returned.evidences ++
      returned.actions ++ returned.agreement.toArray do
    if expression.hasFVar || expression.hasMVar || expression.hasLevelMVar then
      throwError "the inherited kernel did not close its complete native family"
  let levels := family.universeParams.map Level.param
  forallTelescopeReducing (← inferType family.categoryFamily) fun parameters _ => do
    let bundle := mkAppN family.categoryFamily parameters
    let sourceType ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    withLocalDeclD `originalArrow sourceType fun receiver => do
      let forward := family.mark (mkAppN family.family (parameters.push receiver))
      let (result, target) ← family.resultAt levels parameters receiver forward
      let otherForward := compared.mark (mkAppN
        (compared.family.instantiateLevelParams compared.universeParams levels)
        (parameters.push receiver))
      let (otherResult, otherTarget) ← compared.resultAt levels parameters receiver otherForward
      unless ← withTransparency .all <| isDefEq otherTarget target <&&> isDefEq otherResult result do
        throwError "the compared return changed the complete original result"
      unless ← isDefEq (← inferType result) (← mkAppM ``CategoryTheory.Bundled.α #[target]) do
        throwError "the inherited kernel changed its full result type"
      let arrow ← mkProjection result `obj
      let actual ← mkProjection arrow `left
      let originalMap ← mkProjection receiver `hom
      let expected ← mkAppM ``CasCatalogue.Modules.Bilinear.Valued.Kernels.formedKernel
        #[originalMap]
      unless ← withTransparency .all <| isDefEq actual expected do
        throwError "the inherited kernel changed the independently published formedKernel"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl actual) (← mkEq actual expected))
      unless result.containsFVar receiver.fvarId! do
        throwError "the inherited kernel replaced its original receiver"
  -- Calling the route-only API still cannot supply a missing return witness.
  mustReject (discard <| RoutedMethodFamily.forRoute route method)
    "source method lifting requires its actual selected return data"
  mustReject (discard <| RoutedMethodFamily.forRouteWithReturns route method #[])
    "source method lifting requires its actual selected return data"
  let wrong := rows.map fun row => { row with edge := .functor FunctorId.arrowsModulesKernel }
  mustReject (discard <| RoutedMethodFamily.forRouteWithReturns route method wrong)
    "the method return changed its actual selected lift declaration"
