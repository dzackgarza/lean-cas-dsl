/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

/- These engineering controls use existing registered maps and Lean's ordinary
function/parameter rules. They add no mathematical declaration or registry row. -/

private def firstRoute (state : RegistryState) (source : CategoryExpr)
    (entry : OperationEntry) : TermElabM (Array EdgeRef) := do
  let some owner := state.categories.find? (·.id == entry.category)
    | throwError "the universal-context control has no accepted owner"
  let routes ← (routesBetween state source owner.expression).run {}
  let #[route] := routes.filter (state.toSemanticState.isFirstOperationBindingRoute entry.name)
    | throwError "the universal-context control has no unique first-binding route"
  return route.refs

/- An arbitrary full functor is the independent precomposition parameter. Its
whole action and the source object must survive abstraction before equality. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some source := state.categories.find? (·.name == "CommutativeRings")
    | throwError "the precomposition control has no complete source category"
  let some left := state.operations.find? fun row =>
      row.category == CategoryId.rings && row.name == "·"
    | throwError "the precomposition control has no ring operation"
  let some right := state.operations.find? fun row =>
      row.category == CategoryId.monoids && row.name == "·"
    | throwError "the precomposition control has no monoid operation"
  OperationAgreement.withSourceTemplate state source.expression fun parameters context => do
    let carrier ← CategoryContext.carrier context
    let dictionary ← CategoryContext.dictionary context
    let functorType ← mkAppOptM ``CategoryTheory.Functor
      #[some carrier, some dictionary, some carrier, some dictionary]
    let action ← mkFreshExprMVar (some functorType) (userName := `independentAction)
    let receiver ← mkFreshExprMVar (some carrier) (userName := `independentSource)
    let image ← Semantic.objOf action receiver
    let cache ← IO.mkRef (#[] : Array OperationAgreement.RouteTemplate)
    let (leftMap, _) ← OperationAgreement.routedTemplate state left context image
      (← firstRoute state source.expression left) #[] cache
    let (rightMap, _) ← OperationAgreement.routedTemplate state right context image
      (← firstRoute state source.expression right) #[] cache
    let families ← OperationAgreement.abstractTemplates #[action, receiver, leftMap, rightMap]
    let families ← families.mapM fun family => do mkLambdaFVars parameters family
    let families ← OperationAgreement.abstractTemplates families true
    let some leftFamily := families[2]? | unreachable!
    let some rightFamily := families[3]? | unreachable!
    unless leftFamily.getNumHeadLambdas == parameters.size + 2 &&
        OperationAgreement.closed leftFamily && OperationAgreement.closed rightFamily do
      throwError "the universal precomposition lost its independent action or source"
    unless ← OperationAgreement.kernelAcceptsFamily (← mkEq leftFamily rightFamily)
        (← mkEqRefl leftFamily) do
      throwError "the accepted whole-map equation did not survive arbitrary complete precomposition"

/- Equal later numeral values cannot turn two independent rigid parameters into
one universal equation. These are whole power maps, with no operands supplied. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some source := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the independent-parameter control has no complete ring category"
  let some power := state.operations.find? fun row =>
      row.category == CategoryId.rings && row.name == "^"
    | throwError "the independent-parameter control has no registered power family"
  OperationAgreement.withSourceTemplate state source.expression fun parameters context => do
    let receiver ← mkFreshExprMVar (some (← CategoryContext.carrier context))
      (userName := `independentSource)
    let first ← mkFreshExprMVar (some (mkConst ``Nat)) (userName := `firstParameter)
    let second ← mkFreshExprMVar (some (mkConst ``Nat)) (userName := `secondParameter)
    let left ← OperationAgreement.applicationTemplate power receiver #[first]
    let right ← OperationAgreement.applicationTemplate power receiver #[second]
    let families ← OperationAgreement.abstractTemplates #[first, second, receiver, left, right]
    let families ← families.mapM fun family => do mkLambdaFVars parameters family
    let families ← OperationAgreement.abstractTemplates families true
    let some leftFamily := families[3]? | unreachable!
    let some rightFamily := families[4]? | unreachable!
    unless leftFamily.getNumHeadLambdas == parameters.size + 3 do
      throwError "independent declaration parameters were identified before proof"
    if ← OperationAgreement.kernelAcceptsFamily (← mkEq leftFamily rightFamily)
        (← mkEqRefl leftFamily) then
      throwError "different whole power families were identified before their parameters were chosen"

/- A declaration may ignore a parameter computationally. Matching its complete
application must nevertheless retain the selected argument rather than its result. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let ignored ← mkAppM ``Function.const #[mkConst ``Nat, mkNatLit 0]
  let parameter ← mkFreshExprMVar (some (mkConst ``Nat))
  let template := mkApp ignored parameter
  let first := mkApp ignored (mkNatLit 1)
  let second := mkApp ignored (mkNatLit 2)
  unless ← withTransparency .all <| isDefEq first second do
    throwError "the ignored-argument control is not computationally constant"
  OperationAgreement.bindTemplate template first
  let rejected ← try
    OperationAgreement.bindTemplate template second
    pure false
  catch error =>
    if Exception.interpretationKind error == .invalid then pure true else throw error
  unless rejected do throwError "a constant result erased a complete selected parameter"

/- The existing polymorphic additive operation exercises universe quantification
and its exact selected Sort instantiation, without adding any mathematical row. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some addition := state.operations.find? (·.id.raw == "op.additive_monoids.add")
    | throwError "the declared polymorphic additive operation is absent"
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term
      "view (view (ℤ in Rings) along «fun.rings.additive_group»()) along «fun.additive_groups.additive_monoid»()"
    | throwError "the exact additive-source control did not parse"
  let source ← (eval {} term).run {}
  let #[(application, sources)] ← (selectedOperationApplicationsWithSources
      addition.declaration addition.category source #[] (some addition.name)).run {}
    | throwError "the polymorphic operation did not retain its full selected application"
  let #[selectedSource] := sources
    | throwError "the polymorphic operation did not retain a unique complete source"
  let candidate : OperationCandidate := {
    operation := addition.id, application, result := application, sources }
  let some comparison ← OperationAgreement.compareSources state candidate candidate
      selectedSource selectedSource
    | throwError "the complete polymorphic family was not retained"
  let universeNames := (collectLevelParams {} comparison.leftFamily).params
  unless !universeNames.isEmpty && comparison.parameters.size > universeNames.size &&
      (comparison.parameters.extract 0 universeNames.size).all (· matches .sort _) do
    throwError "the universal comparison erased its complete selected universe parameters"
  OperationAgreement.validateComparison state #[candidate] comparison
  let some (Expr.sort level) := (comparison.parameters[0]? : Option Expr) | unreachable!
  let changed := { comparison with
    parameters := comparison.parameters.set! 0 (Lean.mkSort (.succ level)) }
  let rejected ← try
    OperationAgreement.validateComparison state #[candidate] changed
    pure false
  catch error =>
    if Exception.interpretationKind error == .invalid then pure true else throw error
  unless rejected do throwError "a universal comparison accepted a changed selected universe"
