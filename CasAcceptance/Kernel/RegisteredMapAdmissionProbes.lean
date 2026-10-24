/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for dependent map formation. The mathematical domains,
inclusions and evidence procedures are the independent published registrations.
The checks concern complete types, retained original maps and data ownership. -/

open Lean Meta Elab Command Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_cmd liftTermElabM <| withoutErrToSorry do
  for (termSyntax, projection) in #[
      ((← `(CasCatalogue.Modules.IntegerResidueModules.integerResidueModule 5 ⟶
        CasCatalogue.Modules.IntegerResidueModules.integerResidueModule 5)), false),
      ((← `((ℚ × ℚ) →ₗ[ℚ] ℚ)), true)] do
    let expected ← elabTermAndSynthesize termSyntax none
    let some plan ← DeclaredAdmission.resolve? CategoryId.sets expected projection
      | throwError "the complete demanded type has no registered admission"
    unless plan.entry.admission.isSome && plan.entry.evidence.isSome &&
        !plan.application.value.hasMVar && !plan.application.value.hasLevelMVar &&
        plan.projections.isEmpty == !projection do
      throwError "the admission planner lost its exact full type or declared data projection"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let mut scope : Scope := {}
  for (name, text) in #[("R", "ℤ in Rings"), ("M", "RegularModule(R)")] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the selected map input did not parse"
    scope := scope.insert name.toName parsed
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
    "(m ↦ m + m) in M → M"
    | throwError "the full selected map did not parse"
  let trace ← Trace.new
  let value ← (eval scope parsed).run { trace := some trace }
  let (hom, source, target, context, _, _) ← (morphismContext value).run {}
  let selected ← (eval scope (← `(cas_term| M))).run {}
  let selectedContext ← (objectContext selected).run {}
  unless context.expression.syntacticEq selectedContext.expression &&
      (← withTransparency .all <| isDefEq context.bundle selectedContext.bundle) do
    throwError "the lambda replaced its selected full category"
  CategoryContext.checkMorphism context hom source target
  unless (← trace.get).toArray.any (fun (_, node) => match node with
      | .admittedPoint _ _ _ original _ _ _ => original != hom
      | _ => false) do
    throwError "the typed map lost its registered admission or original computational map"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let expected ← elabTermAndSynthesize (← `((ℚ × ℚ) →ₗ[ℚ] ℚ)) none
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "((a, b) ↦ a)"
    | throwError "the typed destructured parameter did not parse"
  let trace ← Trace.new
  let value ← (selectedTypedParameter {} expected parsed).run { trace := some trace }
  unless !value.hasMVar && !value.hasLevelMVar && (← isTypeCorrect value) &&
      (← withTransparency .all <| isDefEq (← inferType value) expected) do
    throwError "the destructured map parameter lost its complete declared type"
  let some (.elementValue point target _) ← trace.node? value
    | throwError "the declared wrapper projection dropped its original admitted point"
  let action ← functionOf point
  let original := mkApp action (← globalPoint.run {})
  unless ← withTransparency .all <| isDefEq (← inferType original) target do
    throwError "the projected parameter changed its original admitted point type"
  let some projected ← DeclaredAdmission.projectedValue? original expected
    | throwError "the parameter no longer has the public single-data-field extraction"
  unless ← withTransparency .all <| isDefEq projected value do
    throwError "the retained point supplies a different complete typed parameter"
  let opaque := Json.mkObj [("ctor", "opaqueData"), ("args", Json.arr #["declared-map-data"])]
  let harness ← Harness.empty
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the point parameter has no declared data category"
  let source : Wire := {
    form := .canonicalMorphism sets
    payload := .computed point (.owned "retained-map-session" 19 opaque) }
  harness.results.modify (·.insert point source)
  let actual ← realize harness trace "the projected actual callable parameter" value
  let .ok ("element", #[_, pointData]) := ComputationalData.envelope actual.json
    | throwError "the projected parameter lost its public element frame"
  let .ok ("point", #[actualSource]) := ComputationalData.envelope pointData
    | throwError "the projected parameter lost its retained point frame"
  unless actual.owner? == source.owner? && actualSource == opaque do
    throwError "the typed wrapper projection lost its actual opaque data or owner"
