/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for lexical binding ownership and actual parameter endpoint reuse. -/

open Lean Meta Elab Command Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the lexical control input did not parse"
    return stx
  let quoted ← `(cas_term| M)
  let `(cas_term| $identifier:ident) := quoted | unreachable!
  unless identifier.getId != identifier.getId.eraseMacroScopes do
    throwError "the quoted lexical control has no macro scope"
  let first ← parse "ℤ in Rings"
  let second ← parse "ℚ in Rings"
  let plain : Language.Scope := ({} : Language.Scope).insert `M first
  let expectedFirst ← (eval {} first).run {}
  let expectedSecond ← (eval {} second).run {}
  let actual ← (eval plain quoted).run {}
  unless actual.sameSource expectedFirst do
    throwError "a quoted reference did not retain its complete file binding"
  unless ← (namesObject plain quoted).run {} do
    throwError "quoted file lookup and object recognition disagree"
  let exact := plain.insert identifier.getId second
  let actual ← (eval exact quoted).run {}
  unless actual.sameSource expectedSecond do
    throwError "an exact scoped file binding lost precedence over its written name"
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let trace ← Trace.new
  let plainReference ← parse "M"
  let plainValue ← (eval exact plainReference).run
    { trace := some trace, closedTerms := some cache }
  let quotedValue ← (eval exact quoted).run { trace := some trace, closedTerms := some cache }
  unless plainValue.sameSource expectedFirst && quotedValue.sameSource expectedSecond do
    throwError "closed reading reuse identified distinct lexical file bindings"
  let actual ← (eval exact quoted).run { bound := [(identifier.getId, expectedFirst)] }
  unless actual.sameSource expectedFirst do
    throwError "a file binding captured an exact lexical stage binding"
  let other ← withFreshMacroScope `(cas_term| M)
  let `(cas_term| $otherIdentifier:ident) := other | unreachable!
  unless otherIdentifier.getId != identifier.getId do
    throwError "the independent lexical control scopes coincide"
  let actual ← (eval plain quoted).run { bound := [(otherIdentifier.getId, expectedSecond)] }
  unless actual.sameSource expectedFirst do
    throwError "different lexical macro scopes captured one another"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let expected ← elabTermAndSynthesize (← `((ℚ × ℚ) →ₗ[ℚ] ℚ)) none
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "((a, b) ↦ a)"
    | throwError "the endpoint reuse control did not parse"
  let trace ← Trace.new
  let value ← (selectedTypedParameter {} expected parsed).run { trace := some trace }
  let some (.elementValue point target selected) ← trace.node? value
    | throwError "the endpoint reuse control has no original admitted point"
  unless ← withTransparency .all <| isDefEq selected target do
    throwError "the control's selected object is not the complete point target"
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the endpoint reuse control has no set category"
  let packet := Json.mkObj [("ctor", "opaqueData"), ("args", Json.arr #["actual point"])]
  let supplied : Wire := {
    form := .canonicalMorphism sets
    payload := .computed point (.owned "actual-parameter" 43 packet) }
  let harness ← Harness.empty
  harness.results.modify (·.insert point supplied)
  let actual ← realize harness trace "the original projected parameter" value
  let .ok ("element", #[selectedData, pointData]) := ComputationalData.envelope actual.json
    | throwError "the projected parameter lost its element frame"
  let .ok endpoint := Backend.MorphismEndpoint.decode selectedData
    | throwError "the unnamed selected target did not use its complete actual callable"
  unless !endpoint.source && endpoint.callable == packet &&
      actual.owner? == supplied.owner? && actual.value == value &&
      pointData == Json.mkObj [("ctor", "point"), ("args", Json.arr #[packet])] do
    throwError "the endpoint frame changed the direction, actual packet, owner or formal parameter"
  -- A separately supplied complete target takes precedence and participates in ownership.
  let actualTarget := Json.mkObj [("ctor", "opaqueData"), ("args", Json.arr #["actual target"])]
  for foreign in #[false, true] do
    let harness ← Harness.empty
    let targetWire : Wire := {
      form := .diagrams sets
      payload := .computed selected
        (.owned "actual-parameter" (if foreign then 44 else 43) actualTarget) }
    harness.results.modify fun cache => (cache.insert point supplied).insert selected targetWire
    if foreign then
      let rejected ← try
        discard <| realize harness trace "the foreign selected target" value
        pure false
      catch error =>
        if Exception.stratum? error == some .unavailable then pure true else throw error
      unless rejected do throwError "a projected parameter combined different owning sessions"
    else
      let actual ← realize harness trace "the actual selected target" value
      let .ok ("element", #[selectedData, _]) := ComputationalData.envelope actual.json
        | throwError "the independently supplied target lost its element frame"
      unless selectedData == actualTarget && actual.owner? == supplied.owner? do
        throwError "the endpoint fallback replaced a supplied complete target"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok ring := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "the structured-selection control ring did not parse"
  let .ok literal := Parser.runParserCategory (← getEnv) `cas_term "1 in R"
    | throwError "the structured-selection control point did not parse"
  let scope : Language.Scope := ({} : Language.Scope).insert `R ring
  let trace ← Trace.new
  let original ← (eval scope literal).run { trace := some trace }
  let expected ← elabTermAndSynthesize (← `(ℤ)) none
  let value ← (typedParameter expected original).run { trace := some trace }
  let some (.elementValue point target selected) ← trace.node? value
    | throwError "the scalar parameter lost its complete selected object"
  if ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType selected) (← inferType target)) then
    throwError "the structured-selection control has only a bare carrier"
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the structured-selection control has no set category"
  let packet := Json.mkObj [("ctor", "opaqueData"), ("args", Json.arr #["selected ring point"])]
  let supplied : Wire := {
    form := .canonicalMorphism sets
    payload := .computed point (.owned "actual-parameter" 45 packet) }
  let harness ← Harness.empty
  harness.results.modify (·.insert point supplied)
  let actual ← realize harness trace "the structured scalar parameter" value
  let .ok ("element", #[selectedData, _]) := ComputationalData.envelope actual.json
    | throwError "the selected scalar lost its complete element frame"
  let selectedWire ← realize harness trace "the original selected ring" selected
  unless selectedData == selectedWire.json && actual.owner? == supplied.owner? do
    throwError "the scalar parameter replaced its selected structure with the carrier endpoint"
  if (Backend.MorphismEndpoint.decode selectedData).isOk then
    throwError "a bare carrier supplied the selected ring structure"
