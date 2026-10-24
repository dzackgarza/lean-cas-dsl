/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Materialize a complete registered operation recipe through its existing
generalized PointInvocation. The process produces an arbitrary opaque data
witness. No expected mathematical answer or additional operation is supplied. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
    "(x ↦ x + x) in ℤ → ℤ"
    | throwError "the ordinary generalized operation recipe did not parse"
  let trace ← Trace.new
  let .morphism formal domain target _ _ ← (eval {} parsed).run { trace := some trace }
    | throwError "the generalized recipe did not retain its complete formal arrow"
  let operations := (← trace.get).toArray.filterMap fun (body, node) => match node with
    | .operationApply id parameters operands result selected =>
        some (body, id, parameters, operands, result, selected)
    | _ => none
  let #[(body, operation, _, operands, _, _)] := operations
    | throwError "the recipe no longer contains its one declared operation"
  let state ← registryState
  let some row := state.operations.find? (·.id == operation)
    | throwError "the recipe's accepted operation is absent"
  unless operands.size == row.arity && operands.size == 2 do
    throwError "the generalized recipe lost its complete original operands"
  unless !(← withTransparency .all <| isDefEq domain (← closedElementDomain state)) do
    throwError "the whole-map fixture accidentally became a singleton point computation"
  let manifest : Manifest := {
    backends := #[{
      name := "session-probe"
      command := "python3"
      args := #["probe_owned_callable.py", "--materialize-invocation", operation.raw] }]
    registrations := #[{
      operation := operation.raw
      input := row.category.raw
      backend := "session-probe" }] }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let observations ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  let harness := { harness with dispatches := some observations }
  unless harness.rejected.isEmpty && harness.admitted.size == 1 do
    throwError "the existing generic operation registration was not admitted"
  try
    let descriptor ← realize harness trace "the whole operation recipe" formal
    let actual ← realizeArrowObservation harness trace descriptor
    let some owner := actual.owner?
      | throwError "observing a complete registered operation recipe did not materialize its generalized callable"
    unless actual.value == formal do
      throwError "materialization changed the original complete formal map"
    let #[sent] ← observations.get
      | throwError "the one generalized operation was not actually dispatched exactly once"
    let .ok request := sent.getObjVal? "request" | throwError "the dispatch lost its request"
    let .ok invocation := Backend.PointInvocation.decode request
      | throwError "the complete operation did not use the existing public PointInvocation"
    let domainWire ← realizeEndpoint harness trace "the original generalized domain" domain
    let targetWire ← realizeEndpoint harness trace "the original selected codomain" target
    unless invocation.operation == operation.raw && invocation.domain == domainWire.json &&
        invocation.target == targetWire.json do
      throwError "materialization changed the accepted operation or its actual generalized endpoints"
    let some retained := (← harness.results.get)[body]?
      | throwError "the materialized operation body was not retained for subsequent computations"
    unless retained.owner? == some owner && retained.json == actual.json do
      throwError "the callable recipe replaced its actual returned constituent"
    let again ← realizeArrowObservation harness trace actual
    unless again.owner? == actual.owner? && again.json == actual.json &&
        (← observations.get).size == 1 do
      throwError "observing a retained whole callable replayed its formal recipe"
    let some (actualDomain, actualTarget) := homEnds? (← inferType actual.value)
      | throwError "the returned callable lost its original formal endpoints"
    unless ← isDefEq actualDomain domain <&&> isDefEq actualTarget target do
      throwError "the returned complete callable changed its original generalized domain"
  finally
    harness.stop
