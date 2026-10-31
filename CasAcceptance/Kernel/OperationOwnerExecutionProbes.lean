/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for a target operation whose selected owner is the
image of existing registered actions. The unchanged protocol process returns
arbitrary opaque packets. No arithmetic answer, new mathematical declaration,
or leaf implementation is supplied or accepted by these controls. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

namespace CasCatalogue.OperationOwnerExecutionProbes
meta section

private def parse (text : String) : TermElabM Syntax := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the existing selected-owner control did not parse"
  return parsed

private def selectedOwner (trace : Trace) : TermElabM (Value × Expr × OperationEntry) := do
  let source ← (eval {} (← parse
    "view (view (ℤ in Rings) along «fun.rings.additive_group»()) along «fun.additive_groups.additive_monoid»()")).run { trace := some trace }
  let owner ← (semanticObject source).run {}
  let some operation := (← registryState).operations.find?
      (·.id.raw == "op.additive_monoids.add")
    | throwError "the accepted additive-monoid operation is absent"
  return (source, owner, operation)

private def harnessFor (operation : OperationEntry) (complete : Bool := true) :
    TermElabM (Harness × IO.Ref (Array Json)) := do
  let state ← registryState
  let ids := #["fun.rings.additive_group", "fun.additive_groups.additive_monoid"]
  let actions ← ids.mapM fun id => do
    let some action := state.functors.find? (·.id.raw == id)
      | throwError "the selected owner lost an existing action"
    unless action.structural do
      throwError "the selected-owner control no longer exercises structural actions"
    return action
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "owner-probe", command := "python3"
      args := #["probe_owned_callable.py", "--require-argument-owner"] ++
        ids ++ #[operation.id.raw] }]
    registrations := (if complete then actions else actions.extract 0 1).map (fun action => {
      operation := action.id.raw, input := action.inputAddress, backend := "owner-probe" }) ++ #[{
      operation := operation.id.raw, input := operation.category.raw, backend := "owner-probe" }] }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == (if complete then 3 else 2) do
    throwError "the existing action ports or target-category operation were not admitted"
  return ({ harness with dispatches := some calls, demandObjectActions := true }, calls)

private partial def containsData (data expected : Json) : Bool :=
  data == expected || match data with
    | .arr fields => fields.any (containsData · expected)
    | .obj fields => fields.any fun _ field => containsData field expected
    | _ => false

private def checkActualOwner (harness : Harness) (trace : Trace)
    (calls : IO.Ref (Array Json)) (operation : OperationEntry) (owner : Expr)
    (actual : Wire) : TermElabM Unit := do
  let events ← calls.get
  unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
      #[some "fun.rings.additive_group", some "fun.additive_groups.additive_monoid",
        some operation.id.raw] do
    throwError "target-category operation dispatched before its two selected owner actions"
  let #[first, second] ← harness.actions.get
    | throwError "the selected owner lost an actual intermediate action receipt"
  unless first.operation == "fun.rings.additive_group" &&
      second.operation == "fun.additive_groups.additive_monoid" &&
      first.result.objectObserved && second.result.objectObserved &&
      first.result.fragment == second.input.fragment &&
      first.result.json != second.result.json do
    throwError "the owner actions did not compose their distinct actual returned packets"
  let .ok secondRequest := events[1]!.getObjVal? "request"
    | throwError "the second owner action lost its actual request"
  unless (secondRequest.getObjVal? "receiver").toOption == some first.result.json do
    throwError "the second owner action replaced the first actual result by its recipe"
  let .ok request := events[2]!.getObjVal? "request"
    | throwError "the target operation lost its complete request"
  let .ok invocation := Backend.PointInvocation.decode request
    | throwError "the target operation lost its existing generalized-point interface"
  unless invocation.operation == operation.id.raw &&
      invocation.parameters == #[second.result.json] &&
      containsData invocation.arrow second.result.json &&
      !containsData invocation.arrow first.input.json &&
      (events[2]!.getObjValAs? String "registrationInput").toOption ==
        some operation.category.raw do
    throwError "the target-category operation received a source recipe instead of its actual owner"
  unless actual.callableObserved && actual.owner? == second.result.owner? &&
      actual.owner?.isSome do
    throwError "the actual operation result lost its supplying owner"
  let (parameters, dependencies) ← realizedParameterData
    { harness with demandObjectActions := false } trace #[owner]
  unless parameters == #[second.result.fragment] && dependencies.any
      (fun dependency => dependency.fragment == second.result.fragment) do
    throwError "the completed owner was not reused at its retained parameter occurrence"
  let reused ← realizeArrowObservation harness trace actual
  unless reused.fragment == actual.fragment && (← calls.get).size == 3 do
    throwError "reusing the completed target operation replayed an owner action"

-- The public generalized lambda supplies an ordinary operationApply node. Its
-- selected owner is a complete additive monoid, not a source-form registration
-- for the two preceding functors.
run_elab do
  for complete in #[true, false] do
    let trace ← Trace.new
    let (source, owner, operation) ← selectedOwner trace
    discard <| (eval {} (← parse "(x ↦ x + x) in A → A")).run
      { trace := some trace, bound := [(`A, source)] }
    let operations := (← trace.get).toArray.filterMap fun (formal, node) => match node with
      | .operationApply id parameters _ _ _ =>
          if id == operation.id then some (formal, parameters) else none
      | _ => none
    let #[(formal, parameters)] := operations
      | throwError "the selected lambda did not retain one existing additive operation"
    let (harness, calls) ← harnessFor operation complete
    try
      let recipe ← realizeUnobserved harness trace "the selected operation's public recipe" formal
      discard <| prepareOperationObservation harness trace recipe operation.id parameters
      unless (← calls.get).isEmpty && (← harness.actions.get).isEmpty do
        throwError "preparing a candidate executed its unselected owner actions"
      if complete then
        let actual ← realizeOperationObservation harness trace recipe operation.id parameters
        checkActualOwner harness trace calls operation owner actual
      else
        let missing ← try
          discard <| realizeOperationObservation harness trace recipe operation.id parameters
          pure false
        catch error => pure (Exception.stratum? error == some .noImplementation)
        unless missing && (← calls.get).size == 1 && (← harness.actions.get).size == 1 do
          throwError "a missing selected owner action dispatched the target operation or hid its gap"
    finally harness.stop

-- The whole named callable uses the same declared operation and owner, but its
-- original parameter descriptor is built before observation. Both request
-- parameter occurrences must be rebuilt from the demanded image.
run_elab do
  let trace ← Trace.new
  let (source, owner, operation) ← selectedOwner trace
  let #[(application, _)] ← (selectedOperationApplicationsWithSources
      operation.declaration operation.category source #[] (some operation.name)).run
        { trace := some trace }
    | throwError "the complete selected owner did not determine its declared operation"
  let infos ← forallTelescopeReducing (← getConstInfo operation.declaration).type fun arguments _ =>
    arguments.mapM (·.fvarId!.getBinderInfo)
  let parameters := (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
    if info.isExplicit then some argument else none
  let formal ← Trace.recordCallable (some trace) application
    (.namedCallable operation.id.raw operation.category parameters)
  let (harness, calls) ← harnessFor operation
  try
    let descriptor ← realize harness trace "the complete selected operation descriptor" formal
    unless (← calls.get).isEmpty do
      throwError "constructing a whole callable descriptor executed its owner"
    let actual ← realizeArrowObservation harness trace descriptor
    checkActualOwner harness trace calls operation owner actual
  finally harness.stop


-- A request position may allocate a handle that did not exist in the original
-- operand table. That future allocation must never repair an original missing
-- dependency. Both preparations below use the same public operation and the
-- same retained inputs; only the original recipe's invalid handle is changed.
run_elab do
  let trace ← Trace.new
  let (source, _, operation) ← selectedOwner trace
  discard <| (eval {} (← parse "(x ↦ x + x) in A → A")).run
    { trace := some trace, bound := [(`A, source)] }
  let operations := (← trace.get).toArray.filterMap fun (formal, node) => match node with
    | .operationApply id parameters _ _ _ =>
        if id == operation.id then some (formal, parameters) else none
    | _ => none
  let #[(formal, parameters)] := operations
    | throwError "the missing-operand control lost its existing operation occurrence"
  let (harness, _) ← harnessFor operation
  try
    let recipe ← realizeUnobserved harness trace "the original missing-operand control" formal
    let originalOperands ← harness.serviceOperands.get
    let originalTrace ← trace.get
    let fork : IO Harness := do
      return { harness with
        connections := ← IO.mkRef (← harness.connections.get)
        results := ← IO.mkRef (← harness.results.get)
        actions := ← IO.mkRef (← harness.actions.get)
        replies := ← IO.mkRef (← harness.replies.get)
        services := ← IO.mkRef (← harness.services.get)
        derivations := ← IO.mkRef (← harness.derivations.get)
        portFailures := ← IO.mkRef (← harness.portFailures.get)
        serviceOperands := ← IO.mkRef originalOperands
        invocations := ← IO.mkRef (← harness.invocations.get)
        dispatches := some (← IO.mkRef #[]) }
    let positive ← fork
    let positiveTrace ← IO.mkRef originalTrace
    let prepared ← prepareOperationObservation positive positiveTrace recipe operation.id parameters
    let some paths := prepared.input.serviceInputPaths
      | throwError "the valid operation lost its explicit request positions"
    let arrowPath : DataOwnership.Path := #[.field "args", .index 2]
    let targetPath : DataOwnership.Path := #[.field "args", .index 5]
    let some (_, arrowHandle) := paths.find? (·.1 == arrowPath)
      | throwError "the valid operation lost its whole callable position"
    let some (_, targetHandle) := paths.find? (·.1 == targetPath)
      | throwError "the valid operation lost its exact target position"
    let preparedOperands ← positive.serviceOperands.get
    let some arrow := preparedOperands[arrowHandle]?
      | throwError "the valid operation lost its whole callable occurrence"
    let some target := preparedOperands[targetHandle]?
      | throwError "the valid operation lost its target occurrence"
    unless arrow.morphismFramed &&
        sameCompleteWireContext target prepared.targetWire &&
        (← checkedFragment (prepared.input.fragment.project targetPath)) == target.fragment &&
        targetHandle >= originalOperands.size do
      throwError "the missing-operand control requires a genuine framed request and fresh complete target"
    let negative ← fork
    let negativeTrace ← IO.mkRef originalTrace
    let changed := { recipe with serviceHandles := recipe.serviceHandles.push targetHandle }
    let rejected ← try
      discard <| prepareOperationObservation negative negativeTrace changed operation.id parameters
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      if (message.splitOn "the operation presentation lost an exact operand occurrence").length > 1 then
        pure true
      else throw error
    unless rejected do
      throwError "a fresh operation input path repaired an originally missing operand handle"
    for scope in #[positive, negative] do
      let some calls := scope.dispatches | unreachable!
      unless (← calls.get).isEmpty && (← scope.actions.get).isEmpty &&
          (← scope.connections.get).isEmpty do
        throwError "operand-inventory preparation executed an unselected owner action"
  finally harness.stop

end
end CasCatalogue.OperationOwnerExecutionProbes
