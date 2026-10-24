/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/-! An arbitrary opaque process reply tests dispatch and reuse only. No expected
mathematical answer is provided by this fixture or inferred from its implementation. -/

run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
    "2 * generator(F9x in CommutativeRings)"
    | throwError "the complete inherited operation did not parse"
  let trace ← Trace.new
  let .element formal _ ← (eval {} parsed).run { trace := some trace }
    | throwError "the complete inherited operation did not form a point"
  let some classNode@(.operationEquivalence representative chosen candidates comparisons) ← trace.node? formal
    | throwError "the inherited operation lost its complete checked class"
  checkOperationEquivalence formal representative chosen candidates comparisons
  let state ← registryState
  let some canonicalCandidate := candidates[chosen]?
    | throwError "the checked class lost its selected candidate"
  let alternative := candidates.findIdx? (·.operation != canonicalCandidate.operation)
  let some alternative := alternative
    | throwError "the existing universal family has no distinct retained operation"
  let some selected := candidates[alternative]?
    | throwError "the checked class lost its alternative candidate"
  let some entry := state.operations.find? (·.id == selected.operation)
    | throwError "the retained alternative operation is absent"
  let some canonicalEntry := state.operations.find? (·.id == canonicalCandidate.operation)
    | throwError "the retained canonical operation is absent"
  let program : BackendProgram := {
    name := "session-probe"
    command := "python3"
    args := #["probe_owned_callable.py", "--materialize-invocation", selected.operation.raw] }
  let registration : Registration := {
    operation := selected.operation.raw
    input := entry.category.raw
    backend := program.name }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let events ← IO.mkRef #[]
  let harness ← Harness.ofManifest root { backends := #[program], registrations := #[registration] }
  let harness := { harness with dispatches := some events }
  unless harness.rejected.isEmpty && harness.admitted.size == 1 do
    throwError "the alternative's public generic registration was not admitted"
  try
    let recipe ← realize harness trace "the checked operation class" formal
    unless recipe.callableObserved do
      throwError "ordinary evaluation did not demand the installed operation's actual result"
    let actual ← realizeArrowObservation harness trace recipe
    let #[event] ← events.get
      | throwError "the unique equivalent registration was not dispatched exactly once"
    unless (event.getObjValAs? String "operation").toOption == some selected.operation.raw &&
        actual.value == formal && actual.owner?.isSome && actual.callableObserved do
      throwError "equivalent dispatch changed the mathematical result or lost its actual owner"
    let .ok request := event.getObjVal? "request"
      | throwError "the actual equivalent dispatch lost its complete request"
    let .ok invocation := Backend.PointInvocation.decode request
      | throwError "the equivalent computation did not use the complete public invocation"
    unless invocation.operation == selected.operation.raw do
      throwError "the complete invocation lost the actual registered operation address"
    let reused ← realizeArrowObservation harness trace actual
    unless reused.json == actual.json && reused.owner? == actual.owner? &&
        reused.callableObserved && (← events.get).size == 1 do
      throwError "reusing the complete class result recomputed its formal recipe"
    let some retained ← trace.node? formal
      | throwError "execution discarded the original complete semantic class"
    unless reprStr retained == reprStr classNode do
      throwError "computational registration changed the interpreted operation class"
  finally
    harness.stop
  let canonical : Registration := {
    operation := canonicalEntry.id.raw
    input := canonicalEntry.category.raw
    backend := program.name }
  for (registrations, expected) in #[(#[], Stratum.noImplementation),
      (#[registration, canonical], Stratum.ambiguousRealization)] do
    let events ← IO.mkRef #[]
    let harness ← Harness.ofManifest root { backends := #[program], registrations }
    let harness := { harness with dispatches := some events }
    try
      let rejected ← try
        let recipe ← realize harness trace "the unchanged checked class" formal
        discard <| realizeArrowObservation harness trace recipe
        pure false
      catch error => pure (Exception.stratum? error == some expected)
      unless rejected && (← events.get).isEmpty do
        throwError "operation-class availability or ambiguity has the wrong pre-dispatch stratum"
    finally
      harness.stop

/- A second independently formed operation consumes the first operation's actual
owned reply. The process rejects a later request without its previously issued
argument token. This checks composition, with no mathematical answer oracle. -/
run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
    "2 * (2 * generator(F9x in CommutativeRings))"
    | throwError "the nested inherited operation did not parse"
  let trace ← Trace.new
  let .element formal _ ← (eval {} parsed).run { trace := some trace }
    | throwError "the nested inherited operation did not form a point"
  let some (.operationEquivalence _ chosen candidates _) ← trace.node? formal
    | throwError "the nested operation lost its complete semantic class"
  let some canonical := candidates[chosen]?
    | throwError "the nested operation lost its selected representative"
  let some selected := candidates.find? (·.operation != canonical.operation)
    | throwError "the nested operation lost its distinct declared implementation"
  let some entry := (← registryState).operations.find? (·.id == selected.operation)
    | throwError "the nested operation lost its accepted operation"
  let program : BackendProgram := {
    name := "session-probe"
    command := "python3"
    args := #["probe_owned_callable.py", "--require-argument-owner", selected.operation.raw] }
  let registration : Registration := {
    operation := selected.operation.raw
    input := entry.category.raw
    backend := program.name }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let events ← IO.mkRef #[]
  let harness ← Harness.ofManifest root { backends := #[program], registrations := #[registration] }
  let harness := { harness with dispatches := some events }
  try
    let actual ← realize harness trace "the subsequent installed operation" formal
    unless actual.value == formal && actual.callableObserved && actual.owner?.isSome &&
        (← events.get).size == 2 do
      throwError "successive operations did not execute through their exact retained interfaces"
    let reused ← realize harness trace "the complete subsequent result" formal
    unless reused.json == actual.json && reused.owner? == actual.owner? &&
        (← events.get).size == 2 do
      throwError "the subsequent actual result lost its session or was recomputed"
  finally
    harness.stop
