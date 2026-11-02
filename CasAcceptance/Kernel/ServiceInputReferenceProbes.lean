/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for exact original request positions. Two existing
protocol-fixture processes return identical opaque bytes under different live
owners. These arbitrary packets assert no mathematical answer. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def rejects (expected : Option Stratum) (work : TermElabM α) : TermElabM Unit := do
  let failure ← try
    discard <| work
    pure none
  catch error => pure (some (Exception.stratum? error, ← error.toMessageData.toString))
  let some (actual, message) := failure
    | throwError "the exact input reference control unexpectedly succeeded"
  unless actual == expected do
    throwError "the exact input reference control changed failure stratum: {message}"

private def sameWire (actual expected : Wire) : TermElabM Unit := do
  unless actual.value == expected.value && actual.fragment == expected.fragment &&
      actual.owner? == expected.owner? &&
      actual.categoryContext.map (·.bundle) == expected.categoryContext.map (·.bundle) &&
      sameCompleteWireContext actual expected do
    throwError "an exact input path replaced its original complete typed occurrence"

private def fixture : TermElabM (Trace × Harness × Wire × Wire) := do
  let trace ← Trace.new
  let state ← registryState
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the existing finite-object fixture is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set-category fixture is absent"
  let formal ← Semantic.object finite #[← `(2)] (some trace)
  let empty ← Harness.empty
  let original ← realize empty trace "the original input-reference fixture" formal
  let context ← CategoryContext.ofNamed sets formal
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[
      { name := "input-first", command := "python3",
        args := #["probe_deferred_service.py", "child", "mixed-owners-equal"] },
      { name := "input-second", command := "python3",
        args := #["probe_deferred_service.py", "child", "mixed-owners-equal"] }]
    registrations := #[] }
  let harness ← Harness.ofManifest root manifest
  let receive (backend : String) : TermElabM Wire := do
    let .ok session ← harness.connection backend
      | throwError "the input-reference protocol fixture did not start"
    let request := Json.mkObj [
      ("ctor", toJson "fun.sets.identity"), ("args", Json.arr #[]),
      ("receiver", original.json)]
    let .ok answer ← Backend.call session.connection "fun.sets.identity" request
      | throwError "the input-reference protocol fixture did not answer"
    return { original with
      payload := computedPayload formal answer (some (backend, session.identity))
      categoryContext := some context, objectObserved := true }
  try
    let first ← receive "input-first"
    let second ← receive "input-second"
    -- Retain a distinct representation of the same complete context, so a
    -- projection which reconstructs a generic category cannot pass unnoticed.
    let secondContext := { context with bundle := (← mkAppM ``id #[context.bundle]) }
    let second := { second with categoryContext := some secondContext }
    unless first.json == second.json && first.ownership != second.ownership &&
        first.owner?.isSome && second.owner?.isSome &&
        first.categoryContext.map (·.bundle) != second.categoryContext.map (·.bundle) do
      throwError "the fixture lost its distinct owners or complete context records"
    return (trace, harness, first, second)
  catch error =>
    harness.stop
    throw error

run_elab do
  let (trace, harness, first, second) ← fixture
  try
    let firstPath : DataOwnership.Path := #[.field "args", .index 0]
    let secondPath : DataOwnership.Path := #[.field "args", .index 1]
    let firstRef := Backend.inputRef (publicServiceInputPath firstPath)
    let secondRef := Backend.inputRef (publicServiceInputPath secondPath)
    let scope : ServiceScope := {
      harness, trace, references := #[second], known := #[first, second]
      inputReferences := #[(firstPath, first), (secondPath, second)]
      positionedInputs := true, operands := (← IO.mkRef #[]), backend := "input-first" }
    for (reference, expected) in #[(firstRef, first), (secondRef, second)] do
      let some selected ← serviceRetained scope reference
        | throwError "a complete input reference was not retained"
      sameWire selected expected
      sameWire (← serviceWire scope (← serviceObject scope reference)) expected
    unless (← serviceRetained scope first.json).isNone &&
        (← serviceRetained { scope with known := #[first] } first.json).isNone do
      throwError "copied bytes recovered a typed input in a positioned request"
    let some prior ← serviceRetained scope (Backend.resultRef 0)
      | throwError "an existing local result reference disappeared"
    sameWire prior second
    rejects (some .malformed) (serviceRetained scope (Backend.resultRef 1))
    for malformed in #[
        node "inputRef" #[], node "inputRef" #[Json.arr #[Json.bool true]],
        Json.mkObj [("ctor", toJson "inputRef"), ("args", Json.arr #[Json.arr #[]]),
          ("extra", toJson true)],
        Backend.inputRef #[.field "absent"], Backend.inputRef #[]] do
      rejects (some .malformed) (serviceRetained scope malformed)
    rejects (some .malformed) (serviceRetained scope firstRef (some (mkConst ``Nat)))
    rejects (some .malformed) (serviceRetained
      { scope with inputReferences := #[(firstPath, first), (firstPath, first)] } firstRef)
    unless (Backend.validateResultRefs 1 firstRef).isOk &&
        (Backend.validateResultRefs 1 (Backend.resultRef 0)).isOk &&
        !(Backend.validateResultRefs 1 (Backend.resultRef 1)).isOk do
      throwError "input references changed the completed local result scope"

    let handles ← retainServiceOperands harness #[first, second]
    let data ← scopedNode "objectProduct" #[first.fragment, second.fragment]
    let formal ← mkAppM ``Prod #[first.value, second.value]
    let input : Wire := {
      form := first.form, payload := (← scopedPayload formal data)
      serviceHandles := handles
      serviceInputPaths := some #[(firstPath, handles[0]!), (secondPath, handles[1]!)] }
    let (positioned, known, references) ← serviceRequestInputs harness input
    unless positioned && known.isEmpty && references.size == 2 do
      throwError "the prepared request did not retain an exact positional scope"
    for ((actualPath, actual), (expectedPath, expected)) in
        references.zip #[(firstPath, first), (secondPath, second)] do
      unless actualPath == expectedPath do throwError "the original request position changed"
      sameWire actual expected
    let (positioned, known, references) ← serviceRequestInputs harness
      { input with serviceInputPaths := some #[] }
    unless positioned && known.isEmpty && references.isEmpty do
      throwError "an exact empty input scope enabled packet recovery"
    -- Equal bytes with exchanged suppliers must fail before a service is read.
    let exchanged ← scopedNode "objectProduct" #[second.fragment, first.fragment]
    unless exchanged.json == data.json do throwError "the ownership-negative fixture changed bytes"
    rejects none (serviceRequestInputs harness
      { input with payload := (← scopedPayload formal exchanged) })
    rejects (some .unavailable) (serviceRequestInputs harness
      { input with serviceInputPaths := some #[(#[.field "absent"], handles[0]!)] })
    rejects none (serviceRequestInputs harness
      { input with serviceInputPaths := some #[(firstPath, handles[0]!), (firstPath, handles[0]!)] })

    let template := node "typedMap" #[firstRef, secondRef,
      node "identity" #[firstRef, secondRef]]
    let assembled ← assembleServiceResult scope template
    unless (assembled.project #[.field "args", .index 0]).toOption == some first.fragment &&
        (assembled.project #[.field "args", .index 1]).toOption == some second.fragment do
      throwError "nested typed-map assembly changed an original endpoint supplier"
    let arrow ← serviceArrow scope template
    let source ← serviceEndpoint scope arrow true
    let target ← serviceEndpoint scope arrow false
    sameWire (← serviceWire scope source) first
    sameWire (← serviceWire scope target) second

    -- The builder normalizes the public request before assigning typed operand
    -- positions. The whole original typed map occupies its declared slot;
    -- repeated endpoint positions still point to their exact original Wires.
    let state ← registryState
    let some identityFunctor := state.functors.find? (·.id.raw == "fun.sets.identity")
      | throwError "the published identity functor fixture is absent"
    let invocation : Backend.PointInvocation := {
      operation := identityFunctor.mapAddress, parameters := #[]
      arrow := node "map" #[node identityFunctor.id.raw #[], template]
      domain := firstRef, source := firstRef, target := secondRef
      argument := node "identity" #[firstRef, firstRef] }
    let prepared ← SimpleServiceRequest.mapAction (← serviceDecoder scope)
      (.functorMap identityFunctor) first.form invocation.encode
    unless prepared.inputPaths.size == 5 do
      throwError "the normalized map request changed its complete operand inventory"
    for (path, operand) in prepared.inputPaths do
      unless (prepared.fragment.project path).toOption == some operand.fragment do
        throwError "the normalized operand path changed its original packet or suppliers"
    let expectedPositions : Array (DataOwnership.Path × Wire) := #[
      (#[.field "args", .index 3], first),
      (#[.field "args", .index 4], first),
      (#[.field "args", .index 5], second)]
    for (path, expected) in expectedPositions do
      let #[(_, original)] := prepared.inputPaths.filter (·.1 == path)
        | throwError "the normalized request merged repeated original endpoints"
      sameWire (← serviceWire scope original) expected
    let #[(_, originalMap)] := prepared.inputPaths.filter
        (·.1 == #[.field "args", .index 2, .field "args", .index 1])
      | throwError "the normalized request lost its original whole typed-map position"
    sameWire (← serviceWire scope (← serviceEndpoint scope originalMap true)) first
    sameWire (← serviceWire scope (← serviceEndpoint scope originalMap false)) second
    logInfo "PASS: exact input paths, distinct equal-packet suppliers, local result scope, and nested endpoint retention"
  finally harness.stop

end
