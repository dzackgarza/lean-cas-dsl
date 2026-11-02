/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for action reuse after positioned service input lookup.
Two selected producers have the same fixed result port and receive identical
portable protocol witnesses. The field-result boundary retains their distinct
request operands, exactly as `observeLiftStageFieldWithInputs` does. No backend
is started, and these arbitrary packets establish no mathematical answer.

`ServiceCycleProbes` separately checks that recursion detection ignores purely
administrative handle reallocation. This probe concerns completed action reuse. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

run_elab do
  let harness ← Harness.empty
  let trace ← Trace.new
  let state ← registryState
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the action-cache fixture lost its existing finite-object declaration"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the action-cache fixture lost its existing set category"
  let some identity := state.functors.find? (·.id.raw == "fun.sets.identity")
    | throwError "the action-cache fixture lost its existing identity action"
  let source ← Semantic.object finite #[← `(2)] (some trace)
  let context ← CategoryContext.ofNamed sets source
  let action ← Semantic.edgeFunctor state (.functor identity.id)
  let port ← Semantic.objOf action source
  let selected : Node := .functor identity.id #[] source
  let firstProducer ← Trace.recordProduced (some trace) port selected
  let secondProducer ← Trace.recordProduced (some trace) port selected
  Trace.checkProducerRecord firstProducer selected
  Trace.checkProducerRecord secondProducer selected
  unless firstProducer != secondProducer &&
      Trace.unanchor firstProducer == Trace.unanchor secondProducer do
    throwError "the action-cache fixture did not retain two equal-formal selected producers"

  let packet : DataOwnership.Data := { json := node "valueData" #[toJson (73 : Nat)] }
  -- Actual field outputs carry their request's fresh, nonempty retained prefix;
  -- the public port itself need not contain the containing producer's anchor.
  let returned (producer : Expr) : TermElabM Wire := do
    let original ← liftOperand producer context (.object finite) packet false true
    let handles ← retainServiceOperands harness #[original]
    let output ← liftOperand port context (.object finite) packet false true
    return { output with serviceHandles := handles ++ original.serviceHandles }
  let first ← returned firstProducer
  let second ← returned secondProducer
  unless sameActionOperand first second && first.fragment == second.fragment &&
      !first.serviceHandles.isEmpty && first.serviceHandles != second.serviceHandles do
    throwError "the action-cache fixture did not isolate distinct retained output occurrences"
  let retained ← harness.serviceOperands.get
  let some firstOriginal := retained[first.serviceHandles[0]!]?
    | throwError "the first returned packet lost its retained input slot"
  let some secondOriginal := retained[second.serviceHandles[0]!]?
    | throwError "the second returned packet lost its retained input slot"
  unless firstOriginal.value == firstProducer && secondOriginal.value == secondProducer do
    throwError "the returned packets lost their respective selected producer inputs"

  -- Re-retention and explicit input-reference decoding preserve the actual
  -- stored output. New lookup indices must not replace its request receipt.
  let firstPath : DataOwnership.Path := #[.field "args", .index 0]
  let secondPath : DataOwnership.Path := #[.field "args", .index 1]
  let data ← scopedNode "objectProduct" #[first.fragment, second.fragment]
  let requestValue ← mkAppM ``Prod #[port, port]
  let positions := #[(firstPath, first), (secondPath, second)]
  let paths ← retainServiceInputPaths harness data positions
  let laterPaths ← retainServiceInputPaths harness data positions
  unless paths != laterPaths do
    throwError "the same-production fixture did not reallocate lookup indices"
  let request : Wire := {
    form := .diagrams sets, payload := (← recipePayload requestValue data)
    serviceInputPaths := some laterPaths }
  let (positioned, known, inputs) ← serviceRequestInputs harness request
  let scope : ServiceScope := {
    harness, trace, references := #[], known
    inputReferences := inputs, positionedInputs := positioned
    operands := (← IO.mkRef #[]), backend := "unused" }
  let read (path : DataOwnership.Path) : TermElabM Wire := do
    let operand ← serviceObject scope (Backend.inputRef (publicServiceInputPath path))
    serviceWire scope operand
  let firstInput ← read firstPath
  let secondInput ← read secondPath
  unless firstInput.serviceHandles == first.serviceHandles &&
      secondInput.serviceHandles == second.serviceHandles do
    throwError "exact input references replaced the original output's retained handles"

  let resultFormal ← Semantic.objOf action port
  let result ← liftOperand resultFormal context (.object finite) packet false true
  let firstResult := { result with serviceHandles := first.serviceHandles }
  let secondResult := { result with serviceHandles := second.serviceHandles }
  -- Exercise each independent key component used by object and map receipts.
  let firstRecord : ActionExecution := {
    operation := identity.id.raw, action, input := firstInput, parameters := #[]
    parameterInputs := #[firstInput], imageEndpoints := #[firstInput, firstInput]
    result := firstResult }
  retainActionResult harness firstRecord
  let find (input : Wire) (parameters images : Array Wire) :=
    retainedActionResult? harness identity.id.raw action input #[] parameters images
  let miss (label : String) (input : Wire) (parameters images : Array Wire) : TermElabM Unit := do
    if (← find input parameters images).isSome then
      throwError "equal output packets merged distinct retained {label} occurrences"
  let reuse (input : Wire) (parameters images : Array Wire) (expected : Wire) : TermElabM Unit := do
    let some actual ← find input parameters images
      | throwError "the same completed production was not reusable"
    unless actual.value == expected.value && actual.fragment == expected.fragment &&
        actual.serviceHandles == expected.serviceHandles do
      throwError "action reuse selected another production's completed result"
  reuse firstInput #[firstInput] #[firstInput, firstInput] firstResult
  miss "input" secondInput #[firstInput] #[firstInput, firstInput]
  miss "parameter" firstInput #[secondInput] #[firstInput, firstInput]
  miss "source image" firstInput #[firstInput] #[secondInput, firstInput]
  miss "target image" firstInput #[firstInput] #[firstInput, secondInput]

  -- Installing the second receipt also replaces the equal formal entry in
  -- h.results. Each action lookup must still return its own retained result.
  retainActionResult harness { firstRecord with
    input := secondInput, parameterInputs := #[secondInput]
    imageEndpoints := #[secondInput, secondInput], result := secondResult }
  reuse firstInput #[firstInput] #[firstInput, firstInput] firstResult
  reuse secondInput #[secondInput] #[secondInput, secondInput] secondResult
  reuse (← read firstPath) #[firstInput] #[firstInput, firstInput] firstResult
  logInfo "PASS: action reuse preserves distinct equal-packet productions at every retained input position"

end
