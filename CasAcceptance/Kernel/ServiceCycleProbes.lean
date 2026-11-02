/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for deferred service recursion. These compare retained
request occurrences and exercise the guard before request preparation. No backend
is started, and the arbitrary deferred result asserts no mathematical answer. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

run_elab do
  let trace ← Trace.new
  let harness ← Harness.empty
  let state ← registryState
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the existing finite-object fixture is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set-category fixture is absent"
  let formal ← Semantic.object finite #[← `(2)] (some trace)
  let context ← CategoryContext.ofNamed sets formal
  let operand : Wire := {
    form := .object finite
    payload := (← scopedPayload formal { json := node finite.id.raw #[toJson (2 : Nat)] })
    categoryContext := some context }
  let data ← scopedNode "objectProduct" #[operand.fragment, operand.fragment]
  let requestValue ← mkAppM ``Prod #[formal, formal]
  let firstPath : DataOwnership.Path := #[.field "args", .index 0]
  let secondPath : DataOwnership.Path := #[.field "args", .index 1]
  let positions := #[(firstPath, operand), (secondPath, operand)]
  let firstBindings ← retainServiceInputPaths harness data positions
  let secondBindings ← retainServiceInputPaths harness data positions
  let first : Wire := {
    form := .diagrams sets, payload := (← scopedPayload requestValue data)
    serviceInputPaths := some firstBindings }
  let second := { first with serviceInputPaths := some secondBindings }
  if sameServiceSelection first second then
    throwError "the recursion fixture did not allocate distinct administrative handles"
  unless ← sameServiceRequestForCycle harness first second do
    throwError "reallocated handles hid an identical exact request from the recursion guard"
  unless ← sameServiceRequestForCycle harness first
      { second with serviceInputPaths := some #[secondBindings[1]!, secondBindings[0]!] } do
    throwError "position-table order changed exact service request identity"
  if ← sameServiceRequestForCycle harness
      { first with serviceInputPaths := some #[firstBindings[0]!] }
      { second with serviceInputPaths := some #[secondBindings[1]!] } then
    throwError "different exact public input positions were merged"

  -- Equal data at the same position still cannot replace a distinct full
  -- category selection. The bundle is definitionally equal but syntactically
  -- distinct, matching the existing exact-selection contract.
  let alternateContext := { context with bundle := (← mkAppM ``id #[context.bundle]) }
  let alternate := { operand with categoryContext := some alternateContext }
  let alternateBindings ← retainServiceInputPaths harness data
    #[(firstPath, operand), (secondPath, alternate)]
  if ← sameServiceRequestForCycle harness first
      { first with serviceInputPaths := some alternateBindings } then
    throwError "equal packets merged distinct complete input occurrences"

  -- An input can itself retain positioned inputs. Compare its actual children,
  -- not its own freshly allocated administrative handles.
  let nestedData ← scopedNode "valueData" #[data]
  let nestedPath : DataOwnership.Path := #[.field "args", .index 0]
  let nestedFirstBindings ← retainServiceInputPaths harness nestedData #[(nestedPath, first)]
  let nestedSecondBindings ← retainServiceInputPaths harness nestedData #[(nestedPath, second)]
  let nestedFirst := { first with
    payload := (← scopedPayload requestValue nestedData)
    serviceInputPaths := some nestedFirstBindings }
  let nestedSecond := { nestedFirst with serviceInputPaths := some nestedSecondBindings }
  unless ← sameServiceRequestForCycle harness nestedFirst nestedSecond do
    throwError "nested handle reallocation hid an identical exact request"

  let legacyFirst := { first with serviceInputPaths := none }
  let legacySecond := { second with serviceInputPaths := none }
  unless (← sameServiceRequestForCycle harness legacyFirst legacySecond) ==
      sameServiceSelection legacyFirst legacySecond do
    throwError "the recursion guard changed legacy unpositioned behavior"
  if ← sameServiceRequestForCycle harness legacyFirst
      { first with serviceInputPaths := some #[] } then
    throwError "an exact empty input scope was merged with legacy packet recovery"

  -- Exercise the actual recursive service boundary. Its guard must run before
  -- this deliberately unpublished operation could reach request preparation.
  let program : Backend.DeferredData := { calls := #[], result := Json.null }
  let reply : ComputationalReply := { data := { json := program.encode }, backend := "unused" }
  let failure ← try
    discard <| completeServiceReply harness trace #[("service-cycle-probe", first)]
      "service-cycle-probe" second reply
    pure none
  catch error => pure (some (Exception.stratum? error, ← error.toMessageData.toString))
  let some (stratum, message) := failure
    | throwError "the deferred service recursion guard accepted an identical exact request"
  unless stratum == some .unavailable do
    throwError "the deferred service recursion guard reached a different failure: {message}"
  logInfo "PASS: exact service recursion ignores handle allocation, retains input positions, and preserves legacy scope"

end
