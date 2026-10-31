/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/-! Engineering controls for private identifier reservation. Arbitrary retained
packets establish no mathematical answer, supplier, or execution receipt. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let some category := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the reservation control has no existing set category"
  let formal := Lean.mkConst ``Nat
  let context ← CategoryContext.ofNamed category formal
  let packet := toJson "same retained packet"
  let original : Wire := {
    form := .diagrams category, payload := .ordinary formal packet
    categoryContext := some context }
  let snapshot : WireSnapshot := {
    form := original.form, payload := .ordinary formal (Backend.resultRef 12)
    presentationIsos := #[], objectIso := none, categoryContext := some context }
  let assembly : IntrinsicAssembly := {
    result := .object context, formal, fragment := { json := packet }
    template := .literal { json := Backend.resultRef 13 } }
  let first := { original with proofSources := [snapshot, snapshot] }
  let second := { original with intrinsicAssembly := some assembly }
  unless first.json == second.json && first.value == second.value &&
      prospectiveReservedContains (Backend.resultRef 12) #[.wire first, .wire second] &&
      prospectiveReservedContains (Backend.resultRef 13) #[.wire first, .wire second] &&
      !prospectiveReservedContains (Backend.resultRef 13) #[.wire first] &&
      prospectiveReservedContains (Backend.resultRef 12) #[.wire first] do
    throwError "equal visible packets collapsed their distinct complete retained contexts"
  unless prospectiveReservedWire first == #[packet, Backend.resultRef 12, Backend.resultRef 12] &&
      prospectiveReservedInvocation (.intrinsic assembly) == #[packet, Backend.resultRef 13] do
    throwError "the public reservation collectors changed their whole JSON roots or duplicate order"

  let mut shared := first
  for _ in [:8] do shared := { original with productComponents := #[shared, shared] }
  unless prospectiveReservedContains (Backend.resultRef 12)
      #[.wire shared, .snapshot snapshot, .wire shared] &&
      !prospectiveReservedContains (Backend.resultRef 14) #[.wire shared] do
    throwError "shared retained nodes changed complete reservation membership"
  let mut sharedJson := Backend.resultRef 15
  for _ in [:8] do sharedJson := Json.arr #[sharedJson, sharedJson]
  unless prospectiveReservedContains (Backend.resultRef 15) #[.json sharedJson] &&
      !prospectiveReservedContains (Backend.resultRef 14) #[.json sharedJson] do
    throwError "shared JSON nodes changed recursive membership"

  for malformed in #[
      Json.mkObj [("ctor", "resultRef"), ("args", Json.arr #[toJson 16]), ("extra", Json.null)],
      Json.mkObj [("ctor", "resultRef"), ("args", Json.arr #[toJson "16"])],
      Json.mkObj [("ctor", "resultRef"), ("args", Json.arr #[toJson 16, toJson 17])],
      Json.mkObj [((Backend.resultRef 16).compress, Json.null)]] do
    unless !prospectiveReservedContains (Backend.resultRef 16) #[.json malformed] do
      throwError "a malformed lookalike or object key invented a canonical reservation"
  let nested := Json.mkObj [("ctor", "resultRef"), ("args", Json.arr #[toJson "wrong"]),
    ("extra", Json.arr #[Backend.resultRef 18])]
  unless prospectiveReservedContains (Backend.resultRef 18) #[.json nested] &&
      !prospectiveReservedContains (Backend.resultRef 16) #[.json nested] do
    throwError "a malformed parent suppressed its nested canonical reference"

  let live ← Harness.empty
  let inspect ← Harness.empty
  let trace ← Trace.new
  let state ← IO.mkRef ({
    reserved := #[.wire first, .wire second, .json nested,
      .json (Backend.resultRef 0), .json (Json.arr #[Backend.resultRef 2])]
    } : ProspectiveData)
  let reader : ProspectiveReader := {
    live, inspect, trace, state
    objectTemplate := fun _ _ _ _ => throwError "reservation unexpectedly observed a template"
    invocation := fun _ _ _ => throwError "reservation unexpectedly invoked a service"
    endpoints := fun _ _ => throwError "reservation unexpectedly interpreted endpoints" }
  let datum ← prospectiveDatum reader formal
  let key : ProspectiveActionKey := {
    operation := "reservation-control", action := formal, input := original
    parameters := #[], parameterOwnership := #[], dependencies := #[], images := #[] }
  let action ← prospectiveActionValue reader key original context false
  let reused ← prospectiveActionValue reader key original context false
  unless datum.json == Backend.resultRef 1 && action.json == Backend.resultRef 3 &&
      reused.json == action.json && (← state.get).nextReference == 4 do
    throwError "the two allocators changed identifier order or allocated an exact action twice"
  unless !prospectiveReservedContains (Backend.resultRef 4) (← state.get).reserved do
    throwError "the fresh-query control was already reserved"
  state.modify fun current => { current with
    reserved := current.reserved ++ #[.json (Backend.resultRef 4)] }
  let next ← prospectiveDatum reader formal
  let final ← state.get
  unless next.json == Backend.resultRef 5 && final.nextReference == 6 &&
      final.objects.map Prod.fst == #[Backend.resultRef 1, Backend.resultRef 3, Backend.resultRef 5] &&
      final.actions.size == 1 && final.occurrences.isEmpty && final.invocations.isEmpty &&
      final.activeInvocations.isEmpty && (← live.actions.get).isEmpty &&
      (← live.results.get).isEmpty && (← live.serviceOperands.get).isEmpty &&
      (← live.invocations.get).isEmpty do
    throwError "a stale reservation query changed future identities or execution tables"
  unless final.containsFuture (Json.arr #[datum.json]) &&
      !final.containsFuture (Backend.resultRef 0) do
    throwError "reserved actual identifiers became allocated private futures"
  logInfo "PASS: complete reservation contexts, shared nodes, exact JSON membership, ordered private identities and fresh queries"
