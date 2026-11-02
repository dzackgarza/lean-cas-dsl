/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! A whole opaque reply keeps the endpoint occurrences of its actual
invocation. An equal formal cache key is not an endpoint field of that reply.
The process returns only arbitrary ownership witnesses; no map's mathematical
answer or finite-set cardinality is asserted here. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Realize

run_elab do
  let state ← registryState
  let some row := state.morphisms.find? (·.id.raw == "mor.sets.fin_rev")
    | throwError "the existing complete callable is absent"
  let some sets := state.categories.find? (·.id == row.category)
    | throwError "the complete callable's category is absent"
  let trace ← Trace.new
  let formal ← elabTermAndSynthesize (← `($(mkCIdent row.declaration) 4)) none
  let some (source, target) := Language.homEnds? (← inferType formal)
    | throwError "the selected callable has no complete signature"
  Semantic.namedMorphism row formal (some trace)
  let context ← CategoryContext.ofNamed sets source
  let node := fun (size : Nat) => Json.mkObj [
    ("ctor", "obj.sets.fin"), ("args", Json.arr #[toJson size])]
  let original : Wire := {
    form := .diagrams sets, payload := .computed source (.inline (node 7)),
    categoryContext := some context }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "returned-callable-probe", command := "python3",
      args := #["probe_owned_callable.py", "--materialize-invocation", row.id.raw] }]
    registrations := #[{
      operation := row.id.raw, input := row.id.raw, backend := "returned-callable-probe" }] }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  let harness := { harness with dispatches := some calls }
  unless harness.rejected.isEmpty && harness.admitted.size == 1 do
    throwError "the existing whole-callable interface was not admitted"
  try
    harness.results.modify (·.insert source original |>.insert target
      { original with payload := .computed target (.inline original.json) })
    let descriptor ← realizeUnobserved harness trace "the complete callable descriptor" formal
    let actual ← realizeArrowObservation harness trace descriptor
    unless actual.owner?.isSome && (← calls.get).size == 1 do
      throwError "the whole callable did not produce its actual owned reply"
    let .ok request := (← calls.get)[0]!.getObjVal? "request"
      | throwError "the whole callable lost its actual invocation"
    let .ok invocation := Backend.PointInvocation.decode request
      | throwError "the whole callable changed its declared complete request"
    unless invocation.source == original.json && invocation.target == original.json do
      throwError "the whole callable did not use the original selected endpoint packets"
    harness.results.modify (·.insert source
      { original with payload := .computed source (.inline (node 97)) } |>.insert target
      { original with payload := .computed target (.inline (node 97)) })
    let left ← actionMapEndpoint harness trace actual (some context) source true
    let right ← actionMapEndpoint harness trace actual (some context) target false
    unless left.fragment == original.fragment && right.fragment == original.fragment &&
        left.owner?.isNone && right.owner?.isNone do
      throwError "a returned whole callable replaced its invocation endpoints from the formal cache"
    let reusedLeft ← realizeCallableEndpoint harness trace actual source true (some context)
    let reusedRight ← realizeCallableEndpoint harness trace actual target false (some context)
    unless reusedLeft.fragment == original.fragment && reusedRight.fragment == original.fragment &&
        (← calls.get).size == 1 do
      throwError "subsequent callable framing replaced an actual endpoint or replayed the reply"
    if let some path ← IO.getEnv "CAS_RETURNED_CALLABLE_REPORT" then
      IO.FS.writeFile path (Json.mkObj [
        ("purpose", "Returned callable endpoint engineering control; no mathematical verdict"),
        ("formal", toJson (reprStr formal)), ("dispatches", Json.arr (← calls.get)),
        ("actual", actual.json), ("source", left.json), ("target", right.json)]).compress
  finally harness.stop
