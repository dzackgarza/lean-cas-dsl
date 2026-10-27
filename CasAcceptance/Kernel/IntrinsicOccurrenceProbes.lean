/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for intrinsic child occurrences. Existing categorical
identities and composition fix each formal value. Deliberately different valid
computational packets distinguish occurrences; none is a mathematical oracle or
an assertion about an implementation's arithmetic answers. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.IntrinsicOccurrenceProbes
meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def compositionControl (contextual wrapped : Bool) : TermElabM Unit := do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the intrinsic occurrence control lost the accepted set category"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the intrinsic occurrence control lost the finite-object declaration"
  let trace ← Trace.new
  let h ← Harness.empty
  let object ← Semantic.object finite #[← `(2)] (some trace)
  let context ← CategoryContext.ofNamed sets object
  let endpoint ← realizeEndpoint h trace "the original intrinsic endpoint" object
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let signature ← inferType identity
  let first ← mkExpectedTypeHint identity signature
  let second ← mkExpectedTypeHint first signature
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[first, second]
  Trace.record (some trace) composite (if contextual then
    .contextualComposition context first second object object object
    else .morphismComposition sets.id first second object object object)
  let graph := fun (a b : Nat) => Json.arr #[
    Json.arr #[toJson (0 : Nat), toJson a], Json.arr #[toJson (1 : Nat), toJson b]]
  let packet := fun (a b : Nat) => Backend.TypedMap.encode {
    source := endpoint.json, target := endpoint.json, callable := graph a b }
  let original := fun (formal : Expr) (a b : Nat) => ({
    form := Form.canonicalMorphism sets
    payload := WirePayload.computed formal (.inline (packet a b))
    categoryContext := some context, callableObserved := true } : Wire)
  let firstOriginal := original first 0 1
  let secondOriginal := original second 0 0
  h.results.modify (·.insert object endpoint |>.insert first firstOriginal |>.insert second secondOriginal)
  let selected ← realizeUnobserved h trace "the original intrinsic composition" composite
  let (formal, selected) ← if wrapped then do
    let formal ← (Language.callableMap sets object object composite).run { trace := some trace }
    h.results.modify (·.insert composite selected)
    pure (formal, ← realizeUnobserved h trace "the original callable wrapper" formal)
  else pure (composite, selected)
  unless (← h.actions.get).isEmpty && (← h.replies.get).isEmpty do
    throwError "capturing an intrinsic assembly started a computational port"
  -- Every replacement has the same independently selected formal value and
  -- complete Hom. It is still a different actual computational occurrence.
  h.results.modify (·.insert first (original first 1 0) |>.insert second (original second 1 1))
  if wrapped then h.results.modify (·.insert composite (original composite 1 0))
  let observed ← realizeArrowObservation h trace selected
  unless observed.fragment == selected.fragment do
    throwError "an intrinsic callable replaced its retained child occurrences from the cache"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType observed.value) (← inferType formal) <&&>
        isDefEq observed.value formal) do
    throwError "observing an intrinsic callable changed its complete formal value"
  let reused ← realizeArrowObservation h trace observed
  unless reused.fragment == observed.fragment && (← h.actions.get).isEmpty &&
      (← h.replies.get).isEmpty do
    throwError "reusing an intrinsic callable changed an occurrence or started a port"

run_elab compositionControl false false
run_elab compositionControl true false
run_elab compositionControl true true

-- An identity is intrinsic computation, but its selected object may be a pending
-- declared action. Explicit observation must materialize that exact object even
-- when the harness's ambient demand flag remains false.
run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the intrinsic identity control lost its accepted action"
  let some sourceRow := state.objects.find? (·.id.raw == "obj.linear_orders.naturals")
    | throwError "the intrinsic identity control lost its source object"
  let some sourceCategory := state.categories.find? (·.id == sourceRow.category)
    | throwError "the intrinsic identity control lost its source category"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the intrinsic identity control lost its target category"
  let trace ← Trace.new
  let source ← Semantic.object sourceRow #[] (some trace)
  let sourceContext ← CategoryContext.ofNamed sourceCategory source
  let (image, _) ← Semantic.applyRegisteredFunctor entry source #[] (some trace)
  let context ← CategoryContext.ofNamed sets image
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[image]
  Trace.record (some trace) identity (.contextualIdentity context image)
  let supplied := node "obj.linear_orders.integers" #[]
  let original : Wire := {
    form := .object sourceRow, payload := .computed source (.inline supplied)
    categoryContext := some sourceContext }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{ name := "intrinsic-identity-probe", command := "python3"
      args := #["probe_functor_execution.py", "action", entry.id.raw] }]
    registrations := #[{ operation := entry.id.raw, input := entry.inputAddress
      backend := "intrinsic-identity-probe" }] }
  let calls ← IO.mkRef #[]
  let h ← Harness.ofManifest root manifest
  let h := { h with dispatches := some calls }
  unless h.rejected.isEmpty && h.admitted.size == 1 && !h.demandObjectActions do
    throwError "the intrinsic identity control changed its one action or explicit-demand setup"
  try
    h.results.modify (·.insert source original)
    let pending ← realizeUnobserved h trace "the retained intrinsic identity" identity
    unless (← calls.get).isEmpty do
      throwError "forming an intrinsic identity executed its selected object action"
    h.results.modify (·.insert source { original with
      payload := .computed source (.inline (node "obj.linear_orders.naturals" #[])) })
    let observed ← realizeArrowObservation h trace pending
    let events ← calls.get
    unless events.size == 1 do
      throwError "an intrinsic identity failed to observe its retained object action"
    let .ok request := events[0]!.getObjVal? "request"
      | throwError "the intrinsic identity lost its actual object-action request"
    unless (request.getObjVal? "receiver").toOption == some supplied do
      throwError "an intrinsic identity replaced its retained object occurrence from the cache"
    let receipts ← h.actions.get
    let #[receipt] := receipts
      | throwError "the intrinsic identity lost its exact object-action receipt"
    let expected ← scopedNode "identity" #[receipt.result.fragment, receipt.result.fragment]
    unless observed.fragment == expected do
      throwError "the intrinsic identity discarded an actual returned endpoint or supplier"
    let reused ← realizeArrowObservation h trace observed
    unless reused.fragment == observed.fragment && (← calls.get).size == 1 do
      throwError "reusing the observed intrinsic identity replayed its object action"
  finally h.stop

end
end CasCatalogue.IntrinsicOccurrenceProbes
