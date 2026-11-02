/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! An intrinsic Arrow record retains a complete map already framed at its
selected endpoint presentations. Its later observation must preserve that frame
exactly once, even after an unrelated equal formal endpoint enters the cache.
The existing product-swap comparison is Mathlib's; no mathematical answer or
semantic registration is supplied by this engineering control. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted set category is absent"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the accepted finite-object declaration is absent"
  let trace ← Trace.new
  let harness ← Harness.empty
  let X ← Semantic.object finite #[← `(2)] (some trace)
  let Y ← Semantic.object finite #[← `(3)] (some trace)
  let source ← mkAppM ``Prod #[X, Y]
  let presentation ← mkAppM ``Prod #[Y, X]
  let context ← CategoryContext.ofNamed sets source
  let semanticWire ← realizeEndpoint harness trace "the original Arrow endpoint" source
  let presentationWire ← realizeEndpoint harness trace "the selected endpoint presentation" presentation
  let comparison ← mkAppM ``Equiv.toIso #[← mkAppM ``Equiv.prodComm #[X, Y]]
  -- The portable empty graph is an arbitrary framing witness. No graph
  -- totality, map equality, or mathematical answer is inferred from it.
  let comparisonData : DataOwnership.Data := { json := Json.arr #[] }
  let forward ← scopedNode "typedMap"
    #[semanticWire.fragment, presentationWire.fragment, comparisonData]
  let backward ← scopedNode "typedMap"
    #[presentationWire.fragment, semanticWire.fragment, comparisonData]
  let endpoint : Wire := {
    form := .diagrams sets,
    payload := (← scopedPayload source presentationWire.fragment),
    categoryContext := some context,
    objectIso := some (← mkAppM ``CategoryTheory.Iso.symm #[comparison]),
    endpointPresentation := some {
      comparison, forward := forward.json, backward := backward.json,
      forwardOwnership := forward.ownership, backwardOwnership := backward.ownership } }
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let raw : Wire := {
    form := .canonicalMorphism sets,
    payload := .computed identity (.inline (Json.arr #[])),
    categoryContext := some context }
  let framed ← presentMorphism raw endpoint endpoint (some context)
  unless framed.morphismFraming.isSome && framed.fragment != raw.fragment do
    throwError "the Arrow framing fixture lost its nonidentity selected comparison"
  let arrow ← instantiateMVars (← mkAppOptM ``CategoryTheory.Arrow.mk
    #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
      some source, some source, some identity])
  Trace.record (some trace) arrow (.contextualArrow context identity source source)
  harness.results.modify (·.insert source endpoint |>.insert identity framed)
  let descriptor ← realizeUnobserved harness trace "the already framed complete Arrow" arrow
  let expected ← scopedNode "arrow" #[endpoint.fragment, endpoint.fragment, framed.fragment]
  unless descriptor.fragment == expected do
    throwError "forming the complete Arrow changed its original endpoint framing"
  harness.results.modify (·.insert source semanticWire |>.insert identity raw)
  let observed ← realizeObjectObservation harness trace descriptor
  unless observed.fragment == expected do
    throwError "observing an unchanged Arrow map replaced its retained endpoints or applied its comparison twice"
  let reused ← realizeObjectObservation harness trace observed
  unless reused.fragment == expected && (← harness.actions.get).isEmpty do
    throwError "reusing an already framed Arrow changed its data or executed a new action"
