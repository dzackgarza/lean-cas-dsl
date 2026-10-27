/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for transparent endpoint inventories. The existing
product-swap Iso supplies the non-definitional presentation. Opaque bodies are
arbitrary data-flow witnesses: these checks establish no mathematical answer,
comparison law, new registration, or backend execution. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.InventoryPresentationReuseProbes
meta section

private def opaque (label : String) (owner : DataOwnership.Owner) : DataOwnership.Data :=
  let json := Json.mkObj [("ctor", toJson "opaqueData"), ("args", Json.arr #[toJson label])]
  { json, ownership := DataOwnership.capture json owner }

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the inventory control lost the accepted set category"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the inventory control lost the accepted finite-object declaration"
  let trace ← Trace.new
  let harness ← Harness.empty
  let X ← Semantic.object finite #[← `(2)] (some trace)
  let Y ← Semantic.object finite #[← `(3)] (some trace)
  let semantic ← mkAppM ``Prod #[X, Y]
  let actual ← mkAppM ``Prod #[Y, X]
  if ← withoutModifyingState (withTransparency .all <| isDefEq semantic actual) then
    throwError "the inventory control lost its non-definitional presentation"
  let context ← CategoryContext.ofNamed sets semantic
  let semanticWire ← realizeEndpoint harness trace "the original inventory endpoint" semantic
  let actualWire ← realizeEndpoint harness trace "the represented inventory endpoint" actual
  let comparison ← mkAppM ``Equiv.toIso #[← mkAppM ``Equiv.prodComm #[X, Y]]
  let makeMap := fun (formal : Expr) (source target : Wire) (body : DataOwnership.Data) => do
    let data ← scopedNode "typedMap" #[source.fragment, target.fragment, body]
    let wire : Wire := {
      form := .canonicalMorphism sets, payload := (← scopedPayload formal data),
      categoryContext := some context, callableObserved := true, morphismFramed := true }
    retainCallableEndpoints wire source target context
  let forwardBody := opaque "original forward body" ("inventory-forward", 71)
  let backwardBody := opaque "original backward body" ("inventory-backward", 72)
  let forward ← makeMap (← mkAppM ``CategoryTheory.Iso.hom #[comparison])
    semanticWire actualWire forwardBody
  let backward ← makeMap (← mkAppM ``CategoryTheory.Iso.inv #[comparison])
    actualWire semanticWire backwardBody
  let original : Wire := {
    form := .diagrams sets, payload := (← scopedPayload semantic actualWire.fragment),
    categoryContext := some context, objectObserved := true,
    objectIso := some (← mkAppM ``CategoryTheory.Iso.symm #[comparison]) }
  let original ← retainEndpointPresentationMaps original context comparison forward backward
  let inventory ← endpointInventoryFragment actualWire.fragment
  let data ← scopedNode "finiteData" #[original.fragment, inventory]
  if let .error message ← ComputationalData.validatePort actual (← inferType actual) data.json then
    throwError "the existing inventory codec rejected its complete descriptor: {message}"
  let enriched ← liftEndpointOperand original context data
  unless enriched.fragment == data && enriched.objectIso == original.objectIso do
    throwError "inventory enrichment changed the selected object or complete packet"
  let some assembly ← currentIntrinsicAssembly? enriched
    | throwError "the inventory view lost its original typed descriptor"
  let .ctor "finiteData" #[.retained (.wire .object child), _] := assembly.template
    | throwError "the inventory view has no transparent typed descriptor child"
  unless sameCompleteWireContext child original do
    throwError "the inventory view discarded the original complete producer"
  let some presentation := enriched.endpointPresentation
    | throwError "the inventory view discarded its accepted nonidentity presentation"
  unless presentation.comparison == comparison && presentation.namedRefinement.isNone do
    throwError "the inventory view copied a stale producer or selected a new comparison"
  let represented ← endpointValidationView enriched context
  unless represented.value == actualWire.value && represented.fragment == data do
    throwError "the inventory view lost the actual full endpoint interface"
  let (newForward, newBackward) ← endpointPresentationMaps enriched context presentation
  let (forwardSource, forwardTarget) ← liftStageEndpoints newForward context
  let (backwardSource, backwardTarget) ← liftStageEndpoints newBackward context
  unless sameCompleteWireContext forwardSource semanticWire &&
      sameCompleteWireContext backwardTarget semanticWire &&
      sameCompleteWireContext forwardTarget represented &&
      sameCompleteWireContext backwardSource represented do
    throwError "inventory framing changed a selected comparison endpoint occurrence"
  unless (← checkedFragment (newForward.fragment.project #[.field "args", .index 2])) == forwardBody &&
      (← checkedFragment (newBackward.fragment.project #[.field "args", .index 2])) == backwardBody do
    throwError "inventory framing changed a returned comparison body or its supplier"
  checkLiftFactorMapEndpoints context newForward semanticWire represented
  checkLiftFactorMapEndpoints context newBackward represented semanticWire
  unless sameCompleteWireContext (← liftEndpointOperand enriched context enriched.fragment) enriched do
    throwError "an unchanged inventory view did not reuse its exact occurrence"

  -- A logical map scope must switch to the accepted actual full Hom before
  -- checking the complete frame and its unchanged opaque map body.
  let identity ← identityAtContext context semantic
  let raw : Wire := {
    form := .canonicalMorphism sets,
    payload := (← scopedPayload identity (opaque "original logical map" ("inventory-map", 73))),
    categoryContext := some context }
  let framed ← presentMorphism raw enriched enriched (some context)
    (some (some newBackward, some newForward))
  let framed ← captureCompleteCallableWith liftStageEndpoints framed context
  checkLiftFactorMapEndpoints context framed enriched enriched

  -- A pending comparison retains its original executable child. Its returned
  -- complete map may introduce another transparent frame, which is adapted at
  -- observation time rather than projected using an obsolete wrapper depth.
  let pending := { forward with
    payload := (← recipePayload forward.value forward.fragment), callableObserved := false }
  let pendingView ← captureInventoryMapEndpoints context pending semanticWire represented
  unless !pendingView.completedData do
    throwError "capturing an inventory frame claimed the pending comparison had executed"
  let newBody := opaque "later nested callable body" ("inventory-forward", 71)
  let nested ← scopedNode "typedMap" #[semanticWire.fragment, actualWire.fragment, newBody]
  let returned ← makeMap forward.value semanticWire actualWire nested
  let observations ← IO.mkRef (0 : Nat)
  let observe := fun (role : ActionDataRole) (wire : Wire) => do
    if role == .retained || (role == .map && wire.completedData) then return wire
    unless role == .map && sameCompleteWireContext wire pending do
      throwError "the inventory view demanded another producer or endpoint"
    observations.modify (· + 1)
    return returned
  let some pendingAssembly ← currentIntrinsicAssembly? pendingView
    | throwError "the pending inventory view omitted its current producer"
  let observed ← observeIntrinsicAssemblyWith observe liftStageEndpoints harness
    pendingView pendingAssembly
  unless (← observations.get) == 1 && observed.completedData do
    throwError "the pending inventory view did not observe exactly its original callable"
  let .ok outer := Backend.TypedMap.decode observed.json
    | throwError "the observed inventory view omitted its complete frame"
  let .ok inner := Backend.TypedMap.decode outer.callable
    | throwError "the observed inventory view discarded the later transparent frame"
  unless outer.source == semanticWire.json && inner.source == semanticWire.json &&
      outer.target == represented.json && inner.target == represented.json &&
      (← checkedFragment (observed.fragment.project
        #[.field "args", .index 2, .field "args", .index 2])) == newBody do
    throwError "the observed inventory view changed a returned body, supplier or endpoint"
  checkLiftFactorMapEndpoints context observed semanticWire represented
  let some completedAssembly ← currentIntrinsicAssembly? observed
    | throwError "the completed inventory view lost its current typed child"
  let reused ← observeIntrinsicAssemblyWith observe liftStageEndpoints harness
    observed completedAssembly
  unless sameCompleteWireContext reused observed && (← observations.get) == 1 do
    throwError "reusing a completed inventory frame replaced or re-observed its original child"

  -- Equal token bytes from another supplier are not an inventory relation.
  let descriptor := opaque "same descriptor bytes" ("inventory-owner-a", 81)
  let other := opaque "same descriptor bytes" ("inventory-owner-b", 82)
  let changed ← scopedNode "finiteData" #[other, { json := Json.arr #[] }]
  let rejected ← try
    checkInventoryEndpointData descriptor changed
    pure false
  catch error =>
    unless Exception.stratum? error == some .malformed do throw error
    pure true
  unless rejected do
    throwError "an inventory view replaced its descriptor's original supplier"
  let changed ← scopedNode "finiteData" #[enriched.fragment, inventory]
  let rejected ← try
    checkInventoryEndpointData enriched.fragment changed
    pure false
  catch error =>
    unless Exception.stratum? error == some .malformed do throw error
    pure true
  unless rejected do
    throwError "an inventory view replaced an already supplied inventory"
  unless (← harness.actions.get).isEmpty && (← harness.replies.get).isEmpty do
    throwError "transparent inventory adaptation dispatched an unrelated computation"

end
end CasCatalogue.InventoryPresentationReuseProbes
