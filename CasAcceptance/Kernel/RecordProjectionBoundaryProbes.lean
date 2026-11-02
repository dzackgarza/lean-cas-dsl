/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CasCatalogue CasCatalogue.Realize

/-! Engineering controls for explicit public envelopes at structural projection
boundaries. Arbitrary packets establish no mathematical answer or property. -/

private def token (label : String) : Json :=
  Json.mkObj [("ctor", toJson "opaqueData"), ("args", Json.arr #[toJson label])]

run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.subobjects_modules.inclusion")
    | throwError "the existing full-subcategory inclusion is unavailable"
  let scalar ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let action ← mkAppM entry.declaration #[scalar]
  let (bundle, _) ← functorCategoryBundles action
  let context ← CategoryContext.presented { expression := entry.source, bundle }
  let trace ← Trace.new
  withLocalDeclD `selectedSubobject (← CategoryContext.carrier context) fun receiver => do
    let image ← Semantic.objOf action receiver
    let first := DataOwnership.Data.capture (token "equal endpoint bytes") ("first", 31)
    let second := DataOwnership.Data.capture (token "equal endpoint bytes") ("second", 32)
    let callable := DataOwnership.Data.capture (token "stored inclusion") ("map", 33)
    let mapData ← scopedNode "typedMap" #[first, second, callable]
    let packet ← scopedNode "subobject" #[first, second, mapData]
    if let .error message ← ComputationalData.validatePort receiver (← inferType receiver) packet.json then
      throwError "the original complete subobject packet is invalid: {message}"
    if (← exposedRecordData? receiver packet).isSome then
      throwError "the whole subobject envelope was treated as its single stored Arrow"
    let expected ← scopedNode "arrow" #[first, second, mapData]
    for input in #[packet, ← scopedNode "valueData" #[packet]] do
      let some projected ← projectObjectFragment trace entry.source (.functor entry.id)
          action receiver input
        | throwError "the declared inclusion lost its complete exposed Arrow fields"
      unless projected == expected && projected.validate.isOk do
        throwError "the inclusion changed an original field, tag or occurrence supplier"
      if let .error message ← ComputationalData.validatePort image (← inferType image) projected.json then
        throwError "the inclusion's actual output is not valid at its declared Arrow interface: {message}"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the complete set category is unavailable"
  let receiver ← elabTermAndSynthesize
    (← `(CategoryTheory.Core.mk (C := Type 0) (CasCatalogue.Foundation.Objects.fin 2))) none
  let action ← elabTermAndSynthesize (← `(CategoryTheory.Core.inclusion (Type 0))) none
  let actual := DataOwnership.Data.capture (token "original object") ("original", 41)
  let packet ← scopedNode "coreObject" #[actual]
  if (← exposedRecordData? receiver packet).isSome then
    throwError "the complete Core envelope was reinterpreted as its underlying object field"
  let trace ← Trace.new
  -- A supplied descriptor is only the fallback address; the actual complete
  -- mathematical action above independently determines this existing field.
  let some projected ← projectObjectFragment trace sets.expression
      (.functor ⟨"engineering-unused-fallback"⟩) action receiver packet
      (some { json := toJson "unused fallback" })
    | throwError "the explicit Core packet lost its declared original object"
  unless projected == actual do
    throwError "the explicit Core projection changed the actual field or supplier"

run_elab do
  -- A named descriptor may genuinely be an exposed field of a one-field record.
  -- Its complete type, not its JSON tag, distinguishes it from a whole wrapper.
  let wrapper ← elabTermAndSynthesize
    (← `(ULift.up.{0} (α := Type 0) (CasCatalogue.Foundation.Objects.fin 2))) none
  let packet : DataOwnership.Data := {
    json := Json.mkObj [("ctor", toJson "obj.sets.fin"), ("args", Json.arr #[toJson (2 : Nat)])] }
  unless (← exposedRecordData? wrapper packet) == some packet do
    throwError "a correctly typed named object was refused as an actual exposed record field"
  if (← exposedRecordData? wrapper (← scopedNode "coreObject" #[packet])).isSome then
    throwError "a whole Core wrapper supplied an incompatible underlying field"
  logInfo "explicit subobject and Core codecs retain exact fields before record elision"

private def checkNestedCore (outerType : Expr) (owner : Nat) : TermElabM Unit := do
  withLocalDeclD `outer outerType fun outer => do
    let stored ← mkProjection outer `down
    let image ← mkProjection stored `of
    let original := DataOwnership.Data.capture (token "original nested field") ("nested", owner)
    let packet ← scopedNode "coreObject" #[original]
    let some plan ← ComputationalData.recordProjectionPlan? outer image
      | throwError "the independently selected nested projections were not retained"
    let .input path := plan | throwError "the nested projections became a different action"
    unless path.size == 2 && path[0]!.codec == .ordered && path[1]!.codec == .core do
      throwError "the nested path lost the distinct existing record codecs"
    for input in #[packet, ← scopedNode "valueData" #[packet]] do
      let some exposed ← exposedRecordData? outer input
        | throwError "the valid outer record did not expose its Core-valued field"
      let some result ← plan.apply? outer exposed
        | throwError "the nested Core field was not projected through its existing codec"
      unless result == original && result != packet && result.validate.isOk do
        throwError "the nested projection changed the exact original field or its supplier"
      unless (← ComputationalData.validatePort image (← inferType image) result.json).isOk do
        throwError "the selected original field has an incompatible fixed interface"
    -- Opening the retained opaque inner record would require ordinary execution.
    if let some deeper ← ComputationalData.recordProjection ``CategoryTheory.Core.of image then
      let some nestedPlan ← ComputationalData.recordProjectionPlan? outer deeper
        | throwError "the deeper existing Core projection was lost"
      if (← nestedPlan.apply? outer packet).isSome then
        throwError "the nested projection opened a whole opaque inner Core object"

run_elab do
  let first ← elabTermAndSynthesize
    (← `(ULift (CategoryTheory.Core (Type 0)))) none
  checkNestedCore first 51
  let second ← elabTermAndSynthesize
    (← `(ULift (CategoryTheory.Core (CategoryTheory.Core (Type 0))))) none
  checkNestedCore second 61

run_elab do
  let outerType ← elabTermAndSynthesize (← `(Type 0 × Type 0)) none
  withLocalDeclD `outer outerType fun outer => do
    let field ← mkProjection outer `fst
    let image ← mkAppM ``CategoryTheory.Core.mk #[field]
    let first := DataOwnership.Data.capture (token "same constructed field") ("first", 81)
    let second := DataOwnership.Data.capture (token "same constructed field") ("second", 82)
    let packet := DataOwnership.Data.array #[first, second]
    let some plan ← ComputationalData.recordProjectionPlan? outer image
      | throwError "the existing Core constructor's projected field was not retained"
    let some result ← plan.apply? outer packet
      | throwError "the existing Core output codec was not assembled"
    let expected ← scopedNode "coreObject" #[first]
    unless result == expected && result != first && result.validate.isOk do
      throwError "record assembly omitted its Core envelope or changed its exact field owner"

run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.subobjects_modules.inclusion")
    | throwError "the existing complete inclusion is unavailable"
  let scalar ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let action ← mkAppM entry.declaration #[scalar]
  let (bundle, _) ← functorCategoryBundles action
  let context ← CategoryContext.presented { expression := entry.source, bundle }
  let carrier ← exprToSyntax (← CategoryContext.carrier context)
  let outerType ← elabTermAndSynthesize (← `(ULift.{0} $carrier)) none
  withLocalDeclD `outer outerType fun outer => do
    let stored ← mkProjection outer `down
    let some image ← ComputationalData.recordProjection
        ``CategoryTheory.ObjectProperty.FullSubcategory.obj stored
      | throwError "the original refined Arrow field is unavailable"
    let some source ← ComputationalData.recordProjection ``CategoryTheory.Arrow.left image
      | throwError "the original Arrow source field is unavailable"
    let first := DataOwnership.Data.capture (token "same nested endpoint") ("left", 71)
    let second := DataOwnership.Data.capture (token "same nested endpoint") ("right", 72)
    let callable := DataOwnership.Data.capture (token "nested inclusion") ("map", 73)
    let mapData ← scopedNode "typedMap" #[first, second, callable]
    let packet ← scopedNode "subobject" #[first, second, mapData]
    let arrow ← scopedNode "arrow" #[first, second, mapData]
    let some exposed ← exposedRecordData? outer packet
      | throwError "the valid outer record did not retain its refined Arrow field"
    for (selected, expected) in #[(image, arrow), (source, first)] do
      let some plan ← ComputationalData.recordProjectionPlan? outer selected
        | throwError "the nested independently selected Arrow projection was lost"
      let some result ← plan.apply? outer exposed
        | throwError "the nested Arrow codec was not projected"
      unless result == expected && result.validate.isOk do
        throwError "a nested Arrow field changed its original role or occurrence supplier"
  logInfo "nested Core and refined Arrow projections retain exact existing codec fields"
