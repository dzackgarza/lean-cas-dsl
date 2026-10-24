/- Engineering checks of public framing and dispatch addresses. No CAS answers are used. -/
module
import CasCatalogue.ComputationalData
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.ComputationalData
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue

run_elab do
  let state ← registryState
  let ring ← elabTermAndSynthesize (← `(RingCat.of ℤ)) none
  let object ← elabTermAndSynthesize (← `(ModuleCat.of ℤ ℤ)) none
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let opaqueData (token : String) := node "opaqueData" #[toJson token]
  let source := opaqueData "untrusted source object"
  let target := opaqueData "untrusted target object"
  let callable := opaqueData "untrusted defining map"
  let map := Backend.TypedMap.encode ⟨source, target, callable⟩
  let validate := fun (formal : Expr) (data : Json) (accepted : Bool) => do
    let outcome ← ComputationalData.validatePort formal (← inferType formal) data
    unless outcome.isOk == accepted do
      throwError "Arrow record framing disagrees at {← inferType formal}: {repr outcome}"
  validate arrow (node "arrow" #[source, target, map]) true
  validate arrow (node "subobject" #[source, target, map]) false
  for id in #["fun.arrows_modules.kernel", "fun.arrows_modules.cokernel"] do
    let some entry := state.functors.find? (·.id.raw == id)
      | throwError "the declared record fixture is missing"
    let formal ← Semantic.objOf (← mkAppM entry.declaration #[ring]) arrow
    for tag in #["arrow", "subobject"] do
      validate formal (node tag #[source, target, map]) true
      validate formal (node "valueData" #[node tag #[source, target, map]]) true
      validate formal (node tag #[source, target]) false
      validate formal (node tag #[source, target, map, .null]) false
      let wrongSource := Backend.TypedMap.encode ⟨target, target, callable⟩
      let wrongTarget := Backend.TypedMap.encode ⟨source, source, callable⟩
      validate formal (node tag #[source, target, wrongSource]) false
      validate formal (node tag #[source, target, wrongTarget]) false
  let unrelated ← elabTermAndSynthesize (← `((3 : Nat))) none
  for tag in #["arrow", "subobject"] do
    validate unrelated (node tag #[source, target, map]) false
  logInfo "PASS: complete Arrow/kernel/cokernel framing, legacy compatibility, fixed types and endpoint rejection"

run_elab do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let source := node "opaqueData" #[toJson "source"]
  let target := node "opaqueData" #[toJson "target"]
  let argument := node "opaqueData" #[toJson "original point"]
  for inverse in #[false, true] do
    let request : Backend.PresentationInvocation := {
      parameters := #[toJson (3 : Nat)], inverse, source, target, argument }
    let encoded := request.encode
    let .ok decoded := Backend.PresentationInvocation.decode encoded
      | throwError "complete comparison framing was rejected"
    unless decoded.encode == encoded do throwError "comparison data or direction were lost"
  for malformed in #[
      node "presentationApply" #[Json.arr #[], toJson false, source, target],
      node "presentationApply" #[Json.arr #[], toJson false, source, target, argument, .null],
      node "presentationApply" #[Json.mkObj [], toJson false, source, target, argument],
      node "presentationApply" #[Json.arr #[], toJson (0 : Nat), source, target, argument],
      node "presentationApply" #[Json.arr #[], toJson "false", source, target, argument],
      node "apply" #[Json.arr #[], toJson false, source, target, argument]] do
    if (Backend.PresentationInvocation.decode malformed).isOk then
      throwError "malformed comparison framing was accepted"
  let state ← registryState
  unless !state.presentations.isEmpty do throwError "no comparison address fixture is registered"
  for entry in state.presentations do
    let operation := Operation.presentation entry
    let some source := state.objects.find? (·.id == entry.source)
      | throwError "the comparison's registered source is missing"
    let some request := state.form? entry.id.raw
      | throwError "the comparison's public request address is missing"
    unless state.accepts operation request do
      throwError "the comparison's own request address was rejected"
    let endpoints := state.inputAddresses operation (.object source)
    let complete := state.presentationInputAddresses operation (.object source)
    unless complete.contains request.id && endpoints.all complete.contains do
      throwError "the complete request lost its own address or endpoint peers"
    unless !endpoints.contains request.id do
      throwError "an ordinary endpoint gained a complete-request address"
    unless (complete.filter (· == request.id)).size == 1 do
      throwError "the complete-request address was duplicated"
    for other in state.presentations do
      if other.id == entry.id then continue
      let some otherForm := state.form? other.id.raw
        | throwError "another registered comparison has no request form"
      unless !state.accepts operation otherForm do
        throwError "one comparison's request was admitted for another comparison"
  logInfo "PASS: comparison framing, own-address admission, endpoint peers and foreign-comparison rejection"
