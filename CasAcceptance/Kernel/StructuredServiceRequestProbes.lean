module
import CasCatalogue.StructuredServiceRequest
meta import CasCatalogue.StructuredServiceRequest

/-! Typed preparation controls only. The callback table stands for already
retained runtime operands; no backend answer is mathematical evidence. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.ServiceRequest

meta section

def reference (index : Nat) : Json :=
  Json.mkObj [("ctor", "resultRef"), ("args", Json.arr #[toJson index])]

def datum (name : String) (args : Array Json := #[]) : Json :=
  Json.mkObj [("ctor", toJson name), ("args", Json.arr args)]

def lookupOperand (values : Array Operand) (json : Json) : TermElabM Operand := do
  let .ok ("resultRef", #[index]) := ComputationalData.envelope json
    | throwStratum .malformed "the engineering callback requires an exact retained reference"
  let .ok index := index.getNat?
    | throwStratum .malformed "the engineering callback has a malformed index"
  let some value := values[index]?
    | throwStratum .malformed "the engineering callback has no retained operand"
  return value

def decoderFor (values : Array Operand) (endpoints : Array (Nat × Nat × Nat) := #[]) : Decoder := {
  argument := fun expected json => do
    let actual ← lookupOperand values json
    unless ← withTransparency .all <| isDefEq (← inferType actual.value) expected do
      throwStratum .malformed "the retained operand is outside the required complete type"
    return actual
  object := lookupOperand values
  arrow := lookupOperand values
  endpoint := fun operand source => do
    let some (_, first, second) := endpoints.find? (fun row => row.1 == operand.handle)
      | throwStratum .malformed "the retained callable has no exact endpoint occurrence"
    lookupOperand values (reference (if source then first else second))
  project := fun _ _ _ => throwStratum .noImplementation "no structured projection in this fixture"
  condition := fun expected => do
    let some proof ← Codec.conditionProof expected
      | throwStratum .noImplementation "no original formal condition in this fixture"
    return proof
  declaration := fun name parameters => do
    let operands ← parameters.mapM (lookupOperand values)
    let application ← DirectConstruction.instantiate name (← operands.mapM fun item => exprToSyntax item.value)
    return { application, operands }
}

def mustReject (action : TermElabM α) : TermElabM Unit := do
  let rejected ← try
    discard action
    pure false
  catch error => pure (Exception.stratum? error == some .malformed)
  unless rejected do throwError "malformed complete service data was accepted"

def completeCallableControls (prepared : Prepared) (source target : Json) : TermElabM Unit := do
  let answer := Backend.ComputationalValue.inline (Backend.TypedMap.encode {
    source, target, callable := (Backend.ComputationalValue.opaque "arbitrary-untrusted-callable").encode })
  let .ok none ← prepared.complete answer.encode
    | throwError "a well-framed computational callable was promoted to evidence or rejected"
  let wrong := Backend.ComputationalValue.inline (Backend.TypedMap.encode {
    source, target := datum "obj.sets.fin" #[toJson (2 : Nat)],
    callable := (Backend.ComputationalValue.opaque "arbitrary-untrusted-callable").encode })
  if (← prepared.complete wrong.encode).isOk then
    throwError "a complete callable changed its actual target packet"

run_elab do
  let state ← registryState
  let some entry := state.cells.find? (·.id.raw == "cmp.rings.carrier")
    | throwError "the existing natural comparison is absent"
  let receiver ← elabTermAndSynthesize (← `(RingCat.of Int)) none
  let action ← CellAction.select entry #[] #[] false receiver
  let (source, target) ← CellAction.objects action receiver
  let originalContext : CategoryContext := { expression := action.source, bundle := action.sourceBundle }
  let context : CategoryContext := { expression := action.target, bundle := action.targetBundle }
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let ringData := datum "obj.rings.integers"
  let setData := datum "obj.sets.integers"
  let values : Array Operand := #[
    { value := receiver, data := ringData, handle := 0, context := some originalContext },
    { value := source, data := setData, handle := 1, context := some context },
    { value := target, data := setData, handle := 2, context := some context },
    { value := identity, data := datum "identity" #[setData, setData], handle := 3, context := some context },
    { value := receiver, data := (Backend.ComputationalValue.opaque "different-actual-source").encode,
      handle := 4, context := some originalContext },
    { value := source, data := setData, handle := 5, context := some originalContext }]
  let descriptor : Backend.CellComponent := {
    cell := entry.id.raw, parameters := #[], receiver := reference 0, inverse := false }
  let request : Backend.PointInvocation := {
    operation := entry.componentAddress, parameters := #[Json.arr #[], reference 0, toJson false]
    arrow := descriptor.encode, domain := reference 1, source := reference 1,
    target := reference 2, argument := reference 3 }
  let some input := state.componentForm? entry.componentAddress
    | throwError "the comparison has no published complete input"
  let decoder := decoderFor values #[(3, 1, 1)]
  let some prepared ← StructuredServiceRequest.prepare? decoder (.cellComponent entry #[]) input request.encode
    | throwError "the published component family is not prepared"
  let expected ← mkAppM ``CategoryTheory.CategoryStruct.comp
    #[identity, ← CellAction.component action receiver]
  unless ← withTransparency .all <| isDefEq prepared.result expected do
    throwError "component preparation changed the original complete formal application"
  unless prepared.dependencies.any (·.handle == 0) && prepared.dependencies.any (·.handle == 3) do
    throwError "component preparation lost its exact receiver or generalized argument"
  completeCallableControls prepared setData setData
  mustReject <| StructuredServiceRequest.prepare? decoder (.cellComponent entry #[]) input
    { request with parameters := #[Json.arr #[], reference 4, toJson false] }.encode
  mustReject <| StructuredServiceRequest.prepare? decoder (.cellComponent entry #[]) input
    { request with domain := reference 5 }.encode
  mustReject <| StructuredServiceRequest.prepare? decoder (.cellComponent entry #[]) input
    { request with operation := "meth.cardinality" }.encode
  logInfo "PASS: component complete type, exact repeated data, owner handles, wrong model and operation controls"

run_elab do
  let state ← registryState
  let some entry := state.presentations.find? (·.id.raw == "cmp.f9.translation")
    | throwError "the existing presentation is absent"
  let application ← DirectConstruction.close (← DirectConstruction.instantiate entry.declaration #[])
  let formal ← Semantic.presentationArrow entry application.value false
  let some (source, target) := Language.homEnds? (← inferType formal)
    | throwError "the existing presentation lost its complete endpoints"
  let some row := state.objects.find? (·.id == entry.source) | throwError "missing source row"
  let some category := state.categories.find? (·.id == row.category) | throwError "missing category"
  let context ← CategoryContext.ofNamed category source
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let sourceData := datum entry.source.raw
  let targetData := datum entry.target.raw
  let values : Array Operand := #[
    { value := source, data := sourceData, handle := 0, context := some context },
    { value := target, data := targetData, handle := 1, context := some context },
    { value := identity, data := datum "identity" #[sourceData, sourceData], handle := 2, context := some context }]
  let decoder := decoderFor values #[(2, 0, 0)]
  let request : Backend.PresentationInvocation := {
    parameters := #[], inverse := false, source := reference 0, target := reference 1, argument := reference 2 }
  let some input := state.form? entry.id.raw | throwError "missing complete comparison input"
  let some prepared ← StructuredServiceRequest.prepare? decoder (.presentation entry) input request.encode
    | throwError "the published presentation family is not prepared"
  let expected ← mkAppM ``CategoryTheory.CategoryStruct.comp #[identity, formal]
  unless ← withTransparency .all <| isDefEq prepared.result expected do
    throwError "presentation preparation changed its selected formal direction"
  completeCallableControls prepared sourceData targetData
  mustReject <| StructuredServiceRequest.prepare? decoder (.presentation entry) input
    { request with source := reference 1 }.encode
  logInfo "PASS: presentation selected direction, complete endpoints and untrusted callable controls"

run_elab do
  let state ← registryState
  let some entry := state.functor? FunctorId.modulesReindex
    | throwError "the existing family reindex action is absent"
  let some modules := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the existing module fibre is absent"
  let receiver ← elabTermAndSynthesize
    (← `(ModuleCat.of (RingCat.of (ZMod 4)) (ZMod 4))) none
  let base ← elabTermAndSynthesize
    (← `(RingCat.ofHom (Int.castRingHom (ZMod 4)))) none
  let sourceContext ← CategoryContext.ofNamed modules receiver
  let plan ← ReindexAction.select entry #[← exprToSyntax base] base sourceContext
  let (formal, source, target) ← ReindexAction.cartesian plan receiver
  let carrier ← CategoryContext.carrier plan.total
  let dictionary ← CategoryContext.dictionary plan.total
  let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct #[some carrier, some dictionary]
  let identity ← mkAppOptM ``CategoryTheory.CategoryStruct.id #[some carrier, some categoryStructure, some source]
  let baseData := (Backend.ComputationalValue.opaque "retained-original-base-map").encode
  let receiverData := (Backend.ComputationalValue.opaque "retained-module-four").encode
  let sourceData := (Backend.ComputationalValue.opaque "retained-cartesian-source").encode
  let targetData := (Backend.ComputationalValue.opaque "retained-cartesian-target").encode
  let values : Array Operand := #[
    { value := base, data := baseData, handle := 0 },
    { value := receiver, data := receiverData, handle := 1, context := some sourceContext },
    { value := source, data := sourceData, handle := 2, context := some plan.total },
    { value := target, data := targetData, handle := 3, context := some plan.total },
    { value := identity, data := datum "identity" #[sourceData, sourceData], handle := 4,
      context := some plan.total },
    { value := base, data := (Backend.ComputationalValue.opaque "different-base-occurrence").encode, handle := 5 }]
  let decoder := decoderFor values #[(4, 2, 2)]
  let descriptor : Backend.CartesianMap := {
    reindex := entry.id.raw, parameters := #[reference 0], receiver := reference 1 }
  let request : Backend.PointInvocation := {
    operation := entry.cartesianAddress, parameters := #[Json.arr #[reference 0], reference 1]
    arrow := descriptor.encode, domain := reference 2, source := reference 2,
    target := reference 3, argument := reference 4 }
  let some input := state.cartesianForm? entry.cartesianAddress | throwError "missing cartesian input"
  let some prepared ← StructuredServiceRequest.prepare? decoder (.cartesian entry) input request.encode
    | throwError "the published cartesian family is not prepared"
  let expected ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
    #[some carrier, some categoryStructure, some source, some source, some target, some identity, some formal]
  unless ← withTransparency .all <| isDefEq prepared.result expected do
    throwError "cartesian preparation changed the original selected base morphism"
  unless prepared.dependencies.any (·.handle == 0) && prepared.dependencies.any (·.handle == 1) do
    throwError "cartesian preparation lost the actual base map or receiver"
  completeCallableControls prepared sourceData targetData
  mustReject <| StructuredServiceRequest.prepare? decoder (.cartesian entry) input
    { request with parameters := #[Json.arr #[reference 5], reference 1] }.encode
  logInfo "PASS: cartesian selected base map, fibre, repeated data and complete callable controls"

end
