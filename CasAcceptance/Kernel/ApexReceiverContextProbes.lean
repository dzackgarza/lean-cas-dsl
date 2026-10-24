module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue CasCatalogue.Realize

/- Engineering controls for selecting the declared interface of a returned apex.
The opaque objects and maps assert no construction law and no leaf is executed. -/
run_elab do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "the public product fixture is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the public set category is absent"
  let action ← Semantic.edgeFunctor state (.classifierForget ClassifierId.setsFinite)
  let first ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.FiniteObjects.finiteFin 2)) none
  let second ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.FiniteObjects.finiteFin 3)) none
  let left ← Semantic.objOf action first
  let right ← Semantic.objOf action second
  let presentation ← mkAppM row.declaration #[left, right]
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let diagram := (← whnfR (← inferType cone)).getAppArgs.back!
  let .ok plan ← StructuredResult.dataPlan row diagram presentation
    | throwError "the product fixture has no complete constructor data plan"
  let wire := fun tag args => Json.mkObj [("ctor", toJson (tag : String)), ("args", Json.arr args)]
  let opaqueData := fun token => wire "opaqueData" #[toJson (token : String)]
  let edge := wire "classifierForget" #[toJson ClassifierId.setsFinite.raw, Json.arr #[]]
  let inputs := #[wire "functorAction" #[edge, opaqueData "first retained object"],
    wire "functorAction" #[edge, opaqueData "second retained object"]]
  let external := fun binder => Id.run do
    let some binding := plan.binders[binder]? | return none
    for role in binding.inputRoles do
      if let .argument index := role then return inputs[index]?
    return none
  let apexData := wire "objectProduct" inputs
  let typed := fun source target token => wire "typedMap" #[source, target, opaqueData token]
  let some declaration := diagram.getAppFn.constName?
    | throwError "the independently selected diagram has no public constructor"
  let diagramData := wire (Codec.label declaration) inputs
  let complete := fun selected => do
    let answer := wire "cone" #[selected,
      typed selected inputs[0]! "first defining map",
      typed selected inputs[1]! "second defining map"]
    StructuredResult.complete row diagram diagramData (.direct answer)
      presentation (fun answer => StructuredResult.validatePlannedData plan answer
        (fun port seen data => ComputationalData.validatePlannedPort plan port seen data external
          ComputationalData.endpointKeys))
  let .ok completed ← complete apexData
    | throwError "the complete computational fixture failed its original framing"
  let context := #[(inputs[0]!, left), (inputs[1]!, right)]
  let original : Wire := {
    form := .limitApex row, payload := .construction completed (.owned "engineering-owner" 31)
    constructionInputs := some (completed.apex, context) }
  let trace ← CasCatalogue.Trace.new
  let actual ← computationalApexReceiver trace original
  unless actual.form.id == (Form.diagrams sets).id && actual.form.category == sets.id &&
      actual.json == apexData && actual.value == original.value &&
      actual.owner? == original.owner? && actual.constructionInputs == original.constructionInputs do
    throwError "the symbolic apex lost its exact category interface, actual data, formal receiver or owner"
  let portable := wire "objectProduct" #[wire "obj.sets.fin" #[toJson (2 : Nat)],
    wire "obj.sets.fin" #[toJson (3 : Nat)]]
  for (selected, owned) in #[(portable, false), (opaqueData "selected apex", true)] do
    let .ok completed ← complete selected
      | throwError "the projected-scope fixture failed its complete original framing"
    let parent := { original with
      payload := .construction completed (.owned "engineering-owner" 31)
      constructionInputs := some (completed.apex, context) }
    let retainedPacket := parent.json
    let actual ← computationalApexReceiver trace parent
    let expectedOwner := if owned then parent.owner? else none
    unless actual.form.id == (Form.diagrams sets).id && actual.json == selected &&
        actual.value == parent.value && actual.owner? == expectedOwner do
      throwError "the selected apex lost an opaque owner or retained an unrelated defining-map owner"
    unless owned || (actual.payload matches .computed _ (.inline _)) do
      throwError "the projected portable apex stopped being computational data"
    unless parent.json == retainedPacket && containsOpaqueData parent.json &&
        parent.owner? == original.owner? do
      throwError "projecting the method receiver discarded the complete owned parent result"
  let unchanged := fun candidate => do
    let actual ← computationalApexReceiver trace candidate
    unless actual.form.id == candidate.form.id && actual.form.category == candidate.form.category &&
        actual.json == candidate.json && actual.value == candidate.value &&
        actual.owner? == candidate.owner? do
      throwError "receiver selection used absent or contradictory context or erased an actual action"
  unchanged { original with constructionInputs := none }
  unchanged { original with constructionInputs := some (left, context) }
  let some symmetric := state.objects.find? (·.id.raw == "obj.groups.symmetric")
    | throwError "the protected foreign-category fixture is absent"
  let foreign ← mkAppM symmetric.declaration #[mkNatLit 3]
  unchanged { original with constructionInputs := some (completed.apex,
    #[(inputs[0]!, foreign), (inputs[1]!, right)]) }
  let some groups := state.categories.find? (·.id == symmetric.category)
    | throwError "the protected foreign category is absent"
  let foreignPacket := wire "cone" #[wire symmetric.id.raw #[toJson (3 : Nat)]]
  let wrongCategory : Wire := {
    form := .diagrams groups
    payload := .computed original.value (.owned "engineering-owner" 31 foreignPacket) }
  unchanged wrongCategory
  let some list := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the protected nonidentity object action is absent"
  let listAction ← Semantic.asFunctor (← instantiateFresh list.declaration)
  let image ← Semantic.objOf listAction original.value
  let descriptor ← edgeDescriptor trace (.functor list.id) listAction
  let residual := { original with
    form := imageForm state (.functor list.id) sets
    payload := forwardPayload original image
      (wire "functorAction" #[descriptor, original.json]) }
  unless (residual.json.getObjValAs? String "ctor").toOption == some "functorAction" do
    throwError "the residual action fixture did not retain its complete computational action"
  if ← withoutModifyingState <| isDefEq residual.value original.value then
    throwError "the residual action fixture no longer changes the full formal receiver"
  unchanged residual
  unchanged { residual with constructionInputs := none }
  logInfo "PASS: complete computed-apex receiver context, exact category, owner and residual action"
