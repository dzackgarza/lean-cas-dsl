/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import LeanCategories.Catalogue.Semantics
import Mathlib.Algebra.Algebra.Bilinear

/-! Engineering checks of accepted generic actions and retained computational interfaces.
The opaque output fields below assert no mathematical answers or categorical laws. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue

run_elab do
  let state ← registryState
  let some cell := state.cells.find? (·.id.raw == "cmp.rings.carrier")
    | throwError "the accepted independent comparison is missing"
  let original := Lean.mkConst ``CasCatalogue.Algebra.NamedRings.ringIntegers
  for constructors in #[#[], #[ConstructorId.arrow], #[ConstructorId.core],
      #[ConstructorId.arrow, ConstructorId.core], #[ConstructorId.core, ConstructorId.arrow]] do
    let mut receiver := original
    for constructor in constructors.reverse do
      receiver ← if constructor == ConstructorId.core then
        mkAppM ``CategoryTheory.Core.mk #[receiver]
      else do
        mkAppM ``CategoryTheory.Arrow.mk
          #[← mkAppM ``CategoryTheory.CategoryStruct.id #[receiver]]
    let selected ← CellAction.select cell #[] constructors false receiver
    let inverse ← CellAction.select cell #[] constructors true receiver
    let (left, right) ← CellAction.objects selected receiver
    let (inverseLeft, inverseRight) ← CellAction.objects inverse receiver
    unless ← isDefEq left inverseRight <&&> isDefEq right inverseLeft do
      throwError "the inverse component changed the complete selected endpoints"
    for action in #[selected, inverse] do
      let component ← CellAction.component action receiver
      unless !component.hasMVar && !component.hasLevelMVar && (← isTypeCorrect component) do
        throwError "a constructed component lost its complete declaration parameters"
      unless (component.find? (·.isConstOf cell.declaration)).isSome do
        throwError "the derived component discarded its accepted comparison declaration"
      let (sourceMap, targetMap) ← CellAction.maps action
        (← mkAppM ``CategoryTheory.CategoryStruct.id #[receiver])
      unless (← isTypeCorrect sourceMap) && (← isTypeCorrect targetMap) do
        throwError "a component discarded an endpoint functor's full map action"
    let address := cell.componentAddress constructors
    let some (accepted, actualPath) := state.component? address
      | throwError "a canonical component address was not admitted"
    unless accepted.id == cell.id && actualPath == constructors do
      throwError "component admission lost its exact constructor path"
  let refused ← try
    discard <| CellAction.select { cell with invertible := false } #[] #[] true original
    pure false
  catch _ => pure true
  unless refused do throwError "an unregistered inverse became component authority"

run_elab do
  let state ← registryState
  let some construction := state.constructions.find? (·.id.raw == "con.automorphisms")
    | throwError "the accepted dependent construction is missing"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the selected category is missing"
  let selectedCategory ← elabTermAndSynthesize (← `(LeanCategories.Foundation.Mathlib.Sets.{0})) none
  let source ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let other ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 3)) none
  let coreSource ← mkAppM ``CategoryTheory.Core.mk #[source]
  let coreOther ← mkAppM ``CategoryTheory.Core.mk #[other]
  let parameters := #[← exprToSyntax selectedCategory]
  let selected ← DirectConstruction.select construction parameters coreSource
  let object ← DirectConstruction.obj selected coreSource
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[coreSource]
  let mapped ← DirectConstruction.map selected coreSource coreSource identity
  unless ← isDefEq (← inferType mapped) (← DirectConstruction.homAt selected true object object) do
    throwError "the direct construction map changed its selected image endpoints"
  let refused ← try
    discard <| DirectConstruction.map selected coreSource coreOther identity
    pure false
  catch _ => pure true
  unless refused do throwError "a construction map accepted a different original endpoint"
  let some input := state.constructionForm? construction.inputAddress
    | throwError "the construction omitted its declared input address"
  let some operation := state.operation? construction.mapAddress
    | throwError "the construction omitted its map operation"
  unless (state.rejects operation input).isNone &&
      (state.rejects operation (.diagrams sets)).isSome do
    throwError "construction admission ignored its complete invocation schema"

run_elab do
  let state ← registryState
  let some row := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "the accepted dependent lift is missing"
  let source ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ (ℤ × ℤ) ℤ))) none
  let domain ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ ℤ ℤ))) none
  let evidence ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.Kernels.forgetMonoLift ℤ ℤ)) none
  let evidenceType ← whnfR (← inferType evidence)
  let action := evidenceType.getAppArgs[4]!
  let ambient ← Semantic.objOf action source
  let inclusion ← mkAppM ``CategoryTheory.CategoryStruct.id #[ambient]
  let monic ← synthInstance (← mkAppM ``CategoryTheory.Mono #[inclusion])
  let plan ← SelectedLift.fromEvidence row evidence source inclusion monic
  unless plan.parameters.size == 2 && plan.ports.size == 4 do
    throwError "the lift omitted its selected evidence-family parameters or output fields"
  for port in plan.ports do
    unless !port.hasMVar && !port.hasLevelMVar && (← isTypeCorrect port) do
      throwError "a selected lift field is not a complete independent formal value"
  let cone ← elabTermAndSynthesize
    (← `(LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.homMk
      (L := $(← exprToSyntax domain)) (M := $(← exprToSyntax source))
      0 (fun _ _ => rfl))) none
  let baseMap ← Semantic.mapOf action cone
  let proof ← mkAppM ``Eq.symm #[← mkAppM ``CategoryTheory.Category.comp_id #[baseMap]]
  let #[factorStep] ← SelectedLift.factors #[plan] baseMap cone proof
    | throwError "a selected factor lost its complete stage"
  let some (actualDomain, actualTarget) := Language.homEnds? (← inferType factorStep.factor)
    | throwError "a selected factor lost its categorical type"
  unless ← isDefEq actualDomain domain <&&> isDefEq actualTarget plan.ports[0]! do
    throwError "the factor changed its original generalized domain or actual lifted object"
  let sourceEquation ← SelectedLift.factorSourceEquation plan baseMap cone proof
  unless ← Decide.kernelAccepts (← inferType sourceEquation) sourceEquation do
    throwError "the next factor stage lacks its accepted source equation"
  let trace ← Trace.new
  let inner ← SelectedLift.innerEdge state row
  let actionData ← Realize.edgeDescriptor trace inner plan.action
  let data (label : String) := Json.mkObj [("ctor", "opaqueData"),
    ("args", Json.arr #[toJson label])]
  let original := data "original source object"
  let lifted := data "actual returned lifted object"
  let baseApex := data "actual original base apex"
  let image := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[actionData, lifted])]
  let typed (source target arrow : Json) := Json.mkObj [("ctor", "typedMap"),
    ("args", Json.arr #[source, target, arrow])]
  let fields := #[lifted, typed lifted original (data "actual inclusion"),
    typed image baseApex (data "actual forward"), typed baseApex image (data "actual backward")]
  let base := Json.mkObj [("ctor", "subobject"),
    ("args", Json.arr #[baseApex, data "original image ambient", data "original base inclusion"])]
  if let .error message ← LiftedSubobjectData.validateSelectionPrefix
      plan actionData original base fields then
    throwError "the complete selected computation was rejected: {message}"
  let execution : Realize.LiftExecution := {
    selections := #[plan]
    actions := #[actionData]
    parameters := #[#[]]
    sources := #[original]
    bases := #[base]
    outputs := #[fields] }
  let harness ← Realize.Harness.empty
  Realize.cacheLiftFields harness execution (some ("probe", 19))
  for index in [:4] do
    let formal ← SelectedLift.port #[plan] index
    let retained ← Realize.realize harness trace "an actual retained lift field" formal
    unless retained.owner? == some ("probe", 19) do
      throwError "a selected lift field discarded its opaque owning session"
    unless retained.json == (← Realize.liftProjectionData execution index) do
      throwError "a selected lift field replaced its actual returned data"
    if index == 0 then
      let some complete := retained.liftExecution
        | throwError "the lifted object discarded its full selected computation"
      unless complete.outputs == #[fields] && complete.sources == #[original] &&
          complete.bases == #[base] do
        throwError "object projection discarded a complete original lift input or output"
  let some factorOperation := state.operation? row.factorAddress
    | throwError "the canonical factor operation was not admitted"
  let some liftInput := state.liftInputForm? row.inputAddress
    | throwError "the canonical lift input was not admitted"
  unless (state.rejects factorOperation liftInput).isNone do
    throwError "the canonical factor rejected its own complete lift input"
