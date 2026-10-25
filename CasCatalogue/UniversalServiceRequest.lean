/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.SimpleServiceRequest
public import CasCatalogue.SelectedLift
public import CasCatalogue.LiftedSubobjectData

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.UniversalServiceRequest
open ServiceRequest
open SimpleServiceRequest (node sameValue checkClosed)

/-- Preserve an already complete map packet, or frame its actual callable with
the two retained endpoint operands. No endpoint is recovered from a carrier. -/
def mapPacket (decoder : Decoder) (operand : Operand) :
    TermElabM (Json × Operand × Operand) := do
  let source ← decoder.endpoint operand true
  let target ← decoder.endpoint operand false
  let packet ← match Backend.TypedMap.decode operand.data with
    | .ok complete =>
        unless complete.source == source.data && complete.target == target.data do
          throwStratum .malformed "a service map changes its actual retained endpoint packets"
        pure operand.data
    | .error _ => pure (Backend.TypedMap.encode {
        source := source.data, target := target.data, callable := operand.data })
  return (packet, source, target)

/-- Prepare a registered complete (co)limit from its published diagram telescope.
All returned ports remain data; the universal presentation is fixed beforehand. -/
def limit (decoder : Decoder) (row : LimitEntry) (_input : Form)
    (template : Json) : TermElabM Prepared := do
  let state ← registryState
  let some constructor ← Semantic.diagramConstructor row
    | throwStratum .noImplementation "the registered universal construction has no public diagram telescope"
  let .ok (tag, arguments) := ComputationalData.envelope template
    | throwStratum .malformed "the service construction requires its complete diagram"
  unless tag == Codec.label constructor do
    throwStratum .malformed "the service construction changes its registered diagram constructor"
  let selected ← decoder.declaration constructor arguments
  let application ← DirectConstruction.close selected.application
  let diagram ← checkClosed application.value
  let presentation ← StructuredResult.checkReconstruction (← Semantic.limitPresentation row diagram)
  let plan ← match ← StructuredResult.dataPlan row diagram presentation with
    | .ok plan => pure plan
    | .error message => throwStratum .noImplementation m!"the registered construction has no complete data plan: {message}"
  let mut dependencies := selected.operands
  let mut roles : Array (Json × Option Json × Option Json) := #[]
  for operand in selected.operands do
    if (Language.homEnds? (← inferType operand.value)).isSome then
      let (packet, source, target) ← mapPacket decoder operand
      dependencies := dependencies ++ #[source, target]
      roles := roles.push (packet, some source.data, some target.data)
    else
      roles := roles.push (operand.data, none, none)
  let request := node tag (roles.map (·.1))
  let resolveRole : StructuredResult.InputRole → Option Json := fun role => do
    match role with
    | .argument position => return (← roles[position]?).1
    | .source position => (← roles[position]?).2.1
    | .target position => (← roles[position]?).2.2
  let external : Nat → Option Json := fun binder => do
    let binding ← plan.binders[binder]?
    let role ← binding.inputRoles[0]?
    let data ← resolveRole role
    if binding.inputRoles.all (fun other => resolveRole other == some data) then some data else none
  let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← checkClosed (← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone])
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the accepted universal construction lost its registered category"
  let context ← CategoryContext.ofNamed category apex
  let constructionInputs : ComputationalData.InterfaceObjects :=
    plan.binders.filterMap fun binding => if binding.port.isSome then none else do
      let formal ← binding.formalValue
      let actual ← external binding.index
      return (actual, formal)
  return {
    requestValue := diagram, request, result := apex
    resultForm := .limitApex row, dependencies
    resultContext := some context, objectResult := true
    constructionInputs := some (apex, constructionInputs)
    validateTemplate := some fun check template => do
      let .ok template := ComputationalData.valuePayload template
        | throwStratum .malformed "the universal template has a malformed value envelope"
      let validated ← StructuredResult.validatePlannedData plan template fun port _ data => do
        check port.formalField data
        return .ok ()
      if let .error message := validated then
        throwStratum .malformed m!"the universal result template has incomplete framing: {message}"
    complete := fun answer => do
      let .ok answer := ComputationalData.valuePayload answer
        | return .error "the universal result has a malformed computational value envelope"
      return (← StructuredResult.complete row diagram request (.direct answer) presentation
        (fun answer => StructuredResult.validatePlannedData plan answer
          (fun port seen data => ComputationalData.validatePlannedPort plan port seen data
            external ComputationalData.endpointKeys))).map some }

/-- The formal lift and all actual operands stay separate. Public field outputs
are checked against their selected roles and retain their original handles. -/
structure Selection where
  plan : SelectedLift.Plan
  action : Json
  parameters : Array Json
  original : Operand
  source : Operand
  base : Operand
  baseObject : Operand
  outputs : Array Operand
  dependencies : Array Operand

/-- Instantiate only the registered evidence family. Monicity is projected from
the independently typed formal subobject, never decoded from a packet field. -/
def selection (decoder : Decoder) (entry : LiftEntry) (parameters : Array Json)
    (action source base : Json) (outputs : Array Json) (originalArrow : Bool) :
    TermElabM Selection := do
  let state ← registryState
  let declared ← decoder.declaration entry.evidence parameters
  let evidenceType ← withTransparency .all <| whnf (← inferType declared.application.value)
  unless evidenceType.isAppOfArity ``CasCatalogue.MonoLift 5 do
    throwError "the accepted subobject lift lost its complete evidence signature"
  let signature := evidenceType.getAppArgs
  let selected ← SimpleServiceRequest.action decoder action
  let inner ← SelectedLift.innerEdge state entry
  unless (← SimpleServiceRequest.actionIdentity selected.descriptor) == edgeImageDescriptor inner do
    throwStratum .malformed "the service lift changes its registered complete action identity"
  unless ← withTransparency .all <| isDefEq selected.value signature[4]! do
    throwStratum .malformed "the service lift action differs from its selected evidence parameters"
  let sourceType ← if originalArrow then
    mkAppOptM ``CategoryTheory.Arrow #[some signature[0]!, some signature[1]!]
    else pure signature[0]!
  let original ← decoder.argument sourceType source
  let source ← if originalArrow then decoder.project original "source" none else pure original
  let targetArrow ← mkAppOptM ``CategoryTheory.Arrow #[some signature[2]!, some signature[3]!]
  let base ← decoder.argument (← LiftedSubobjectData.subobjectType targetArrow) base
  let baseObject ← decoder.project base "obj" none
  let inclusion ← decoder.project base "hom" none
  let monic ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[base.value]
  let condition ← mkAppM ``CategoryTheory.Mono #[inclusion.value]
  unless !monic.hasSorry && (← Decide.kernelAccepts condition monic) do
    throwStratum .malformed "the service lift has no independently checked formal monicity"
  let declaredApplication ← DirectConstruction.close declared.application
  let plan ← SelectedLift.fromEvidence entry declaredApplication.value source.value inclusion.value monic
  let selected ← SimpleServiceRequest.closeAction selected
  sameValue selected.value plan.action "lift action"
  let mut actual := #[]
  for (data, index) in outputs.zipIdx do
    let some formal := plan.ports[index]?
      | throwStratum .malformed "the service lift has too many preceding outputs"
    let operand ← decoder.argument (← inferType formal) data
    sameValue operand.value formal "preceding lift output"
    actual := actual.push operand
  let dependencies := declared.operands ++ selected.dependencies ++
    #[original, source, base, baseObject, inclusion] ++ actual
  if !actual.isEmpty then
    if let .error message ← LiftedSubobjectData.validateSelectionPrefix plan
        selected.descriptor source.data base.data (actual.map (·.data)) then
      throwStratum .malformed m!"the service lift changes its preceding complete output data: {message}"
  return {
    plan, action := selected.descriptor, parameters := declared.operands.map (·.data)
    original, source, base, baseObject, outputs := actual, dependencies }

/-- Parse only fixed framing before resolving data slots. A whole typed source,
base or preceding output can itself be a scoped reference. -/
def liftFields (template : Json) (operation : String) :
    TermElabM (Bool × String × Array Json × Json × Json × Json × Array Json) := do
  let .ok (tag, #[identity, action, source, base, earlier]) := ComputationalData.envelope template
    | throwStratum .malformed "the service lift requires its five ordered input fields"
  unless tag == "liftInput" || tag == "monoLiftInput" do
    throwStratum .malformed "the service lift has a different public input form"
  let .ok id := identity.getStr?
    | throwStratum .malformed "the service lift requires its registered identifier"
  let some index := LiftField.all.findIdx? (fun field => operation == id ++ "#" ++ field.label)
    | throwStratum .malformed "the service lift changes its dispatched field"
  let .ok outputs := earlier.getArr?
    | throwStratum .malformed "the service lift requires its ordered preceding output prefix"
  unless outputs.size == index do
    throwStratum .malformed "the service lift omits or changes its preceding output prefix"
  let parameters ← match template.getObjVal? "parameters" with
    | .ok json => match json.getArr? with
      | .ok parameters => pure parameters
      | .error _ => throwStratum .malformed "the service lift parameters are not an ordered array"
    | .error _ =>
      if tag == "liftInput" then pure #[]
      else throwStratum .malformed "the service lift omitted its selected evidence parameters"
  return (tag == "liftInput", id, parameters, action, source, base, outputs)

def liftField (decoder : Decoder) (entry : LiftEntry) (field : LiftField)
    (input : Form) (template : Json) : TermElabM Prepared := do
  let operation := entry.fieldAddress field
  let (originalArrow, id, parameters, action, source, base, outputs) ← liftFields template operation
  unless id == entry.id.raw do
    throwStratum .malformed "the service request changes its selected lift"
  let selected ← selection decoder entry parameters action source base outputs originalArrow
  let invocation : Backend.LiftInput := {
    originalArrow, lift := entry.id.raw, action := selected.action
    source := selected.original.data, base := selected.base.data
    outputs := selected.outputs.map (·.data), parameters := selected.parameters }
  let .ok _ := Backend.LiftInput.decode invocation.encode operation
    | throwStratum .malformed "the resolved service lift lost its complete public framing"
  let some index := LiftField.all.findIdx? (· == field) | unreachable!
  let formal ← checkClosed selected.plan.ports[index]!
  let context ← SelectedLift.context selected.plan (index >= 2)
  return {
    requestValue := formal, request := invocation.encode, result := formal
    resultForm := formFor (← registryState) context input (index != 0)
    dependencies := selected.dependencies, resultContext := some context
    objectResult := index == 0, callableResult := index != 0
    complete := fun answer => do
      return (← LiftedSubobjectData.validateSelectionPrefix selected.plan selected.action
        selected.source.data selected.base.data (invocation.outputs.push answer)).map fun _ => none }

def liftFactor (decoder : Decoder) (entry : LiftEntry) (input : Form)
    (template : Json) : TermElabM Prepared := do
  let .ok ("liftFactorInput", #[identity, action, source, base, earlier, baseMap, cone]) :=
      ComputationalData.envelope template
    | throwStratum .malformed "the service factor requires its seven ordered fields"
  unless identity.getStr?.toOption == some entry.id.raw do
    throwStratum .malformed "the service factor changes its selected lift"
  let .ok outputs := earlier.getArr?
    | throwStratum .malformed "the service factor lost its complete lift outputs"
  unless outputs.size == 4 do
    throwStratum .malformed "the service factor requires all four preceding lift outputs"
  let .ok parameters := (template.getObjVal? "parameters").bind (·.getArr?)
    | throwStratum .malformed "the service factor omitted its selected evidence parameters"
  let selected ← selection decoder entry parameters action source base outputs false
  let cone ← decoder.arrow cone
  let (coneData, domain, coneTarget) ← mapPacket decoder cone
  sameValue coneTarget.value selected.source.value "factor cone target"
  let baseMap ← decoder.arrow baseMap
  let (baseData, baseDomain, baseTarget) ← mapPacket decoder baseMap
  sameValue baseTarget.value selected.baseObject.value "factor base target"
  sameValue baseDomain.value (← Semantic.objOf selected.plan.action domain.value) "factor image domain"
  let equation ← mkEq (← Semantic.mapOf selected.plan.action cone.value)
    (← mkAppM ``CategoryTheory.CategoryStruct.comp #[baseMap.value, selected.plan.inclusion])
  let proof ← decoder.condition equation
  unless !proof.hasSorry && (← Decide.kernelAccepts equation proof) do
    throwStratum .malformed "the service factor lacks its independently checked compatibility equation"
  let formal ← checkClosed (← SelectedLift.factor selected.plan baseMap.value cone.value proof)
  let .ok baseMapData := Backend.TypedMap.decode baseData | unreachable!
  let .ok coneMapData := Backend.TypedMap.decode coneData | unreachable!
  let invocation : Backend.LiftFactorInput := {
    lift := entry.id.raw, action := selected.action, source := selected.source.data
    base := selected.base.data, outputs := selected.outputs.map (·.data)
    parameters := selected.parameters, baseMap := baseMapData, cone := coneMapData }
  let .ok _ := Backend.LiftFactorInput.decode invocation.encode entry.factorAddress
    | throwStratum .malformed "the resolved service factor lost its complete public framing"
  let context ← SelectedLift.context selected.plan
  return {
    requestValue := formal, request := invocation.encode, result := formal
    resultForm := formFor (← registryState) context input true
    dependencies := selected.dependencies ++ #[cone, domain, coneTarget, baseMap, baseDomain, baseTarget]
    resultContext := some context, callableResult := true
    complete := fun answer => do
      return (← LiftedSubobjectData.validateMap formal domain.data invocation.outputs[0]! answer).map fun _ => none }

/-- Only the owned universal/lift families are handled here. No shape, category,
backend name or computational answer selects a different mathematical operation. -/
def prepare? (decoder : Decoder) (operation : Operation) (input : Form) (template : Json) :
    TermElabM (Option Prepared) := do
  match operation with
  | .limit .. | .liftField .. | .liftFactor .. =>
    if let some message := (← registryState).rejects operation input then
      throwStratum .malformed m!"the service input is not admitted for its operation: {message}"
  | _ => return none
  match operation with
  | .limit row => return some (← limit decoder row input template)
  | .liftField entry field => return some (← liftField decoder entry field input template)
  | .liftFactor entry => return some (← liftFactor decoder entry input template)
  | _ => return none

end CasCatalogue.UniversalServiceRequest
