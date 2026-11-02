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
def mapFragment (decoder : Decoder) (operand : Operand) :
    TermElabM (DataOwnership.Data × Operand × Operand) := do
  let source ← decoder.endpoint operand true
  let target ← decoder.endpoint operand false
  let packet ← match Backend.TypedMap.decode operand.data with
    | .ok complete =>
        unless complete.source == source.data && complete.target == target.data do
          throwStratum .malformed "a service map changes its actual retained endpoint packets"
        unless DataOwnership.project #[.field "args", .index 0] operand.ownership == source.ownership &&
            DataOwnership.project #[.field "args", .index 1] operand.ownership == target.ownership do
          throwStratum .malformed "a service map changes its actual retained endpoint ownership"
        pure operand.fragment
    | .error _ => pure {
        json := Backend.TypedMap.encode {
          source := source.data, target := target.data, callable := operand.data }
        ownership := argsOwnership #[source.ownership, target.ownership, operand.ownership] }
  return (packet, source, target)

/-- Observational compatibility wrapper. Runtime assembly uses `mapFragment` so
the complete packet's occurrence scopes remain available. -/
def mapPacket (decoder : Decoder) (operand : Operand) :
    TermElabM (Json × Operand × Operand) := do
  let (packet, source, target) ← mapFragment decoder operand
  return (packet.json, source, target)

/-- The same framing branch as `mapFragment` fixes each retained input path.
An existing complete map stays whole; a new frame retains its actual callable
and both original endpoint operands at their declared fields. -/
def mapInputPaths (operand source target : Operand) : Array (DataOwnership.Path × Operand) :=
  let endpoints := #[(#[DataOwnership.Step.field "args", .index 0], source),
    (#[.field "args", .index 1], target)]
  match Backend.TypedMap.decode operand.data with
  | .ok _ => #[(#[], operand)] ++ endpoints
  | .error _ => endpoints.push (#[.field "args", .index 2], operand)

/-- Materialize the already selected universal interface from exact typed operands.
The public decoder and private captured invocation supply the same ordered input
roles to this factory. No operand is decoded or recovered from equal JSON here. -/
def materializedLimit (row : LimitEntry) (diagram presentation : Expr)
    (plan : StructuredResult.DataPlan) (dependencies : Array Operand)
    (roles : Array (DataOwnership.Data × Option DataOwnership.Data ×
      Option DataOwnership.Data))
    (inputPaths : Array (DataOwnership.Path × Operand) := #[]) : TermElabM Prepared := do
  let state ← registryState
  let some constructor ← Semantic.diagramConstructor row
    | throwStratum .noImplementation "the registered universal construction has no public diagram telescope"
  let tag := Codec.label constructor
  let diagram ← checkClosed diagram
  let presentation ← StructuredResult.checkReconstruction presentation
  let request := node tag (roles.map (·.1.json))
  let requestOwnership := argsOwnership (roles.map (·.1.ownership))
  let resolveRole : StructuredResult.InputRole → Option DataOwnership.Data := fun role => do
    match role with
    | .argument position => return (← roles[position]?).1
    | .source position => (← roles[position]?).2.1
    | .target position => (← roles[position]?).2.2
  let externalFragment : Nat → Option DataOwnership.Data := fun binder => do
    let binding ← plan.binders[binder]?
    let role ← binding.inputRoles[0]?
    let data ← resolveRole role
    if binding.inputRoles.all (fun other => resolveRole other == some data) then some data else none
  let external : Nat → Option Json := fun binder => do
    let binding ← plan.binders[binder]?
    let role ← binding.inputRoles[0]?
    let data ← resolveRole role
    if binding.inputRoles.all (fun other => (resolveRole other).map (·.json) == some data.json) then
      some data.json else none
  -- The existing data-plan role agreement cannot choose a supplier merely
  -- because distinct sessions happened to return the same token bytes.
  for binding in plan.binders do
    if (external binding.index).isSome && (externalFragment binding.index).isNone then
      throwStratum .malformed "a repeated universal input changes its actual opaque ownership"
  let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← checkClosed (← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone])
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the accepted universal construction lost its registered category"
  let context ← CategoryContext.ofNamed category apex
  let scopedInputs : Array (DataOwnership.Data × Expr) :=
    plan.binders.filterMap fun binding => if binding.port.isSome then none else do
      let formal ← binding.formalValue
      let actual ← externalFragment binding.index
      return (actual, formal)
  let constructionInputs : ComputationalData.InterfaceObjects :=
    scopedInputs.map fun (actual, formal) => (actual.json, formal)
  let constructionInputOwnership := scopedInputs.map (·.1.ownership)
  return {
    requestValue := diagram, request, requestOwnership, inputPaths, result := apex
    resultForm := .limitApex row, dependencies
    resultContext := some context, objectResult := true
    constructionInputs := some (apex, constructionInputs)
    constructionInputOwnership
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
            external ComputationalData.endpointKeys))).map some
    completeScoped := some fun answer scope => do
      let .ok answer := ComputationalData.valuePayload answer
        | return .error "the universal result has a malformed computational value envelope"
      let scope := ComputationalData.InterfaceScope.valuePayload? scope
      return (← StructuredResult.complete row diagram request (.direct answer) presentation
        (fun answer => StructuredResult.validatePlannedData plan answer
          (fun port seen data => ComputationalData.validatePlannedPort plan port seen data
            external ComputationalData.endpointKeys
            (scope := ComputationalData.InterfaceScope.arg? scope port.index)))).map some }


/-- Prepare a registered complete (co)limit from its published diagram telescope.
All returned ports remain data; the universal presentation is fixed beforehand. -/
def limit (decoder : Decoder) (row : LimitEntry) (_input : Form)
    (template : Json) : TermElabM Prepared := do
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
  let mut roles : Array (DataOwnership.Data × Option DataOwnership.Data ×
    Option DataOwnership.Data) := #[]
  let mut inputPaths := #[]
  for (operand, index) in selected.operands.zipIdx do
    if (Language.homEnds? (← inferType operand.value)).isSome then
      let (packet, source, target) ← mapFragment decoder operand
      dependencies := dependencies ++ #[source, target]
      roles := roles.push (packet, some source.fragment, some target.fragment)
      inputPaths := inputPaths ++ prefixInputPaths #[.field "args", .index index]
        (mapInputPaths operand source target)
    else
      roles := roles.push (operand.fragment, none, none)
      inputPaths := inputPaths.push (#[.field "args", .index index], operand)
  materializedLimit row diagram presentation plan dependencies roles inputPaths

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
  sourceImage? : Option Operand := none
  comparisonImage? : Option Operand := none
  actionOwnership : DataOwnership.Table := #[]
  parameterOwnership : DataOwnership.Table := #[]
  inputPaths : Array (DataOwnership.Path × Operand) := #[]
  scope : Option ComputationalData.InterfaceScope := none

/-- Metadata occurrences keep the suppliers of their exact typed operands. -/
def Selection.imageOwnership (selected : Selection) : DataOwnership.Table :=
  DataOwnership.prefix #[.field "sourceImage"]
      ((selected.sourceImage?.map (·.ownership)).getD #[]) ++
    DataOwnership.prefix #[.field "comparisonImage"]
      ((selected.comparisonImage?.map (·.ownership)).getD #[])

/-- Scope the normalized public lift packet at the preparer's original typed
operand positions. Descriptor parameters, source, base, earlier outputs and
actual images remain separate even when their packet spellings coincide. -/
def selectionValidationScope (decoder : Decoder) (selected : Selection)
    (originalArrow : Bool) : TermElabM (Option ComputationalData.InterfaceScope) := do
  let children ← selected.inputPaths.filterMapM fun (path, operand) => do
    return (← decoder.validationScope operand).map fun scope => (path, scope)
  if children.isEmpty then return none
  let invocation : Backend.LiftInput := {
    originalArrow, lift := selected.plan.entry.id.raw, action := selected.action
    source := selected.original.data, base := selected.base.data
    outputs := selected.outputs.map (·.data), parameters := selected.parameters
    sourceImage? := selected.sourceImage?.map (·.data)
    comparisonImage? := selected.comparisonImage?.map (·.data) }
  let data : DataOwnership.Data := {
    json := invocation.encode
    ownership := selected.imageOwnership ++
      DataOwnership.prefix #[.field "parameters"] selected.parameterOwnership ++
      argsOwnership #[#[], selected.actionOwnership, selected.original.ownership,
        selected.base.ownership, operandArrayOwnership selected.outputs] }
  match ComputationalData.InterfaceScope.assemble data children with
  | .ok scope => return some scope
  | .error message => throwStratum .malformed message

/-- Instantiate only the registered evidence family. Monicity is projected from
the independently typed formal subobject, never decoded from a packet field. -/
def selection (decoder : Decoder) (entry : LiftEntry) (parameters : Array Json)
    (action source base : Json) (outputs : Array Json) (originalArrow : Bool)
    (images : Backend.LiftImages := {}) :
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
  let sourceImage? ← images.sourceImage?.mapM fun data => do
    let formal ← if originalArrow then do
        let .constructMap constructor _ := entry.edge
          | throwError "the selected lift has no complete constructor action"
        let some action := (state.constructor? constructor).bind (·.functorialAction)
          | throwError "the selected lift lost its accepted constructor action"
        Semantic.objOf (← Semantic.applyConstructorFunctor action plan.action) original.value
      else Semantic.objOf plan.action source.value
    let operand ← decoder.argument (← inferType formal) data
    sameValue operand.value formal "lift source image"
    return operand
  let sourceImageObject? ← sourceImage?.mapM fun image => do
    if originalArrow then decoder.project image "source" none else pure image
  if let some image := sourceImageObject? then
    if let .error message ← LiftedSubobjectData.validateSourceImageBase plan image.data base.data
        (← decoder.validationScope base) (← decoder.validationScope image) then
      throwStratum .malformed m!"the service lift changes its actual image ambient: {message}"
  let mut actual := #[]
  for (data, index) in outputs.zipIdx do
    let some formal := plan.ports[index]?
      | throwStratum .malformed "the service lift has too many preceding outputs"
    let operand ← decoder.argument (← inferType formal) data
    sameValue operand.value formal "preceding lift output"
    actual := actual.push operand
  let comparisonImage? ← images.comparisonImage?.mapM fun data => do
    let formal ← Semantic.objOf plan.action plan.ports[0]!
    let operand ← decoder.argument (← inferType formal) data
    sameValue operand.value formal "lift comparison image"
    return operand
  let dependencies := declared.operands ++ selected.dependencies ++
    #[original, source, base, baseObject, inclusion] ++ actual ++
    sourceImage?.toArray ++ sourceImageObject?.toArray ++ comparisonImage?.toArray
  let result : Selection := {
    plan, action := selected.descriptor, parameters := declared.operands.map (·.data)
    original, source, base, baseObject, outputs := actual, dependencies,
    sourceImage?, comparisonImage?
    actionOwnership := selected.descriptorOwnership
    parameterOwnership := operandArrayOwnership declared.operands
    inputPaths := prefixInputPaths #[.field "parameters"]
        (operandArrayInputPaths declared.operands) ++
      prefixInputPaths #[.field "args", .index 1] selected.descriptorInputPaths ++
      #[(#[.field "args", .index 2], original), (#[.field "args", .index 3], base)] ++
      prefixInputPaths #[.field "args", .index 4] (operandArrayInputPaths actual) ++
      sourceImage?.toArray.map (fun operand => (#[.field "sourceImage"], operand)) ++
      comparisonImage?.toArray.map (fun operand => (#[.field "comparisonImage"], operand)) }
  let scope ← selectionValidationScope decoder result originalArrow
  if !actual.isEmpty then
    if let .error message ← LiftedSubobjectData.validateSelectionPrefixWith plan
        selected.descriptor source.data base.data (actual.map (·.data))
        (LiftedSubobjectData.ComparisonImageRole.ofMetadata sourceImage?.isSome
          (comparisonImage?.map (·.data))) scope originalArrow then
      throwStratum .malformed m!"the service lift changes its preceding complete output data: {message}"
  return { result with scope }

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
  let .ok images := Backend.LiftImages.decode template outputs.size
    | throwStratum .malformed "the service lift has incomplete or mistimed actual image metadata"
  let selected ← selection decoder entry parameters action source base outputs originalArrow images
  let invocation : Backend.LiftInput := {
    originalArrow, lift := entry.id.raw, action := selected.action
    source := selected.original.data, base := selected.base.data
    outputs := selected.outputs.map (·.data), parameters := selected.parameters
    sourceImage? := selected.sourceImage?.map (·.data)
    comparisonImage? := selected.comparisonImage?.map (·.data) }
  let requestOwnership := selected.imageOwnership ++
    DataOwnership.prefix #[.field "parameters"] selected.parameterOwnership ++
    argsOwnership #[#[], selected.actionOwnership, selected.original.ownership,
      selected.base.ownership, operandArrayOwnership selected.outputs]
  let .ok _ := Backend.LiftInput.decode invocation.encode operation
    | throwStratum .malformed "the resolved service lift lost its complete public framing"
  let some index := LiftField.all.findIdx? (· == field) | unreachable!
  let formal ← checkClosed selected.plan.ports[index]!
  let context ← SelectedLift.context selected.plan (index >= 2)
  return {
    requestValue := formal, request := invocation.encode, requestOwnership, result := formal
    inputPaths := selected.inputPaths
    resultForm := formFor (← registryState) context input (index != 0)
    dependencies := selected.dependencies, resultContext := some context
    objectResult := index == 0, callableResult := index != 0
    callableInterface := if index == 0 then none else some .framed
    complete := fun answer => do
      return (← LiftedSubobjectData.validateSelectionPrefixWith selected.plan selected.action
        selected.source.data selected.base.data (invocation.outputs.push answer)
        (LiftedSubobjectData.ComparisonImageRole.ofMetadata invocation.sourceImage?.isSome
          invocation.comparisonImage?)).map fun _ => none
    completeScoped := some fun answer replyScope => do
      let scope ← match selected.scope with
        | none => pure (.ok none)
        | some request =>
          pure ((LiftedSubobjectData.appendSelectionReplyScope request
            (replyScope.getD { data := { json := answer } })).map some)
      let .ok scope := scope | return scope.map fun _ => none
      return (← LiftedSubobjectData.validateSelectionPrefixWith selected.plan selected.action
        selected.source.data selected.base.data (invocation.outputs.push answer)
        (LiftedSubobjectData.ComparisonImageRole.ofMetadata invocation.sourceImage?.isSome
          invocation.comparisonImage?) scope originalArrow).map fun _ => none }

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
  let .ok images := Backend.LiftImages.decode template outputs.size
    | throwStratum .malformed "the service factor omitted its complete actual image metadata"
  let selected ← selection decoder entry parameters action source base outputs false images
  let cone ← decoder.arrow cone
  let (coneData, domain, coneTarget) ← mapFragment decoder cone
  sameValue coneTarget.value selected.source.value "factor cone target"
  let baseMap ← decoder.arrow baseMap
  let (baseData, baseDomain, baseTarget) ← mapFragment decoder baseMap
  sameValue baseTarget.value selected.baseObject.value "factor base target"
  sameValue baseDomain.value (← Semantic.objOf selected.plan.action domain.value) "factor image domain"
  let equation ← mkEq (← Semantic.mapOf selected.plan.action cone.value)
    (← mkAppM ``CategoryTheory.CategoryStruct.comp #[baseMap.value, selected.plan.inclusion])
  let proof ← decoder.condition equation
  unless !proof.hasSorry && (← Decide.kernelAccepts equation proof) do
    throwStratum .malformed "the service factor lacks its independently checked compatibility equation"
  let formal ← checkClosed (← SelectedLift.factor selected.plan baseMap.value cone.value proof)
  let .ok baseMapData := Backend.TypedMap.decode baseData.json | unreachable!
  let .ok coneMapData := Backend.TypedMap.decode coneData.json | unreachable!
  let invocation : Backend.LiftFactorInput := {
    lift := entry.id.raw, action := selected.action, source := selected.source.data
    base := selected.base.data, outputs := selected.outputs.map (·.data)
    parameters := selected.parameters, baseMap := baseMapData, cone := coneMapData
    sourceImage? := selected.sourceImage?.map (·.data)
    comparisonImage? := selected.comparisonImage?.map (·.data) }
  -- Both complete maps were already checked at their original typed roles.
  -- Keep their actual envelopes and suppliers instead of stripping optional
  -- fields and then attaching the original whole-map occurrence to new bytes.
  let request := invocation.encode.setObjVal! "args" (Json.arr #[
    toJson invocation.lift, invocation.action, invocation.source, invocation.base,
    Json.arr invocation.outputs, baseData.json, coneData.json])
  let requestOwnership := selected.imageOwnership ++
    DataOwnership.prefix #[.field "parameters"] selected.parameterOwnership ++
    argsOwnership #[#[], selected.actionOwnership, selected.source.ownership,
      selected.base.ownership, operandArrayOwnership selected.outputs,
      baseData.ownership, coneData.ownership]
  let .ok _ := Backend.LiftFactorInput.decode request entry.factorAddress
    | throwStratum .malformed "the resolved service factor lost its complete public framing"
  let context ← SelectedLift.context selected.plan
  return {
    requestValue := formal, request, requestOwnership, result := formal
    inputPaths := selected.inputPaths ++
      prefixInputPaths #[.field "args", .index 5] (mapInputPaths baseMap baseDomain baseTarget) ++
      prefixInputPaths #[.field "args", .index 6] (mapInputPaths cone domain coneTarget)
    resultForm := formFor (← registryState) context input true
    dependencies := selected.dependencies ++ #[cone, domain, coneTarget, baseMap, baseDomain, baseTarget]
    resultContext := some context, callableResult := true
    callableInterface := some .framed
    complete := fun answer => do
      return (← LiftedSubobjectData.validateMap formal domain.data invocation.outputs[0]! answer).map fun _ => none
    completeScoped := some fun answer scope => do
      return (← LiftedSubobjectData.validateMap formal domain.data invocation.outputs[0]! answer
        (scope := scope) (context? := some context)).map fun _ => none }

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
