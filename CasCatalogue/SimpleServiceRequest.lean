/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.ServiceRequest
public import CasCatalogue.FunctorActionData

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.SimpleServiceRequest
open ServiceRequest

def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

def sameValue (actual expected : Expr) (what : String) : TermElabM Unit := do
  unless ← withoutModifyingState <| withTransparency .all <|
      isDefEq (← inferType actual) (← inferType expected) <&&> isDefEq actual expected do
    throwStratum .malformed m!"the service request changes its complete selected {what}"

def checkClosed (value : Expr) : TermElabM Expr := do
  let value ← instantiateMVars value
  if value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars then
    throwStratum .malformed "the service request omitted a complete formal parameter"
  unless ← isTypeCorrect value do
    throwStratum .malformed "the service request has incompatible complete parameter types"
  return value

def completePort (formal : Expr) (dependencies : Array Operand) (answer : Json) :
    TermElabM (Except String (Option StructuredResult.Result)) := do
  return (← ComputationalData.validatePort formal (← inferType formal) answer
    (dependencies.map fun operand => (operand.data, operand.value))).map fun _ => none

def completeMap (formal : Expr) (source target : Json)
    (dependencies : Array Operand) (answer : Json) :
    TermElabM (Except String (Option StructuredResult.Result)) := do
  let some (domain, endpoint) := Language.homEnds? (← inferType formal)
    | throwError "the prepared callable lost its complete original Hom type"
  if ← withTransparency .all <| isDefEq domain (← ServiceRequest.closedElementDomain) then
    return (← ComputationalData.validateElementAt endpoint target
      (← ServiceRequest.pointResultValue formal) answer).map fun _ => none
  return (← ComputationalData.validateEndpointPort formal source target answer
    (dependencies.map fun operand => (operand.data, operand.value))).map fun _ => none

structure SelectedAction where
  value : Expr
  source : Option CategoryExpr
  target : CategoryExpr
  descriptor : Json
  parameters : Array Json
  dependencies : Array Operand
  declarations : Array DirectConstruction.Application
  /-- Relative to the complete action descriptor and its invocation parameter array. -/
  descriptorOwnership : DataOwnership.Table := #[]
  parameterOwnership : DataOwnership.Table := #[]

/-- The descriptor names an existing complete action, including its literal
nested constructor applications. Only typed operands instantiate declarations. -/
partial def action (decoder : Decoder) (descriptor : Json) : TermElabM SelectedAction := do
  let state ← registryState
  let .ok (tag, arguments) := ComputationalData.envelope descriptor
    | throwStratum .malformed "the service action requires its complete public descriptor"
  if let some entry := state.functors.find? (·.id.raw == tag) then
    let selected ← decoder.declaration entry.declaration arguments
    let parameters := selected.operands.map (·.data)
    let parameterOwnership := operandArrayOwnership selected.operands
    return {
      value := (← Semantic.asFunctor selected.application.value)
      source := some entry.source, target := entry.target
      descriptor := node tag parameters, parameters
      dependencies := selected.operands, declarations := #[selected.application]
      descriptorOwnership := DataOwnership.prefix #[.field "args"] parameterOwnership
      parameterOwnership }
  if let some entry := state.constructions.find? (·.id.raw == tag) then
    let selected ← decoder.declaration entry.declaration arguments
    let parameters := selected.operands.map (·.data)
    let parameterOwnership := operandArrayOwnership selected.operands
    return {
      value := (← Semantic.asFunctor selected.application.value)
      source := none, target := entry.target
      descriptor := node tag parameters, parameters
      dependencies := selected.operands, declarations := #[selected.application]
      descriptorOwnership := DataOwnership.prefix #[.field "args"] parameterOwnership
      parameterOwnership }
  if tag == "classifierForget" then
    let #[id, parameters] := arguments
      | throwStratum .malformed "the classifier action lost its ordered parameters"
    let .ok id := id.getStr?
      | throwStratum .malformed "the classifier identifier must be a string"
    let .ok parameters := parameters.getArr?
      | throwStratum .malformed "classifier parameters must be an ordered array"
    let some entry := state.classifiers.find? (·.id.raw == id)
      | throwStratum .malformed "the classifier action is not mathematically published"
    let selected ← decoder.declaration entry.declaration parameters
    let mut classifier := selected.application.value
    let type ← whnfR (← inferType classifier)
    if type.isAppOf ``LeanCategories.PropertyClassifier then
      classifier ← mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[classifier]
    else if type.isAppOf ``LeanCategories.StructureClassifier then
      classifier ← mkAppM ``LeanCategories.StructureClassifier.toClassifier #[classifier]
    let value ← Semantic.asFunctor (← mkAppM ``LeanCategories.Classifier.forget #[classifier])
    let parameters := selected.operands.map (·.data)
    let descriptor := node tag #[toJson id, Json.arr parameters]
    let descriptorOwnership := argsOwnership #[#[], operandArrayOwnership selected.operands]
    return {
      value, source := some (.refine entry.host entry.id), target := entry.host
      descriptor, parameters := #[descriptor]
      dependencies := selected.operands, declarations := #[selected.application]
      descriptorOwnership, parameterOwnership := arrayOwnership #[descriptorOwnership] }
  if tag == "constructorMap" then
    let #[id, inner] := arguments
      | throwStratum .malformed "the constructor action lost its complete inner action"
    let .ok id := id.getStr?
      | throwStratum .malformed "the constructor identifier must be a string"
    let some entry := state.constructor? ⟨id⟩
      | throwStratum .malformed "the constructor is not mathematically published"
    let some declaration := entry.functorialAction
      | throwStratum .malformed "the constructor has no published action on functors"
    let inner ← action decoder inner
    let descriptor := node tag #[toJson id, inner.descriptor]
    let descriptorOwnership := argsOwnership #[#[], inner.descriptorOwnership]
    let some source := inner.source
      | throwStratum .malformed "the nested action has no published structural source schema"
    return {
      value := (← Semantic.applyConstructorFunctor declaration inner.value)
      source := some (.construct entry.id #[.category source])
      target := .construct entry.id #[.category inner.target]
      descriptor, parameters := #[descriptor]
      dependencies := inner.dependencies, declarations := inner.declarations
      descriptorOwnership, parameterOwnership := arrayOwnership #[descriptorOwnership] }
  throwStratum .malformed "the service action does not name a published functor projection"

def closeAction (selected : SelectedAction) : TermElabM SelectedAction := do
  for declaration in selected.declarations do discard <| DirectConstruction.close declaration
  return { selected with value := (← checkClosed selected.value) }

/-- The complete public action grammar determines its existing recursive identity. -/
partial def actionIdentity (descriptor : Json) : TermElabM Json := do
  let .ok (tag, arguments) := ComputationalData.envelope descriptor
    | throwStratum .malformed "the derived service action descriptor is malformed"
  match tag, arguments with
  | "classifierForget", #[.str id, _] =>
    pure (Json.mkObj [("classifierForget", toJson id)])
  | "constructorMap", #[.str id, inner] =>
    pure (Json.mkObj [("constructorMap", Json.arr #[toJson id, ← actionIdentity inner])])
  | _, _ => pure (Json.mkObj [("functor", toJson tag)])

def selectedDescriptor (operation : Operation) (parameters : Array Json) :
    TermElabM Json := do
  match operation with
  | .functor entry | .functorMap entry => pure (node entry.id.raw parameters)
  | .construction entry _ => pure (node entry.id.raw parameters)
  | .edgeAction edge _ =>
    let #[descriptor] := parameters
      | throwStratum .malformed "the derived service action requires one complete action descriptor"
    unless (← actionIdentity descriptor) == edgeImageDescriptor edge do
      throwStratum .malformed "the derived service operation changes its registered action identity"
    return descriptor
  | _ => throwError "this request is not an object or map action"

def objectAction (decoder : Decoder) (operation : Operation) (input : Form)
    (template : Json) : TermElabM Prepared := do
  let .ok invocation := Backend.ConstructionInvocation.decode operation.id template
    | throwStratum .malformed "the service object action has an incomplete construction invocation"
  let selected ← action decoder (← selectedDescriptor operation invocation.parameters)
  let (sourceBundle, _) ← functorCategoryBundles selected.value
  let original ← decoder.argument (← mkAppM ``CategoryTheory.Bundled.α #[sourceBundle])
    invocation.receiver
  let formal ← Semantic.objOf selected.value original.value
  let selected ← closeAction selected
  let formal ← checkClosed formal
  let (_, targetBundle) ← functorCategoryBundles selected.value
  let target : CategoryContext := { expression := selected.target, bundle := targetBundle }
  let parameters := match operation with
    | .edgeAction .. => #[selected.descriptor]
    | _ => selected.parameters
  let parameterOwnership := match operation with
    | .edgeAction .. => arrayOwnership #[selected.descriptorOwnership]
    | _ => selected.parameterOwnership
  let request := Backend.ConstructionInvocation.encode {
    construction := operation.id, parameters, receiver := original.data }
  let requestOwnership := DataOwnership.prefix #[.field "args"] parameterOwnership ++
    DataOwnership.prefix #[.field "receiver"] original.ownership
  let dependencies := selected.dependencies.push original
  return {
    requestValue := original.value, request, requestOwnership, result := formal
    familyApplication := selected.declarations[0]?.map (·.value)
    resultForm := formFor (← registryState) target input
    dependencies, resultContext := some target, objectResult := true
    action := some (.object selected.value original parameters selected.dependencies)
    complete := completePort formal dependencies }

def mapAction (decoder : Decoder) (operation : Operation) (input : Form)
    (template : Json) : TermElabM Prepared := do
  let .ok invocation := Backend.PointInvocation.decode template
    | throwStratum .malformed "the service map action requires its complete point invocation"
  unless invocation.operation == operation.id do
    throwStratum .malformed "the service map invocation changes its operation identifier"
  let descriptor ← selectedDescriptor operation invocation.parameters
  let .ok ("map", #[declared, originalTemplate]) :=
      ComputationalData.envelope invocation.arrow
    | throwStratum .malformed "the service map action lost its action and original typed map"
  unless declared == descriptor do
    throwStratum .malformed "the service map action differs from its complete selected parameters"
  let selected ← action decoder descriptor
  let original ← decoder.arrow originalTemplate
  let .ok _ := Backend.TypedMap.decode original.data
    | throwStratum .malformed "the service map action requires the complete original typedMap"
  let formalMap ← Semantic.mapOf selected.value original.value
  let selected ← closeAction selected
  let formalMap ← checkClosed formalMap
  let (sourceBundle, targetBundle) ← functorCategoryBundles selected.value
  let some sourceExpression := selected.source <|> original.context.map (·.expression) <|>
      (original.form.bind (← registryState).formExpression?)
    | throwStratum .malformed "the construction map omitted its complete original source context"
  let source : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
  let target : CategoryContext := { expression := selected.target, bundle := targetBundle }
  let some (imageSource, imageTarget) := Language.homEnds? (← inferType formalMap)
    | throwStratum .malformed "the complete mapped action has no independently fixed Hom type"
  CategoryContext.checkMorphism target formalMap imageSource imageTarget
  let imageSourceData ← decoder.argument (← inferType imageSource) invocation.source
  let imageTargetData ← decoder.argument (← inferType imageTarget) invocation.target
  sameValue imageSourceData.value imageSource "image source"
  sameValue imageTargetData.value imageTarget "image target"
  let domain ← decoder.argument (← inferType imageSource) invocation.domain
  CategoryContext.checkObject target domain.value
  let argument ← decoder.argument (← CategoryContext.hom target domain.value imageSource)
    invocation.argument
  let formal ← checkClosed (← ServiceRequest.compose target domain.value imageSource imageTarget
    argument.value formalMap)
  let parameters := match operation with
    | .edgeAction .. => #[selected.descriptor]
    | _ => selected.parameters
  let parameterOwnership := match operation with
    | .edgeAction .. => arrayOwnership #[selected.descriptorOwnership]
    | _ => selected.parameterOwnership
  let arrow := node "map" #[selected.descriptor, original.data]
  let arrowOwnership := argsOwnership #[selected.descriptorOwnership, original.ownership]
  let request := Backend.PointInvocation.encode {
    operation := operation.id, parameters, arrow
    domain := domain.data, source := imageSourceData.data, target := imageTargetData.data
    argument := argument.data }
  let requestOwnership := argsOwnership #[#[], parameterOwnership, arrowOwnership,
    domain.ownership, imageSourceData.ownership, imageTargetData.ownership, argument.ownership]
  let dependencies := selected.dependencies ++
    #[original, domain, imageSourceData, imageTargetData, argument]
  let whole := domain.data == imageSourceData.data &&
    domain.ownership == imageSourceData.ownership &&
    argument.data == node "identity" #[imageSourceData.data, imageSourceData.data] &&
    argument.ownership == argsOwnership #[imageSourceData.ownership, imageSourceData.ownership]
  return {
    requestValue := formal, request, requestOwnership, result := formal
    familyApplication := selected.declarations[0]?.map (·.value)
    resultForm := formFor (← registryState) target input true
    dependencies, resultContext := some target, callableResult := true
    pointResult := (← withoutModifyingState <| withTransparency .all <|
      isDefEq domain.value (← ServiceRequest.closedElementDomain))
    action := if whole then some (.wholeMap selected.value source target original
      selected.descriptor parameters selected.dependencies imageSourceData imageTargetData)
      else none
    complete := completeMap formal domain.data imageTargetData.data dependencies }

def callable (decoder : Decoder) (operation : Operation) (input : Form)
    (template : Json) : TermElabM Prepared := do
  let state ← registryState
  let some (declaration, categoryId) := state.callable? operation.id
    | throwStratum .malformed "the service callable has no published declaration"
  let .ok invocation := Backend.PointInvocation.decode template
    | throwStratum .malformed "the service callable requires its complete point invocation"
  unless invocation.operation == operation.id do
    throwStratum .malformed "the service point invocation changes its published operation"
  let application ← decoder.declaration declaration invocation.parameters
  let applicationValue ← DirectConstruction.close application.application
  let formalArrow ← checkClosed applicationValue.value
  let some (source, target) := Language.homEnds? (← inferType formalArrow)
    | throwStratum .malformed "the service callable lost its complete published Hom type"
  let dataCategory := match operation with
    | .operation _ => CategoryId.sets
    | _ => categoryId
  let some category := state.categories.find? (·.id == dataCategory)
    | throwError "the published callable's complete data category is absent"
  let context ← CategoryContext.ofNamed category source
  CategoryContext.checkMorphism context formalArrow source target
  let sourceData ← decoder.argument (← inferType source) invocation.source
  let targetData ← decoder.argument (← inferType target) invocation.target
  sameValue sourceData.value source "callable source"
  sameValue targetData.value target "callable target"
  let arrow ← decoder.argument (← inferType formalArrow) invocation.arrow
  sameValue arrow.value formalArrow "callable declaration"
  let domain ← decoder.argument (← inferType source) invocation.domain
  CategoryContext.checkObject context domain.value
  let argument ← decoder.argument (← CategoryContext.hom context domain.value source)
    invocation.argument
  let formal ← checkClosed (← ServiceRequest.compose context domain.value source target
    argument.value formalArrow)
  let request := Backend.PointInvocation.encode {
    operation := operation.id, parameters := application.operands.map (·.data)
    arrow := arrow.data, domain := domain.data, source := sourceData.data
    target := targetData.data, argument := argument.data }
  let requestOwnership := argsOwnership #[#[], operandArrayOwnership application.operands,
    arrow.ownership, domain.ownership, sourceData.ownership, targetData.ownership, argument.ownership]
  let dependencies := application.operands ++ #[sourceData, targetData, arrow, domain, argument]
  return {
    requestValue := formal, request, requestOwnership, result := formal
    familyApplication := some formalArrow
    resultForm := formFor state context input true
    dependencies, resultContext := some context, callableResult := true
    pointResult := (← withoutModifyingState <| withTransparency .all <|
      isDefEq domain.value (← ServiceRequest.closedElementDomain))
    complete := completeMap formal domain.data targetData.data dependencies }

/-- Methods and properties retain the existing semantic route and ordinary
executor, including accepted comparisons and prescribed result lifts. -/
def semanticRequest (decoder : Decoder) (operation : Operation) (input : Form)
    (template : Json) : TermElabM Prepared := do
  let state ← registryState
  let some expression := state.formExpression? input
    | throwStratum .malformed "the service receiver has no published source-category expression"
  let original ← decoder.object template
  let trace ← Trace.new
  match operation with
  | .method entry =>
    let (result, context) ← Semantic.methodIn entry.name original.value expression (some trace)
    let result ← checkClosed result
    let familyApplication := (FunctorActionData.objectAction? result).bind fun (action, _) =>
      FunctorActionData.directActionDeclaration? state action
    return {
      requestValue := original.value, request := original.data, result
      familyApplication
      requestOwnership := original.ownership
      resultForm := formFor state context input
      dependencies := #[original], resultContext := some context
      objectResult := true, trace := some trace
      complete := completePort result #[original] }
  | .property entry =>
    let result ← Semantic.propertyIn entry.name original.value expression (some trace)
    let result ← checkClosed result
    return {
      requestValue := original.value, request := original.data, result
      requestOwnership := original.ownership
      resultForm := input, dependencies := #[original]
      trace := some trace, decisionResult := true
      complete := fun answer => do
        return (← Codec.decode (mkApp (mkConst ``Option [0]) (mkConst ``Bool)) answer).map
          fun _ => none }
  | _ => throwError "this request is not a published method or property"

def prepare? (decoder : Decoder) (operation : Operation) (input : Form)
    (template : Json) : TermElabM (Option Prepared) := do
  match operation with
  | .functor _ | .construction _ false | .edgeAction _ false =>
    return some (← objectAction decoder operation input template)
  | .functorMap _ | .construction _ true | .edgeAction _ true =>
    return some (← mapAction decoder operation input template)
  | .operation _ | .morphism _ | .application _ | .binder _ =>
    return some (← callable decoder operation input template)
  | .method _ | .property _ => return some (← semanticRequest decoder operation input template)
  | _ => return none

end CasCatalogue.SimpleServiceRequest
