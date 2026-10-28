/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.ServiceRequest
public import CasCatalogue.CellAction
public import CasCatalogue.ReindexAction

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.StructuredServiceRequest

open ServiceRequest

def malformed (message : MessageData) : TermElabM α :=
  throwStratum .malformed message

def sameValue (expected actual : Expr) : TermElabM Unit := do
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType expected) (← inferType actual) <&&> isDefEq expected actual) do
    malformed "a service operand changed its complete declared value or type"

def checkContext (expected : CategoryContext) (operand : Operand) : TermElabM Unit := do
  if let some actual := operand.context then
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq expected.bundle actual.bundle) do
      malformed "a service operand changed its complete selected category dictionary"

/-- Equality here checks a repeated input field, not mathematical agreement between
two independent computational answers. Both complete expressions and actual packets
must be retained at the repeated occurrence. -/
def repeated (decoder : Decoder) (expected : Operand) (json : Json) :
    TermElabM Operand := do
  let actual ← decoder.argument (← inferType expected.value) json
  sameValue expected.value actual.value
  unless actual.data == expected.data && actual.ownership == expected.ownership do
    malformed "a repeated service input changed its actual computational data or opaque ownership"
  return actual

def selectedObject (decoder : Decoder) (context : CategoryContext)
    (expected : Expr) (json : Json) : TermElabM Operand := do
  let actual ← decoder.argument (← CategoryContext.carrier context) json
  checkContext context actual
  CategoryContext.checkObject context actual.value
  sameValue expected actual.value
  return actual

def resultForm (context : CategoryContext) (origin : Form) :
    TermElabM Form := do
  if let some row := CategoryContext.named? (← registryState) context.expression then
    return .canonicalMorphism row
  return .contextual context.expression origin

def composite (context : CategoryContext) (domain source target first second : Expr) :
    TermElabM Expr := do
  CategoryContext.checkMorphism context first domain source
  CategoryContext.checkMorphism context second source target
  let carrier ← CategoryContext.carrier context
  let dictionary ← CategoryContext.dictionary context
  let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some carrier, some dictionary]
  let result ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
    #[some carrier, some categoryStructure, some domain, some source, some target, some first, some second]
  let result ← instantiateMVars result
  CategoryContext.checkMorphism context result domain target
  if result.hasMVar || result.hasLevelMVar || result.hasFVar || result.hasLooseBVars then
    malformed "the service application has unresolved complete mathematical parameters"
  unless ← isTypeCorrect result do
    malformed "the service application is outside its published complete signature"
  return result

def invocation (operation : Operation) (json : Json) :
    TermElabM Backend.PointInvocation := do
  let .ok request := Backend.PointInvocation.decode json
    | malformed "the service requires the complete seven-field apply request"
  unless request.operation == operation.id do
    malformed "the service request changed its enclosing published operation"
  return request

def callableDescriptor (json : Json) :
    TermElabM (Json × Option Backend.TypedMap) := do
  if (json.getObjValAs? String "ctor").toOption == some "typedMap" then
    let .ok arrow := Backend.TypedMap.decode json
      | malformed "the service callable has malformed complete endpoints"
    return (arrow.callable, some arrow)
  return (json, none)

/-- Complete the existing generalized application from a separately derived
published callable. Every input is decoded at its actual full category dictionary.
No result type, backend choice, or mathematical assertion is accepted from data. -/
def prepareCallable (decoder : Decoder) (operation : Operation) (input : Form)
    (request : Backend.PointInvocation) (formal source target : Expr)
    (context : CategoryContext) (descriptor : Json) (parameters : Array Json)
    (dependencies : Array Operand) (wrapper : Option Backend.TypedMap)
    (descriptorOwnership : DataOwnership.Table := #[])
    (parameterOwnership : DataOwnership.Table := #[])
    (descriptorInputPaths : Array (DataOwnership.Path × Operand) := #[])
    (parameterInputPaths : Array (DataOwnership.Path × Operand) := #[]) :
    TermElabM Prepared := do
  let domain ← decoder.argument (← CategoryContext.carrier context) request.domain
  checkContext context domain
  CategoryContext.checkObject context domain.value
  let sourceData ← selectedObject decoder context source request.source
  let targetData ← selectedObject decoder context target request.target
  let argument ← decoder.argument (← CategoryContext.hom context domain.value source) request.argument
  checkContext context argument
  CategoryContext.checkMorphism context argument.value domain.value source
  let mut dependencies := dependencies ++ #[domain, sourceData, targetData, argument]
  let (arrow, arrowOwnership, arrowInputPaths) ← match wrapper with
    | none => pure (descriptor, descriptorOwnership, descriptorInputPaths)
    | some wrapped => do
        let first ← repeated decoder sourceData wrapped.source
        let second ← repeated decoder targetData wrapped.target
        dependencies := dependencies ++ #[first, second]
        pure (Backend.TypedMap.encode {
          source := sourceData.data, target := targetData.data, callable := descriptor },
          argsOwnership #[first.ownership, second.ownership, descriptorOwnership],
          #[(#[.field "args", .index 0], first), (#[.field "args", .index 1], second)] ++
            prefixInputPaths #[.field "args", .index 2] descriptorInputPaths)
  let result ← composite context domain.value source target argument.value formal
  let actual : Backend.PointInvocation := {
    operation := operation.id, parameters, arrow, domain := domain.data
    source := sourceData.data, target := targetData.data, argument := argument.data }
  let requestOwnership := argsOwnership #[#[], parameterOwnership, arrowOwnership,
    domain.ownership, sourceData.ownership, targetData.ownership, argument.ownership]
  return {
    requestValue := result, request := actual.encode, requestOwnership, result
    inputPaths := prefixInputPaths #[.field "args", .index 1] parameterInputPaths ++
      prefixInputPaths #[.field "args", .index 2] arrowInputPaths ++
      #[(#[.field "args", .index 3], domain), (#[.field "args", .index 4], sourceData),
        (#[.field "args", .index 5], targetData), (#[.field "args", .index 6], argument)]
    resultForm := ← resultForm context input
    dependencies, resultContext := some context, callableResult := true
    callableInterface := some (.endpoints domain.value targetData.value
      domain.fragment targetData.fragment)
    callableEndpointOperands := some (domain, targetData)
    complete := fun answer => do
      return (← ComputationalData.validateEndpointPort result domain.data targetData.data answer).map
        (fun _ => none) }

def prepareCell (decoder : Decoder) (entry : CellEntry)
    (constructors : Array ConstructorId) (input : Form) (template : Json) :
    TermElabM Prepared := do
  let operation := Operation.cellComponent entry constructors
  let request ← invocation operation template
  let (descriptor, wrapper) ← callableDescriptor request.arrow
  let component ← if constructors.isEmpty then do
      let .ok component := Backend.CellComponent.decode descriptor
        | malformed "the service component omitted its complete selected receiver"
      pure component
    else do
      let .ok constructed := Backend.ConstructedCellComponent.decode descriptor
        | malformed "the service component omitted its complete constructor path"
      unless constructed.constructors == constructors.map (·.raw) do
        malformed "the service component changed its accepted constructor path"
      pure constructed.component
  unless component.cell == entry.id.raw do
    malformed "the service component changed its registered natural transformation"
  let declaration ← decoder.declaration entry.declaration component.parameters
  let receiver ← decoder.object component.receiver
  -- Bind the full receiver before closing implicit declaration parameters.
  discard <| CellAction.assemble entry declaration.application constructors component.inverse receiver.value
  let closed ← DirectConstruction.close declaration.application
  let action ← CellAction.select entry (← closed.explicit.mapM exprToSyntax)
    constructors component.inverse receiver.value
  let sourceContext : CategoryContext := {
    expression := action.source, bundle := action.sourceBundle }
  CategoryContext.checkObject sourceContext receiver.value
  checkContext sourceContext receiver
  let receiver ← repeated decoder receiver component.receiver
  let #[parameterData, receiverData, inverseData] := request.parameters
    | malformed "the component invocation omitted its ordered parameters, receiver or direction"
  let .ok parameterData := parameterData.getArr?
    | malformed "the component's complete declaration parameters are not ordered data"
  unless parameterData.size == declaration.operands.size do
    malformed "the component invocation changed its complete declaration arity"
  let repeatedParameters ← (declaration.operands.zip parameterData).mapM fun (expected, data) =>
    repeated decoder expected data
  let repeatedReceiver ← repeated decoder receiver receiverData
  unless inverseData.getBool?.toOption == some component.inverse do
    malformed "the component invocation changed its independently selected direction"
  let parameters := declaration.operands.map (·.data)
  let actualComponent : Backend.CellComponent := {
    cell := entry.id.raw, parameters, receiver := receiver.data, inverse := component.inverse }
  let actualDescriptor := if constructors.isEmpty then actualComponent.encode else
    Backend.ConstructedCellComponent.encode {
      constructors := constructors.map (·.raw), component := actualComponent }
  let componentOwnership := argsOwnership
    #[#[], operandArrayOwnership declaration.operands, receiver.ownership, #[]]
  let descriptorOwnership := if constructors.isEmpty then componentOwnership else
    argsOwnership #[#[], componentOwnership]
  let componentInputPaths := prefixInputPaths #[.field "args", .index 1]
      (operandArrayInputPaths declaration.operands) ++
    #[(#[.field "args", .index 2], receiver)]
  let descriptorInputPaths := if constructors.isEmpty then componentInputPaths else
    prefixInputPaths #[.field "args", .index 1] componentInputPaths
  let parameterOwnership := arrayOwnership
    #[operandArrayOwnership repeatedParameters, repeatedReceiver.ownership, #[]]
  let parameterInputPaths := prefixInputPaths #[.index 0]
      (operandArrayInputPaths repeatedParameters) ++ #[(#[.index 1], repeatedReceiver)]
  let formal ← CellAction.component action receiver.value
  let (source, target) ← CellAction.objects action receiver.value
  let context : CategoryContext := { expression := action.target, bundle := action.targetBundle }
  prepareCallable decoder operation input request formal source target context actualDescriptor
    #[Json.arr parameters, receiver.data, toJson component.inverse]
    (declaration.operands ++ repeatedParameters ++ #[receiver, repeatedReceiver]) wrapper
    descriptorOwnership parameterOwnership descriptorInputPaths parameterInputPaths

def prepareCartesian (decoder : Decoder) (entry : FunctorEntry)
    (input : Form) (template : Json) : TermElabM Prepared := do
  let operation := Operation.cartesian entry
  let request ← invocation operation template
  let (descriptor, wrapper) ← callableDescriptor request.arrow
  let .ok selectedMap := Backend.CartesianMap.decode descriptor
    | malformed "the cartesian service omitted its reindex action, parameters or receiver"
  unless selectedMap.reindex == entry.id.raw do
    malformed "the cartesian service changed its complete registered reindex action"
  let declaration ← decoder.declaration entry.declaration selectedMap.parameters
  let receiver ← decoder.object selectedMap.receiver
  let action ← Semantic.asFunctor declaration.application.value
  discard <| Semantic.objOf action receiver.value
  let closed ← DirectConstruction.close declaration.application
  let action ← instantiateMVars (← Semantic.asFunctor closed.value)
  let (sourceBundle, _) ← functorCategoryBundles action
  let sourceContext : CategoryContext := { expression := entry.source, bundle := sourceBundle }
  CategoryContext.checkObject sourceContext receiver.value
  checkContext sourceContext receiver
  let parametersSyntax ← closed.explicit.mapM exprToSyntax
  -- ReindexAction checks the whole declared action, the actual base morphism and
  -- complete source fibre. Neither a carrier nor the resulting image selects it.
  let mut plans : Array ReindexAction.Plan := #[]
  for operand in declaration.operands do
    let candidate ← try
      withoutModifyingState (some <$> ReindexAction.select entry parametersSyntax
        operand.value sourceContext)
    catch error =>
      if Exception.interpretationKind error == .invalid then pure none else throw error
    if let some candidate := candidate then plans := plans.push candidate
  let #[plan] := plans
    | malformed "the cartesian request has no unique complete declared base-morphism argument"
  let (formal, source, target) ← ReindexAction.cartesian plan receiver.value
  let #[parameterData, receiverData] := request.parameters
    | malformed "the cartesian invocation omitted its complete parameters or original receiver"
  let .ok parameterData := parameterData.getArr?
    | malformed "the cartesian declaration parameters are not ordered data"
  unless parameterData.size == declaration.operands.size do
    malformed "the cartesian invocation changed its complete declaration arity"
  let repeatedParameters ← (declaration.operands.zip parameterData).mapM fun (expected, data) =>
    repeated decoder expected data
  let repeatedReceiver ← repeated decoder receiver receiverData
  let parameters := declaration.operands.map (·.data)
  let actualDescriptor := Backend.CartesianMap.encode {
    reindex := entry.id.raw, parameters, receiver := receiver.data }
  let descriptorOwnership := argsOwnership
    #[#[], operandArrayOwnership declaration.operands, receiver.ownership]
  let descriptorInputPaths := prefixInputPaths #[.field "args", .index 1]
      (operandArrayInputPaths declaration.operands) ++
    #[(#[.field "args", .index 2], receiver)]
  let parameterOwnership := arrayOwnership
    #[operandArrayOwnership repeatedParameters, repeatedReceiver.ownership]
  let parameterInputPaths := prefixInputPaths #[.index 0]
      (operandArrayInputPaths repeatedParameters) ++ #[(#[.index 1], repeatedReceiver)]
  prepareCallable decoder operation input request formal source target plan.total actualDescriptor
    #[Json.arr parameters, receiver.data]
    (declaration.operands ++ repeatedParameters ++ #[receiver, repeatedReceiver]) wrapper
    descriptorOwnership parameterOwnership descriptorInputPaths parameterInputPaths

partial def pointData (json : Json) : Bool :=
  match ComputationalData.envelope json with
  | .ok ("valueData", #[inner]) => pointData inner
  | .ok ("element", _) | .ok ("constrainedPoint", _) => true
  | .ok _ => false
  | .error _ => true

/-- The existing language supplies the selected carrier action and its checked
route comparisons. This service adds no model graph or representation-based
choice of functor, and retains both complete original endpoint objects. -/
def carrierCallable (formal source target : Expr) (context : CategoryContext) :
    TermElabM (Expr × Expr × Expr × CategoryContext) := do
  let selected : Language.Value := .derivedMorphism formal source target context
    (.derivedObject source context #[], .derivedObject target context #[])
  let mapped ← (Language.carrierMorphism selected).run {}
  let (arrow, first, second, targetContext, _, _) ← (Language.morphismContext mapped).run {}
  return (arrow, first, second, targetContext)

def preparePresentation (decoder : Decoder) (entry : PresentationComparisonEntry)
    (input : Form) (template : Json) : TermElabM Prepared := do
  let .ok request := Backend.PresentationInvocation.decode template
    | malformed "the presentation service requires its complete five-field request"
  let declaration ← decoder.declaration entry.declaration request.parameters
  let application ← DirectConstruction.close declaration.application
  let formal ← Semantic.presentationArrow entry application.value request.inverse
  let some (source, target) := Language.homEnds? (← inferType formal)
    | malformed "the published presentation lost its complete categorical endpoints"
  let state ← registryState
  let some sourceRow := state.objects.find?
      (·.id == if request.inverse then entry.target else entry.source)
    | malformed "the presentation's selected source object is not published"
  let some targetRow := state.objects.find?
      (·.id == if request.inverse then entry.source else entry.target)
    | malformed "the presentation's selected target object is not published"
  unless sourceRow.category == targetRow.category do
    malformed "the presentation's published endpoints have different categories"
  let some category := state.categories.find? (·.id == sourceRow.category)
    | malformed "the presentation's complete selected category is not published"
  let context ← CategoryContext.ofNamed category source
  CategoryContext.checkMorphism context formal source target
  let sourceData ← selectedObject decoder context source request.source
  let targetData ← selectedObject decoder context target request.target
  let argument ← try decoder.arrow request.argument
    catch error =>
      unless pointData request.argument do throw error
      let (_, carrierSource, _, carrierContext) ← carrierCallable formal source target context
      let terminal ← Language.globalPointSource.run {}
      decoder.argument (← CategoryContext.hom carrierContext terminal carrierSource) request.argument
  -- The complete original callable determines whether this is application in
  -- the category itself or along its already published carrier functor.
  let inCategory ← withoutModifyingState do
    try
      checkContext context argument
      discard <| CategoryContext.morphismDomain context argument.value source
      pure true
    catch _ => pure false
  let (action, actionSource, actionTarget, actionContext) ← if inCategory then
    pure (formal, source, target, context)
    else carrierCallable formal source target context
  checkContext actionContext argument
  let domain ← CategoryContext.morphismDomain actionContext argument.value actionSource
  let domainData ← decoder.endpoint argument true
  let argumentTarget ← decoder.endpoint argument false
  checkContext actionContext domainData
  checkContext actionContext argumentTarget
  sameValue domain domainData.value
  sameValue actionSource argumentTarget.value
  if inCategory && (argumentTarget.data != sourceData.data ||
      argumentTarget.ownership != sourceData.ownership) then
    malformed "the presentation argument changed the actual selected source data or opaque ownership"
  let result ← composite actionContext domain actionSource actionTarget argument.value action
  let terminal ← Language.globalPointSource.run {}
  let closedPoint ← withoutModifyingState (withTransparency .all <| isDefEq domain terminal)
  let parameters := declaration.operands.map (·.data)
  let actual : Backend.PresentationInvocation := {
    parameters, inverse := request.inverse
    source := sourceData.data, target := targetData.data, argument := argument.data }
  let requestOwnership := argsOwnership #[operandArrayOwnership declaration.operands, #[],
    sourceData.ownership, targetData.ownership, argument.ownership]
  let form ← if closedPoint then pure (.element (.object targetRow))
    else resultForm actionContext input
  return {
    requestValue := result, request := actual.encode, requestOwnership, result
    inputPaths := prefixInputPaths #[.field "args", .index 0]
      (operandArrayInputPaths declaration.operands) ++
      #[(#[.field "args", .index 2], sourceData), (#[.field "args", .index 3], targetData),
        (#[.field "args", .index 4], argument)]
    resultForm := form
    dependencies := declaration.operands ++ #[sourceData, targetData, argument, domainData, argumentTarget]
    resultContext := some actionContext, callableResult := !closedPoint
    pointResult := closedPoint
    callableInterface := some (.endpoints domain actionTarget
      domainData.fragment targetData.fragment)
    callableEndpointOperands := if inCategory then some (domainData, targetData) else none
    complete := fun answer => do
      let checked ← if closedPoint then
        ComputationalData.validateElementAt target targetData.data result answer
        else ComputationalData.validateEndpointPort result domainData.data targetData.data answer
      return checked.map (fun _ => none) }

/-- These families reuse the published complete request and existing formal
selection helpers. Non-owned families are handled by the other shared preparers. -/
def prepare? (decoder : Decoder) (operation : Operation) (input : Form) (template : Json) :
    TermElabM (Option Prepared) := do
  match operation with
  | .cellComponent entry constructors => some <$> prepareCell decoder entry constructors input template
  | .cartesian entry => some <$> prepareCartesian decoder entry input template
  | .presentation entry => some <$> preparePresentation decoder entry input template
  | _ => pure none

end CasCatalogue.StructuredServiceRequest
