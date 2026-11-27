module

public import CasRuntime.RoutedMethod
public import CasCompiler.PropertyFamily

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend



structure PreparedPropertyRoute where
  private mk ::
  preparation : RoleScope
  family : PropertyFamily
  actions : Array ClosedTerm
  environment : RuntimeEnvironment
  receiverSource : ClosedTerm
  receiver : ValueBinding
  boundaries : Array RoutedSourceBoundary
  dependencies : Array ValueBinding

opaque PreparedPropertyRoute.prepare (kernel : Kernel) (graph : ValueGraph)
    (request : PreparedRequest) : MetaM PreparedPropertyRoute := do
  let .primitive (.property family) levels := request.action
    | throwError "the property observation lost its accepted native family"
  unless request.source.kind == .typeValue do
    throwError "a property observation requires its native proposition, not a proof"
  discard <| request.admitInputs graph
  let some application := request.application
    | throwError "the property observation lost its complete receiver application"
  let some retained := request.origin.application
    | throwError "the property observation lost its original actual argument table"
  let values := retained.arguments
  unless application.arguments.size == family.parameterCount + 1 &&
      values.size == application.arguments.size do
    throwError "the property observation changed its complete source telescope"
  let some receiver := values[family.parameterCount]?.bind id
    | throwError "the property observation has no actual original receiver"
  let some receiverSlot := application.arguments[family.parameterCount]?
    | throwError "the property observation lost its original receiver position"
  withSourceScope request fun context bound => do
    let selections ← request.environment.selections.inContext context
    let some selectedId := request.selectionBinding
      | throwError "the property request lost its original selected source binding"
    let some originalSelection := selections[selectedId]?
      | throwError "the property request lost its complete original source selection"
    family.checkSelection context selections originalSelection
    request.withArguments kernel.ledger.owners.identities context bound (family.parameterCount + 1)
        fun context bound actual _ => do
      let actions ← family.specializeActions levels (actual.extract 0 family.parameterCount)
      let original ← receiver.selectedSource context
      let selections ← SourceSelectionScope.merge
        (← request.environment.selections.inContext context)
        (← receiver.role.selections.inContext context)
      let boundaries ← routedSourceBoundaries context selections family.route original
      let some receiverSource := actual[family.parameterCount]?
        | throwError "the property observation lost its original receiver position"
      let environment ← RuntimeEnvironment.captureBound request.environment.worker
        context bound graph (some request.environment) selections
      return ⟨request.roles.scope, family, ← actions.mapM context.close, environment,
        ← context.close receiverSource, receiver, boundaries, request.scope⟩



structure SelectedPropertyBoundary where
  private mk ::
  route : PreparedPropertyRoute
  boundary : RoutedSourceBoundary
  registration : Registration

def PreparedPropertyRoute.select (route : PreparedPropertyRoute) (profile : RealizationProfile)
    (manifest : Manifest) : MetaM SelectedPropertyBoundary := do
  let (offset, registration) ← selectRegistrationBoundary profile manifest
    (.property route.family.entry.id) route.family.entry.id.raw (route.boundaries.map (·.forms))
  let some boundary := route.boundaries[offset]?
    | throwError "the selected property boundary is outside its original route"
  unless boundary.offset == offset && offset <= route.family.route.refs.size do
    throwError "the selected property boundary changed its original source position"
  return ⟨route, boundary, registration⟩



structure PreparedPropertyInvocation where
  private mk ::
  preparation : RoleScope
  registration : Registration
  property : PropertyId
  offset : Nat
  receiver : ValueBinding
  dependencies : Array ValueBinding
  views : Array InputDescriptorView

def SelectedPropertyBoundary.materialize (selection : SelectedPropertyBoundary) (kernel : Kernel)
    (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM PreparedPropertyInvocation := do
  let route := selection.route
  request.requirePreparation route.preparation
  let (receiver, source, dependencies, environment) ← materializeSourcePrefix kernel evaluateSource request
    transaction route.family.route route.family.actionFamilies route.actions route.receiverSource route.receiver
    route.dependencies selection.boundary.offset route.environment
  unless route.family.receiverViews.size == route.family.route.refs.size + 1 do
    throwError "the property lost its complete original category-constructor positions"
  let some receiverView := route.family.receiverViews[selection.boundary.offset]?
    | throwError "the property receiver lost its original selected route position"
  let prepared ← sourceReceiverViews kernel evaluateSource request transaction
    selection.boundary.category receiverView source receiver environment
  let views ← InputDescriptorView.collect (← transaction.view) (← kernel.codes.get)
    #[receiver] prepared
  let dependencies := dependencies ++ views.flatMap (·.dependencies)
  return ⟨route.preparation, selection.registration, route.family.entry.id, selection.boundary.offset, receiver,
    dependencies, views⟩

def PreparedPropertyInvocation.roots (invocation : PreparedPropertyInvocation) :
    Array InputPosition :=
  #[{ path := #[], binding := invocation.receiver }]



def PreparedPropertyInvocation.encode (invocation : PreparedPropertyInvocation)
    (graph : ValueGraph) (connection : ConnectionGeneration) :
    Except String (EncodedInputs × Json) := do
  let encoded ← graph.encodeInputs connection invocation.roots invocation.views
  let #[receiver] := encoded.values
    | throw "the property packet changed its complete receiver arity"
  return (encoded, receiver)

end CasRuntime
