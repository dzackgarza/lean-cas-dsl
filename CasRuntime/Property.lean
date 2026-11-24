module

public import CasRuntime.RoutedMethod
public import CasCompiler.PropertyFamily

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- One complete property source application before any registration is inspected. The native
proposition, exact category parameters and original receiver keep their prepared authority. -/
structure PreparedPropertyRoute where
  private mk ::
  preparation : RoleScope
  family : PropertyFamily
  actions : Array ClosedTerm
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
  withSourceScope request fun context _ => do
    let mut parameters := #[]
    for parameter in application.arguments.extract 0 family.parameterCount do
      let source ← parameter.source.source.inContext context
      let source ← match values[parameter.sourceIndex]?.bind id with
        | some value => markValue kernel.marks value source
        | none =>
          unless parameter.wireIndex.isNone do
            throwError "the property observation lost a computational category parameter"
          pure source
      parameters := parameters.push source
    let actions ← family.specializeActions levels parameters
    let receiverSource := receiverSlot.source.source
    let boundaries ← routedSourceBoundaries family.route (← receiverSource.inContext context)
    return ⟨request.roles.scope, family, ← actions.mapM context.close, receiverSource, receiver, boundaries,
      request.scope⟩

/-- Registration selection retains its exact original source offset. No property derivation
or synthetic computation address is introduced. -/
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

/-- The released property packet is its actual selected receiver. Complete native parameters
and intermediate dependencies remain owned by the same prepared request and reservation. -/
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
  let (receiver, source, dependencies) ← materializeSourcePrefix kernel evaluateSource request
    transaction route.family.route route.actions route.receiverSource route.receiver
    route.dependencies selection.boundary.offset
  let prepared ← sourceReceiverViews kernel evaluateSource request transaction
    selection.boundary.category source receiver
  let views ← InputDescriptorView.collect (← transaction.view) (← kernel.codes.get)
    #[receiver] prepared
  let dependencies := dependencies ++ views.flatMap (·.dependencies)
  return ⟨route.preparation, selection.registration, route.family.entry.id, selection.boundary.offset, receiver,
    dependencies, views⟩

def PreparedPropertyInvocation.roots (invocation : PreparedPropertyInvocation) :
    Array InputPosition :=
  #[{ path := #[], binding := invocation.receiver }]

/-- Encode only the independently retained receiver, under the raw property request grammar.
The root and every nested scoped reference still refer to their original value bindings. -/
def PreparedPropertyInvocation.encode (invocation : PreparedPropertyInvocation)
    (graph : ValueGraph) (connection : ConnectionGeneration) :
    Except String (EncodedInputs × Json) := do
  let encoded ← graph.encodeInputs connection invocation.roots invocation.views
  let #[receiver] := encoded.values
    | throw "the property packet changed its complete receiver arity"
  return (encoded, receiver)

end CasRuntime
