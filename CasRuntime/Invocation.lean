module

public import CasRuntime.ChildCall
public import CasRuntime.Transport
public import CasRuntime.Materialize
public import CasRuntime.Encode
public import CasRuntime.Presentation
public import CasRuntime.Point
public import CasRuntime.RoutedMethod
public import CasRuntime.Property
public import CasRuntime.Limit
public import CasRuntime.Creation

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

mutual




partial def Kernel.invoke (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (wire : FramedConnection) (reservation : DispatchReservation)
    (encoded : EncodedInputs) (arguments : Json)
    (codec : Option (PreparedResultCodec request.roles.scope) := none) :
    MetaM (PreparedResponse request) := do
  let codec ← match codec with
    | some codec => pure codec
    | none => PreparedResultCodec.forNative request (preparedSymbolicCheck kernel request transaction)
  let codec := some codec
  let graph ← transaction.view
  let issued ← RequestScope.issue kernel.ledger reservation graph encoded.slots encoded.inputs #[]
  let selected := match reservation.selected with
    | .primitive identity => Json.mkObj [
      ("kind", toJson "registration"), ("operation", toJson identity.registration.operation),
      ("input", toJson identity.registration.input), ("backend", toJson identity.registration.backend),
      ("manifestDigest", toJson identity.manifestDigest), ("profileDigest", toJson identity.profileDigest)]
    | .native value _ => Json.mkObj [
      ("kind", toJson "native"), ("value", Observation.identityJson value)]
  CasTools.Diagnostics.emit "dispatch" <| Json.mkObj [
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("scope", Observation.identityJson issued.id),
    ("connection", Json.mkObj [("worker", toJson reservation.connection.worker),
      ("serial", toJson reservation.connection.serial)]),
    ("selected", selected), ("operands", arguments),
    ("request", request.observation.toJson)]
  let control ← match ← wire.invokeControlBefore kernel.ledger transaction reservation issued
      arguments kernel.timeoutMs with
    | .ok control => pure control
    | .error error => portFailure error
  let (scope, reply) ← kernel.settle evaluateSource request transaction wire reservation issued
    (fun results => do
      RequestScope.issue kernel.ledger reservation (← transaction.view) encoded.slots
        encoded.inputs results)
    control
  CasTools.Diagnostics.emit "reply.admission.started" <| Json.mkObj [
    ("occurrence", Observation.identityJson request.occurrence),
    ("scope", Observation.identityJson reply.scopeId), ("requestId", toJson reply.requestId),
    ("reply", reply.value)]
  try
    match ← reply.stageCompletion request transaction scope wire.connection
        (some (kernel.resolveFixedInput evaluateSource transaction request.program)) codec with
    | .error failure => transactionFailure failure
    | .ok association =>
      let admitted ← request.admitResult (← transaction.view) association.response.root
      CasTools.Diagnostics.emit "reply.admitted" <| Json.mkObj [
        ("occurrence", Observation.identityJson request.occurrence),
        ("value", Observation.valueIdentityJson admitted.root)]
      return admitted
  catch error =>
    CasTools.Diagnostics.emit "reply.rejected" <| Json.mkObj [
      ("occurrence", Observation.identityJson request.occurrence),
      ("detail", toJson (← error.toMessageData.toString))]
    throw error




partial def Kernel.invokeRegistration (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (registration : Registration) (role : String)
    (parameters : Array ValueBinding) (bindings : Array (Nat × ValueBinding)) :
    MetaM (PreparedResponse request) := do
  let wire ← kernel.connections.get registration.backend
  let graph ← transaction.view
  let inputs ← request.admitInputs graph
  let arguments ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
  let roots : Array InputPosition :=
    parameters.mapIdx (fun index binding =>
      { path := #[.field "parameters", .index index], binding }) ++
    bindings.mapIdx (fun index binding =>
      { path := #[.field "bindings", .index index, .field "value"], binding := binding.2 }) ++
    arguments.mapIdx (fun index binding =>
      { path := #[.field "arguments", .index index], binding })
  let encoded ← IO.ofExcept <|
    (graph.encodeInputs wire.connection.generation roots).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      (parameters ++ bindings.map (·.2) ++ arguments) with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  CasTools.Diagnostics.emit "request.dispatched" <| Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("operation", toJson registration.operation),
    ("registration", Json.mkObj [("operation", toJson registration.operation),
      ("input", toJson registration.input), ("backend", toJson registration.backend)])]
  let leading := parameters.size + bindings.size
  kernel.invoke evaluateSource request transaction wire reservation encoded <|
    dependentContext role (encoded.values.extract 0 parameters.size)
      (bindings.zipWith (fun binding packet => (binding.1, packet))
        (encoded.values.extract parameters.size leading))
      (encoded.values.extract leading encoded.values.size) (argumentLayouts request) request.source



partial def Kernel.invokeLimit (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (registration : Registration)
    (invocation : PreparedLimitInvocation) : MetaM (PreparedResponse request) := do
  request.requirePreparation invocation.preparation
  unless registration.operation == invocation.family.operation &&
      invocation.forms.contains registration.input do
    throwError "the construction changed its original operation or diagram category"
  let codec ← invocation.resultCodec kernel request transaction registration
  let wire ← kernel.connections.get registration.backend
  let graph ← transaction.view
  invocation.requireInputs request graph
  let (encoded, packet) ← IO.ofExcept <|
    (invocation.encode graph wire.connection.generation).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      invocation.dependencies with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  CasTools.Diagnostics.emit "request.dispatched" <| Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("operation", toJson registration.operation),
    ("registration", Json.mkObj [("operation", toJson registration.operation),
      ("input", toJson registration.input), ("backend", toJson registration.backend)])]
  kernel.invoke evaluateSource request transaction wire reservation encoded packet (some codec)




partial def Kernel.invokeCreation (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (registration : Registration)
    (invocation : PreparedCreationInvocation) : MetaM (PreparedResponse request) := do
  request.requirePreparation invocation.preparation
  unless registration.operation == invocation.family.operation &&
      invocation.forms.contains registration.input do
    throwError "the creation changed its original fixed family or input form"
  let wire ← kernel.connections.get registration.backend
  let graph ← transaction.view
  invocation.requireInputs request graph
  let (encoded, parameters) ← IO.ofExcept <|
    (invocation.encode graph wire.connection.generation).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      invocation.dependencies with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  CasTools.Diagnostics.emit "request.dispatched" <| Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("operation", toJson registration.operation),
    ("registration", Json.mkObj [("operation", toJson registration.operation),
      ("input", toJson registration.input), ("backend", toJson registration.backend)])]
  kernel.invoke evaluateSource request transaction wire reservation encoded
    (dependentContext "" parameters #[] #[] #[] request.source)




partial def Kernel.invokePresentation (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (registration : Registration)
    (invocation : PreparedPresentationInvocation) : MetaM (PreparedResponse request) := do
  request.requirePreparation invocation.preparation
  unless registration.operation == invocation.operation &&
      invocation.forms.contains registration.input do
    throwError "the presentation invocation changed its selected operation or input form"
  let wire ← kernel.connections.get registration.backend
  let graph ← transaction.view
  discard <| request.admitInputs graph
  let (encoded, packet) ← IO.ofExcept <|
    (invocation.encode graph wire.connection.generation).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      invocation.dependencies with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  CasTools.Diagnostics.emit "request.dispatched" <| Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("operation", toJson registration.operation),
    ("registration", Json.mkObj [("operation", toJson registration.operation),
      ("input", toJson registration.input), ("backend", toJson registration.backend)])]
  kernel.invoke evaluateSource request transaction wire reservation encoded packet



partial def Kernel.invokeMethod (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction)
    (invocation : PreparedMethodInvocation) : MetaM (PreparedResponse request) := do
  request.requirePreparation invocation.preparation
  let registration := invocation.registration
  unless registration.operation == invocation.method.raw do
    throwError "the selected method registration changed its published address"
  let graph ← transaction.view
  discard <| request.admitInputs graph
  let wire ← kernel.connections.get registration.backend
  let (encoded, packet) ← IO.ofExcept <|
    (invocation.encode graph wire.connection.generation).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      invocation.dependencies with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  CasTools.Diagnostics.emit "request.dispatched" <| Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("operation", toJson registration.operation),
    ("registration", Json.mkObj [("operation", toJson registration.operation),
      ("input", toJson registration.input), ("backend", toJson registration.backend)])]
  kernel.invoke evaluateSource request transaction wire reservation encoded packet



partial def Kernel.invokeProperty (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction)
    (invocation : PreparedPropertyInvocation) : MetaM (PreparedResponse request) := do
  request.requirePreparation invocation.preparation
  let registration := invocation.registration
  unless registration.operation == invocation.property.raw do
    throwError "the selected property registration changed its accepted address"
  let graph ← transaction.view
  discard <| request.admitInputs graph
  let wire ← kernel.connections.get registration.backend
  let (encoded, packet) ← IO.ofExcept <|
    (invocation.encode graph wire.connection.generation).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      invocation.dependencies with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  CasTools.Diagnostics.emit "request.dispatched" <| Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("operation", toJson registration.operation),
    ("registration", Json.mkObj [("operation", toJson registration.operation),
      ("input", toJson registration.input), ("backend", toJson registration.backend)])]
  kernel.invoke evaluateSource request transaction wire reservation encoded packet




partial def Kernel.invokePoint (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (registration : Registration)
    (invocation : PreparedPointInvocation) : MetaM (PreparedResponse request) := do
  request.requirePreparation invocation.preparation
  unless registration.operation == invocation.operation &&
      invocation.forms.contains registration.input do
    throwError "the named point invocation changed its selected operation or input form"
  let codec ← invocation.resultCodec kernel request transaction registration
  let wire ← kernel.connections.get registration.backend
  let graph ← transaction.view
  invocation.requireInputs request graph
  let (encoded, packet) ← IO.ofExcept <|
    (invocation.encode graph wire.connection.generation).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      invocation.dependencies with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  CasTools.Diagnostics.emit "request.dispatched" <| Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("operation", toJson registration.operation),
    ("registration", Json.mkObj [("operation", toJson registration.operation),
      ("input", toJson registration.input), ("backend", toJson registration.backend)])]
  kernel.invoke evaluateSource request transaction wire reservation encoded packet codec


partial def Kernel.invokeObjectAction (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (registration : Registration)
    (invocation : PreparedObjectAction) : MetaM (PreparedResponse request) := do
  request.requirePreparation invocation.preparation
  unless registration.operation == invocation.operation &&
      invocation.forms.contains registration.input do
    throwError "the object action changed its original operation or input form"
  let wire ← kernel.connections.get registration.backend
  let graph ← transaction.view
  invocation.requireInputs request graph
  let (encoded, packet) ← IO.ofExcept <|
    (invocation.encode graph wire.connection.generation).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      invocation.dependencies with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  CasTools.Diagnostics.emit "request.dispatched" <| Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("transaction", Observation.identityJson transaction.id),
    ("operation", toJson registration.operation),
    ("registration", Json.mkObj [("operation", toJson registration.operation),
      ("input", toJson registration.input), ("backend", toJson registration.backend)])]
  kernel.invoke evaluateSource request transaction wire reservation encoded packet



partial def Kernel.invokeExport (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (callable : ValueBinding) (role : String) :
    MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  let code ← IO.ofExcept <| (graph.callable callable).mapError IO.userError
  let some node := graph.find code.value
    | throwError "internal: the native callable is outside the active graph"
  let .ownedToken owner _ _ := node.payload.data
    | throwError "internal: the retained callable has no native export"
  let wire ← kernel.connections.ofOwner owner
  let inputs ← request.admitInputs graph
  let arguments ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
  let roots : Array InputPosition := arguments.mapIdx fun index binding =>
    { path := #[.field "arguments", .index index], binding }
  let encoded ← IO.ofExcept <|
    (graph.encodeExportInputs wire.connection.generation callable roots).mapError IO.userError
  let reservation ← match ← transaction.reserveExport request.occurrence callable wire.connection
      arguments with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.invoke evaluateSource request transaction wire reservation encoded <|
    dependentContext role #[] #[] encoded.values (argumentLayouts request) request.source







partial def Kernel.settle (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (wire : FramedConnection) (reservation : DispatchReservation)
    (scope : RequestScope) (issue : Array ValueBinding → IO RequestScope)
    (control : InvocationReply) : MetaM (RequestScope × ImmediateReply) := do
  match control with
  | .immediate reply => return (scope, reply)
  | .deferred requestId calls template exports =>
    scope.retire
    kernel.deferred evaluateSource request transaction reservation issue requestId calls template exports
  | .suspended _ continuation captures calls _ =>
    let malformed : {α : Type} → String → MetaM α := fun reason =>
      throwStratum .malformed m!"suspension: {reason}"
    let graph ← transaction.view
    let mut references := #[]
    for capture in captures do
      match ScopedReference.parse? capture with
      | .ok (some reference) => references := references.push reference
      | .ok none => malformed "a declared capture must be a scoped reference"
      | .error reason => malformed reason
    let captured ← scope.capture reservation graph scope.wireId references
    scope.retire
    let mut results : Array ValueBinding := #[]
    for call in calls do
      let child ← issue results
      let value ← try kernel.child evaluateSource request transaction reservation child call
        finally child.retire
      results := results.push value
    let slots := captured ++ results
    let resumed ← RequestScope.issueResume kernel.ledger reservation (← transaction.view) slots #[]
    let next ← match ← wire.resumeControlBefore kernel.ledger transaction reservation resumed
        continuation captured.size results.size kernel.timeoutMs with
      | .ok next => pure next
      | .error error => portFailure error
    kernel.settle evaluateSource request transaction wire reservation resumed
      (fun prior => do
        RequestScope.issueResume kernel.ledger reservation (← transaction.view) slots prior)
      next





partial def Kernel.deferred (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (reservation : DispatchReservation)
    (issue : Array ValueBinding → IO RequestScope)
    (requestId : Nat) (calls : Array Json) (template exports : Json) :
    MetaM (RequestScope × ImmediateReply) := do
  let mut results : Array ValueBinding := #[]
  for call in calls do
    let scope ← issue results
    let value ← try kernel.child evaluateSource request transaction reservation scope call
      finally scope.retire
    results := results.push value
  let graph ← transaction.view
  let scope ← issue results
  let frame := Json.mkObj [("request_id", toJson requestId), ("status", "ok"),
    ("value", template), ("exports", exports)]
  let reply ← try
      liftM (m := IO) <| ImmediateReply.parseControl scope reservation graph scope.wireId
        requestId frame
    catch error => throwStratum .malformed m!"deferred result: {← error.toMessageData.toString}"
  return (scope, reply)

end

end CasRuntime
