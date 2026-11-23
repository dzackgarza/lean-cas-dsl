module

public import CasRuntime.ChildCall
public import CasRuntime.Transport
public import CasRuntime.Materialize
public import CasRuntime.Encode
public import CasRuntime.Presentation
public import CasRuntime.Point
public import CasRuntime.RoutedMethod

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

mutual

/-- Send one prepared invocation on its reserved connection, then admit and stage the whole
reply with its completion. A deferred group runs first, with the provider permit released.
Reuse: FramedConnection.invokeControlBefore and stageCompletion. -/
partial def Kernel.invoke (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (wire : FramedConnection) (reservation : DispatchReservation)
    (encoded : EncodedInputs) (arguments : Json) : MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  let issued ← RequestScope.issue kernel.ledger reservation graph encoded.slots encoded.inputs #[]
  let control ← match ← wire.invokeControlBefore kernel.ledger transaction reservation issued
      arguments kernel.timeoutMs with
    | .ok control => pure control
    | .error error => portFailure error
  let (scope, reply) ← kernel.settle evaluateSource request transaction wire reservation issued
    (fun results => do
      RequestScope.issue kernel.ledger reservation (← transaction.view) encoded.slots
        encoded.inputs results)
    control
  match ← reply.stageCompletion request transaction scope wire.connection
      (some (kernel.resolveFixedInput evaluateSource transaction request.program)) with
  | .error failure => transactionFailure failure
  | .ok association => request.admitResult (← transaction.view) association.response.root

/-- Dispatch a published operation on its selected registration.
`parameters` are the retained family parameters and `bindings` the earlier outputs the selected
field depends on; the request supplies the action arguments. -/
partial def Kernel.invokeRegistration (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (registration : Registration) (role : String)
    (parameters bindings : Array ValueBinding) : MetaM (PreparedResponse request) := do
  let wire ← kernel.connections.get registration.backend
  let graph ← transaction.view
  let inputs ← request.admitInputs graph
  let arguments ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
  let roots : Array InputPosition :=
    parameters.mapIdx (fun index binding =>
      { path := #[.field "parameters", .index index], binding }) ++
    bindings.mapIdx (fun index binding =>
      { path := #[.field "bindings", .index index], binding }) ++
    arguments.mapIdx (fun index binding =>
      { path := #[.field "arguments", .index index], binding })
  let encoded ← IO.ofExcept <|
    (graph.encodeInputs wire.connection.generation roots).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      (parameters ++ bindings ++ arguments) with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  let leading := parameters.size + bindings.size
  kernel.invoke evaluateSource request transaction wire reservation encoded <|
    dependentContext role (encoded.values.extract 0 parameters.size)
      (encoded.values.extract parameters.size leading)
      (encoded.values.extract leading encoded.values.size) (argumentLayouts request) request.source

/-- Invoke a complete named presentation through the ordinary reservation, scope, deferred
control, reply admission and atomic completion lifecycle. Only its published packet differs
from a dependentContext invocation. -/
partial def Kernel.invokePresentation (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (registration : Registration)
    (invocation : PreparedPresentationInvocation) : MetaM (PreparedResponse request) := do
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
  kernel.invoke evaluateSource request transaction wire reservation encoded packet

/-- Dispatch the unique selected routed-method boundary through the existing reservation,
scoped input, suspension and reply-admission machinery, using its published method packet. -/
partial def Kernel.invokeMethod (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction)
    (invocation : PreparedMethodInvocation) : MetaM (PreparedResponse request) := do
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
  kernel.invoke evaluateSource request transaction wire reservation encoded packet

/-- Send the released named-point packet through the same reservation, scope, deferred-reply
and complete typed result admission lifecycle. The original arrow and all declared parameter
owners remain reservation dependencies although the arrow has a named descriptor view. -/
partial def Kernel.invokePoint (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (registration : Registration)
    (invocation : PreparedPointInvocation) : MetaM (PreparedResponse request) := do
  unless registration.operation == invocation.operation &&
      invocation.forms.contains registration.input do
    throwError "the named point invocation changed its selected operation or input form"
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
  kernel.invoke evaluateSource request transaction wire reservation encoded packet

/-- Invoke a retained native export on its original supplying connection.
Source: execution contract v2 §4.1. No registration is searched for a selected callable. -/
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

/-- Follow one invocation's control to its immediate reply. A deferred group is executed. A
suspension's calls run through the production lowerer and executor in the suspending scope,
then the same occurrence is resumed on its supplying connection with the declared captures
and the child results; the resumed control is followed in turn. `issue` forms a scope over the
positions of the scope that issued `control`, with a completed prefix of child results.
Source: execution contract v2 §6; python-sdk.md "Generator suspension". -/
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
    let captured ← scope.resolveMany reservation graph scope.wireId references
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

/-- Execute an ordered deferred group and form its final immediate control.
Source: execution contract v2 §6. Each child has a fresh scope over the original inputs and
the completed prefix of results. The final template is read in a scope over all results and
is then admitted at the parent's prepared role, like an immediate reply. -/
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
