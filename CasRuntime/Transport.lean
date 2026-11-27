module

public import CasRuntime.Connection
public import CasRuntime.Transaction
public import CasRuntime.Reply

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

private def sameInvocation (left right : DispatchReservation) : Bool :=
  left.occurrence == right.occurrence && left.transaction == right.transaction &&
    left.connection == right.connection && left.selected == right.selected

private def ownsInvocation (wire : FramedConnection) (transaction : CellTransaction)
    (reservation : DispatchReservation) (scope : RequestScope) : Bool :=
  reservation.connection == wire.connection.generation &&
    (match reservation.selected with
      | .primitive selected => selected.registration.backend == wire.backend
      | .native .. => true) &&
    reservation.transaction == transaction.id && sameInvocation scope.reservation reservation

private def DispatchTarget.operation : DispatchTarget → String
  | .primitive selected => selected.registration.operation
  | .native .. => "$cas.invoke_export"

/-- Frame the exact reserved target; native tokens come only from its stored code identity.
Reuse: cas_session._Invoke and _InvokeExport in the pinned public SDK. -/
private def invocationFrame (reservation : DispatchReservation) (scope : RequestScope)
    (requestId : Nat) (arguments : Json) : Json :=
  match reservation.selected with
  | .primitive selected => Json.mkObj [
      ("protocol", toJson (2 : Nat)), ("request_id", toJson requestId),
      ("op", .str selected.registration.operation), ("input", .str selected.registration.input),
      ("args", arguments), ("scope_id", .str scope.wireId)]
  | .native _ token => Json.mkObj [
      ("protocol", toJson (2 : Nat)), ("request_id", toJson requestId),
      ("op", .str "$cas.invoke_export"), ("scope_id", .str scope.wireId),
      ("token", .str token),
      ("captures", .arr ((Array.range scope.captureCount).map fun index =>
        (ScopedReference.scope index).encode)), ("context", arguments)]

/-- The resume of a suspended invocation: a fresh request naming the continuation, with the
declared captures and then the child results as references to the resume scope from zero.
Reuse: cas_session._Resume in the pinned public SDK. -/
private def resumeFrame (scope : RequestScope) (continuation : String) (captures results : Nat)
    (requestId : Nat) : Json :=
  let reference := fun (index : Nat) => (ScopedReference.scope index).encode
  Json.mkObj [("protocol", toJson (2 : Nat)), ("request_id", toJson requestId),
    ("op", .str "$cas.resume"), ("continuation", .str continuation),
    ("scope_id", .str scope.wireId),
    ("captures", .arr ((Array.range captures).map reference)),
    ("results", .arr ((Array.range results).map fun index => reference (captures + index)))]

private def failureReply (id : Nat) (operation : String) (frame : Json) : Except PortError Unit := do
  match ← str frame "status" with
  | "error" =>
    (checkServiceFields #["request_id", "status", "kind", "message"] frame).mapError PortError.protocol
    throw (.backend (← str frame "kind") (← str frame "message"))
  | "unsupported" =>
    (checkServiceFields #["request_id", "status", "op"] frame).mapError PortError.protocol
    unless (← str frame "op") == operation do
      throw (.protocol "the unsupported reply changed its consumed operation")
    throw (.unsupported operation)
  | status => throw (.protocol s!"request {id} has an unknown control status {status}")

/-- A complete successful control frame: an immediate value, an ordered deferred group with
its final template, or a suspension with its continuation, declared captures and ordered child
calls (execution contract v2 §6, python-sdk.md "Generator suspension"). A group is validated
before any child runs. -/
inductive InvocationReply
  | immediate (reply : ImmediateReply)
  | deferred (requestId : Nat) (calls : Array Json) (template exports : Json)
  | suspended (requestId : Nat) (continuation : String) (captures calls : Array Json)
      (exports : Json)

/-- Exact released ordinary and graph-control records. This is framing only; complete
native role and argument admission remains at the original child-execution boundary. -/
private def controlArguments (call : Json) : Except String Json := do
  let operation ← call.getObjValAs? String "op"
  if operation == "$cas.project" || operation == "$cas.apply" then
    checkServiceFields #["op", "args"] call
    let arguments ← call.getObjVal? "args"
    if operation == "$cas.project" then
      checkServiceFields #["value", "field"] arguments
      discard <| (← arguments.getObjVal? "field").getNat?
    else
      checkServiceFields #["value", "arguments"] arguments
      discard <| (← arguments.getObjVal? "arguments").getArr?
    let some _ ← ScopedReference.parse? (← arguments.getObjVal? "value")
      | throw "a graph control requires an actual scoped value reference"
    return arguments
  if operation.startsWith "$cas." then
    throw "an ordinary child call cannot use a reserved graph-control address"
  return (← DeferredCall.decode call).arguments

/-- Read and validate the complete deferred control before any child is scheduled.
Exports retain the original scope; only backward child-result positions remain unresolved. -/
private def deferredControl (scope : RequestScope) (actual : DispatchReservation)
    (graph : ValueGraph) (requestId : Nat) (frame value : Json) : IO InvocationReply := do
  IO.ofExcept <| (checkServiceFields #["request_id", "status", "value", "exports"] frame).mapError IO.userError
  IO.ofExcept <| (checkServiceFields #["ctor", "args"] value).mapError IO.userError
  let arguments ← IO.ofExcept <| ((value.getObjVal? "args").bind (·.getArr?)).mapError IO.userError
  let #[calls, template] := arguments
    | throw <| IO.userError "a deferred computation requires its ordered calls and final result template"
  let calls ← IO.ofExcept <| calls.getArr?.mapError IO.userError
  let exports ← IO.ofExcept <| (frame.getObjVal? "exports").mapError IO.userError
  let declared ← ReplyExport.parseControl scope actual graph scope.wireId exports
  for call in calls, index in [:calls.size] do
    let arguments ← IO.ofExcept <| (controlArguments call).mapError IO.userError
    scope.validateReplyTemplate actual graph scope.wireId declared index arguments
  scope.validateReplyTemplate actual graph scope.wireId declared calls.size template
  return .deferred requestId calls template exports

/-- Validate the complete original captures, exports and finite nonempty child group before
retiring its source scope or scheduling a child. Captures use the same exact-address owner as
immediate export captures, retaining distinct equal-valued positions. -/
private def suspendedControl (scope : RequestScope) (actual : DispatchReservation)
    (graph : ValueGraph) (requestId : Nat) (frame : Json) : IO InvocationReply := do
  IO.ofExcept <| (checkServiceFields
    #["request_id", "status", "continuation", "captures", "calls", "exports"] frame).mapError IO.userError
  let continuation ← IO.ofExcept <| (frame.getObjValAs? String "continuation").mapError IO.userError
  if continuation.isEmpty then throw <| IO.userError "a suspension requires its continuation token"
  let captures ← IO.ofExcept <| ((frame.getObjVal? "captures").bind (·.getArr?)).mapError IO.userError
  let references ← captures.mapM fun capture => do
    let some reference ← IO.ofExcept <| (ScopedReference.parse? capture).mapError IO.userError
      | throw <| IO.userError "a declared capture must be a scoped reference"
    return reference
  discard <| scope.capture actual graph scope.wireId references
  let calls ← IO.ofExcept <| ((frame.getObjVal? "calls").bind (·.getArr?)).mapError IO.userError
  if calls.isEmpty then throw <| IO.userError "a suspension requires a nonempty call group"
  let exports ← IO.ofExcept <| (frame.getObjVal? "exports").mapError IO.userError
  let declared ← ReplyExport.parseControl scope actual graph scope.wireId exports
  for call in calls, index in [:calls.size] do
    let arguments ← IO.ofExcept <| (controlArguments call).mapError IO.userError
    scope.validateReplyTemplate actual graph scope.wireId declared index arguments
  return .suspended requestId continuation captures calls exports

/-- Cooperative cancellation settles the cell; its resource leases retain exact frame drainers. -/
opaque FramedConnection.cancel (wire : FramedConnection) (transaction : CellTransaction)
    (reservation : DispatchReservation) : BaseIO Bool := do
  unless reservation.transaction == transaction.id &&
      reservation.connection == wire.connection.generation do return false
  transaction.abort

/-- Send an exact selected primitive or retained export once, before value admission.
For a retained export, arguments is its already prepared invocation context.
The native permit spans the entire frame and cancellation cleanup. All process I/O runs
outside transaction, owner and resource-state mutexes. Receipt construction is a later boundary.
Reuse: CasContract framing/negotiation, native Semaphore, RequestScope and ImmediateReply. -/
private def FramedConnection.exchange (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (operation : String) (commit : RequestLease → BaseIO (Except TransactionFailure Unit))
    (frameFor : Nat → Json) : IO (Except PortError InvocationReply) := do
  let unavailable := fun reason => PortError.unavailable wire.backend reason
  unless ownsInvocation wire transaction reservation scope do
    return .error (unavailable "request_identity_mismatch")
  let some pending ← ledger.pendingFor reservation.occurrence transaction.id
    | return .error (unavailable "reserved_without_receipt")
  unless sameInvocation pending reservation do
    return .error (unavailable "request_identity_mismatch")
  wire.acquire
  try
    unless ← ledger.owners.isLive wire.connection.generation do
      return .error (unavailable "stale_owner")
    let some graph ← transaction.activeGraph
      | return .error (unavailable "cancelled")
    if let .native code token := reservation.selected then
      let some node := graph.find code
        | return .error (.protocol "the retained native code is outside the active graph")
      let .ownedToken owner actual _ := node.payload.data
        | return .error (.protocol "the retained native target has no actual export token")
      unless owner == wire.connection.generation && actual == token do
        return .error (.protocol "the retained native target changed its actual owner or token")
    try discard <| scope.resolveMany reservation graph scope.wireId #[]
    catch error => return .error (.protocol error.toString)
    let lease ← match ← wire.beginRequest transaction.id reservation.occurrence with
      | .ok lease => pure lease
      | .error error => return .error error
    match ← commit lease with
    | .error failure =>
      lease.abandon
      match failure with
      | .settled => return .error (unavailable "cancelled")
      | .reservation .consumed => return .error (unavailable "reserved_without_receipt")
      | .reservation .staleOwner => return .error (unavailable "stale_owner")
      | _ => throw <| IO.userError "internal: the prepared send lost its transaction association"
    | .ok () => pure ()
    try
      writeFrame wire.connection.child.stdin (frameFor lease.requestId)
    catch error =>
      wire.close
      let failure := PortError.disconnected s!"connection_lost_after_send: {error}"
      let won ← transaction.failPort failure
      scope.retire
      return .error (if won then failure else .unavailable wire.backend "request_already_settled")
    let frame ← match ← readFrame wire.connection.child.stdout with
      | .ok frame => pure frame
      | .error error =>
        wire.close
        let won ← transaction.failPort error
        scope.retire
        return .error (if won then error else .unavailable wire.backend "request_already_settled")
    unless (frame.getObjValAs? Nat "request_id").toOption == some lease.requestId do
      wire.close
      let failure := PortError.protocol "the reply does not answer its exact outstanding request"
      let won ← transaction.failPort failure
      scope.retire
      return .error (if won then failure else .unavailable wire.backend "request_already_settled")
    unless ← lease.readCompleted do
      lease.discardAfterDrain
      scope.retire
      return .error (unavailable "cancelled")
    let some current ← transaction.activeGraph
      | scope.retire; return .error (unavailable "cancelled")
    let status := (frame.getObjValAs? String "status").toOption
    let success := status == some "suspended" || status == some "ok"
    let (frame, observations) ←
      if success then
        match splitRoutineObservations wire.ready.routineObservations frame with
        | .ok (control, routines) =>
          pure (control, if wire.ready.routineObservations then some routines else none)
        | .error reason =>
          let failure := PortError.protocol reason
          let won ← transaction.failPort failure
          scope.retire
          return .error (if won then failure else .unavailable wire.backend "request_already_settled")
      else pure (frame, none)
    let result : Except PortError InvocationReply ←
      if status == some "suspended" then
        try
          pure (.ok (← suspendedControl scope reservation current lease.requestId frame))
        catch error => pure (.error (.protocol error.toString))
      else if (frame.getObjValAs? String "status").toOption == some "ok" then
        let value := (frame.getObjVal? "value").toOption.getD .null
        if (value.getObjValAs? String "ctor").toOption == some "deferredData" then
          try
            pure (.ok (← deferredControl scope reservation current lease.requestId frame value))
          catch error => pure (.error (.protocol error.toString))
        else
          try
            pure (.ok (.immediate (← ImmediateReply.parseControl scope reservation current
              scope.wireId lease.requestId frame)))
          catch error => pure (.error (.protocol error.toString))
      else pure <| match failureReply lease.requestId operation frame with
        | .error error => .error error
        | .ok () => .error (.protocol "the control has no immediate result")
    match result with
    | .ok reply =>
      match ← transaction.recordRoutineInvocation scope lease observations with
      | .ok () => return .ok reply
      | .error .settled =>
        scope.retire
        return .error (unavailable "cancelled")
      | .error _ =>
        let failure := PortError.protocol "routine observation lost its actual received-frame identity"
        let won ← transaction.failPort failure
        scope.retire
        return .error (if won then failure else .unavailable wire.backend "request_already_settled")
    | .error error =>
      let won ← transaction.failPort error
      scope.retire
      if !won then return .error (unavailable "request_already_settled")
      return .error error
  finally wire.release

opaque FramedConnection.invokeControl (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) : IO (Except PortError InvocationReply) :=
  wire.exchange ledger transaction reservation scope reservation.selected.operation
    (transaction.commitSend reservation) (invocationFrame reservation scope · arguments)

/-- Resume a suspended invocation on its supplying connection: a fresh request on the same
occurrence, whose reply is again a control (execution contract §6). -/
opaque FramedConnection.resumeControl (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (continuation : String) (captures results : Nat) : IO (Except PortError InvocationReply) :=
  wire.exchange ledger transaction reservation scope "$cas.resume"
    (transaction.commitResume reservation) (resumeFrame scope continuation captures results)

/-- A call deadline aborts its cell while the exact existing reader or queue item survives.
The IO worker retains its permit/reader or queued permit claim and observes transaction abort.
Reuse: the native task/event-loop deadline helper shared with negotiation. -/
private def FramedConnection.before (wire : FramedConnection) (transaction : CellTransaction)
    (reservation : DispatchReservation) (scope : RequestScope) (timeoutMs : UInt32)
    (exchange : IO (Except PortError InvocationReply)) : IO (Except PortError InvocationReply) := do
  unless ownsInvocation wire transaction reservation scope do
    return .error (.unavailable wire.backend "request_identity_mismatch")
  if timeoutMs == 0 then
    let draining ← wire.isDraining
    let failure := PortError.unavailable wire.backend (if draining then "busy_draining" else "deadline")
    let won ← transaction.failPort failure
    scope.retire
    return .error (if won then failure else .unavailable wire.backend "request_already_settled")
  let worker ← IO.asTask (prio := .dedicated) exchange
  match ← awaitBefore worker timeoutMs with
  | some result => IO.ofExcept result
  | none =>
    let draining ← wire.isDraining
    let failure := PortError.unavailable wire.backend (if draining then "busy_draining" else "deadline")
    let won ← transaction.failPort failure
    scope.retire
    return .error (if won then failure else .unavailable wire.backend "request_already_settled")

opaque FramedConnection.invokeControlBefore (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) (timeoutMs : UInt32) : IO (Except PortError InvocationReply) :=
  wire.before transaction reservation scope timeoutMs
    (wire.invokeControl ledger transaction reservation scope arguments)

opaque FramedConnection.resumeControlBefore (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (continuation : String) (captures results : Nat) (timeoutMs : UInt32) :
    IO (Except PortError InvocationReply) :=
  wire.before transaction reservation scope timeoutMs
    (wire.resumeControl ledger transaction reservation scope continuation captures results)

/-- An invocation whose prepared consumer accepts only an immediate value. -/
private def immediateOnly (wire : FramedConnection) (transaction : CellTransaction) (scope : RequestScope)
    (control : Except PortError InvocationReply) : IO (Except PortError ImmediateReply) := do
  match control with
  | .error error => return .error error
  | .ok (.immediate reply) => return .ok reply
  | .ok (.deferred ..) | .ok (.suspended ..) =>
    let failure := PortError.protocol "a deferred control is not an immediate result value"
    let won ← transaction.failPort failure
    scope.retire
    return .error (if won then failure else .unavailable wire.backend "request_already_settled")

opaque FramedConnection.invoke (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) : IO (Except PortError ImmediateReply) := do
  immediateOnly wire transaction scope (← wire.invokeControl ledger transaction reservation scope arguments)

opaque FramedConnection.invokeBefore (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) (timeoutMs : UInt32) : IO (Except PortError ImmediateReply) := do
  immediateOnly wire transaction scope
    (← wire.invokeControlBefore ledger transaction reservation scope arguments timeoutMs)

end CasRuntime
