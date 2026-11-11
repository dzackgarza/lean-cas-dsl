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

/-- A complete successful control frame: an immediate value, or an ordered deferred group with
its final template (execution contract v2 §6). The group is validated before any child runs. -/
inductive InvocationReply
  | immediate (reply : ImmediateReply)
  | deferred (requestId : Nat) (calls : Array Json) (template exports : Json)

/-- Read the whole deferred control: exact fields, the envelope, and backward-only result
references. Reuse: checkServiceFields and validateResultRefs of the released port. -/
private def deferredControl (requestId : Nat) (frame value : Json) : Except String InvocationReply := do
  checkServiceFields #["request_id", "status", "value", "exports"] frame
  checkServiceFields #["ctor", "args"] value
  let #[calls, template] ← (← value.getObjVal? "args").getArr?
    | throw "a deferred computation requires its ordered calls and final result template"
  let calls ← calls.getArr?
  for call in calls, index in [:calls.size] do
    validateResultRefs index (← call.getObjVal? "args")
  validateResultRefs calls.size template
  return .deferred requestId calls template (← frame.getObjVal? "exports")

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
opaque FramedConnection.invokeControl (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) : IO (Except PortError InvocationReply) := do
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
    match ← transaction.commitSend reservation lease with
    | .error failure =>
      lease.abandon
      match failure with
      | .settled => return .error (unavailable "cancelled")
      | .reservation .consumed => return .error (unavailable "reserved_without_receipt")
      | .reservation .staleOwner => return .error (unavailable "stale_owner")
      | _ => throw <| IO.userError "internal: the prepared send lost its transaction association"
    | .ok () => pure ()
    let operation := reservation.selected.operation
    try
      writeFrame wire.connection.child.stdin <|
        invocationFrame reservation scope lease.requestId arguments
    catch error =>
      wire.close
      let failure := PortError.disconnected s!"connection_lost_after_send: {error}"
      discard <| transaction.failPort failure
      scope.retire
      return .error failure
    let frame ← match ← readFrame wire.connection.child.stdout with
      | .ok frame => pure frame
      | .error error =>
        wire.close
        discard <| transaction.failPort error
        scope.retire
        return .error error
    unless (frame.getObjValAs? Nat "request_id").toOption == some lease.requestId do
      wire.close
      let failure := PortError.protocol "the reply does not answer its exact outstanding request"
      discard <| transaction.failPort failure
      scope.retire
      return .error failure
    unless ← lease.readCompleted do
      lease.discardAfterDrain
      scope.retire
      return .error (unavailable "cancelled")
    let some current ← transaction.activeGraph
      | scope.retire; return .error (unavailable "cancelled")
    let result : Except PortError InvocationReply ←
      if (frame.getObjValAs? String "status").toOption == some "ok" then
        let value := (frame.getObjVal? "value").toOption.getD .null
        if (value.getObjValAs? String "ctor").toOption == some "deferredData" then
          pure ((deferredControl lease.requestId frame value).mapError PortError.protocol)
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
      if (← transaction.activeGraph).isNone then
        scope.retire
        return .error (unavailable "cancelled")
      return .ok reply
    | .error error =>
      discard <| transaction.failPort error
      scope.retire
      return .error error
  finally wire.release

/-- A call deadline aborts its cell while the exact existing reader or queue item survives.
The IO worker retains its permit/reader or queued permit claim and observes transaction abort.
Reuse: the native task/event-loop deadline helper shared with negotiation. -/
opaque FramedConnection.invokeControlBefore (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) (timeoutMs : UInt32) : IO (Except PortError InvocationReply) := do
  unless ownsInvocation wire transaction reservation scope do
    return .error (.unavailable wire.backend "request_identity_mismatch")
  if timeoutMs == 0 then
    let draining ← wire.isDraining
    let failure := PortError.unavailable wire.backend (if draining then "busy_draining" else "deadline")
    discard <| transaction.failPort failure
    scope.retire
    return .error failure
  let worker ← IO.asTask (prio := .dedicated) <|
    wire.invokeControl ledger transaction reservation scope arguments
  match ← awaitBefore worker timeoutMs with
  | some result => IO.ofExcept result
  | none =>
    let draining ← wire.isDraining
    let failure := PortError.unavailable wire.backend (if draining then "busy_draining" else "deadline")
    discard <| transaction.failPort failure
    scope.retire
    return .error failure

/-- An invocation whose prepared consumer accepts only an immediate value. -/
private def immediateOnly (transaction : CellTransaction) (scope : RequestScope)
    (control : Except PortError InvocationReply) : IO (Except PortError ImmediateReply) := do
  match control with
  | .error error => return .error error
  | .ok (.immediate reply) => return .ok reply
  | .ok (.deferred ..) =>
    let failure := PortError.protocol "a deferred control is not an immediate result value"
    discard <| transaction.failPort failure
    scope.retire
    return .error failure

opaque FramedConnection.invoke (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) : IO (Except PortError ImmediateReply) := do
  immediateOnly transaction scope (← wire.invokeControl ledger transaction reservation scope arguments)

opaque FramedConnection.invokeBefore (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) (timeoutMs : UInt32) : IO (Except PortError ImmediateReply) := do
  immediateOnly transaction scope
    (← wire.invokeControlBefore ledger transaction reservation scope arguments timeoutMs)

end CasRuntime
