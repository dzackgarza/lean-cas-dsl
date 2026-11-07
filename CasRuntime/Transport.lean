module

public import CasRuntime.Connection
public import CasRuntime.Transaction
public import CasRuntime.Reply

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

private def sameInvocation (left right : DispatchReservation) : Bool :=
  left.occurrence == right.occurrence && left.transaction == right.transaction &&
    left.connection == right.connection && decide (left.selected = right.selected)

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

/-- Cooperative cancellation settles the cell; its resource leases retain exact frame drainers. -/
opaque FramedConnection.cancel (wire : FramedConnection) (transaction : CellTransaction)
    (reservation : DispatchReservation) : BaseIO Bool := do
  unless reservation.transaction == transaction.id &&
      reservation.connection == wire.connection.generation do return false
  transaction.abort

/-- Send an exact selected primitive once and return parsed control, before value admission.
The native permit spans the entire frame and cancellation cleanup. All process I/O runs
outside transaction, owner and resource-state mutexes. Receipt construction is a later boundary.
Reuse: CasContract framing/negotiation, native Semaphore, RequestScope and ImmediateReply. -/
opaque FramedConnection.invoke (wire : FramedConnection) (ledger : OccurrenceLedger)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (arguments : Json) : IO (Except PortError ImmediateReply) := do
  let unavailable := fun reason => PortError.unavailable wire.backend reason
  unless reservation.connection == wire.connection.generation &&
      reservation.selected.registration.backend == wire.backend &&
      reservation.transaction == transaction.id && sameInvocation scope.reservation reservation do
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
    let operation := reservation.selected.registration.operation
    try
      writeFrame wire.connection.child.stdin <| Json.mkObj [
        ("protocol", toJson (2 : Nat)), ("request_id", toJson lease.requestId),
        ("op", .str operation), ("input", .str reservation.selected.registration.input),
        ("args", arguments), ("scope_id", .str scope.wireId)]
    catch error =>
      wire.close
      discard <| transaction.abort
      scope.retire
      return .error (.disconnected s!"connection_lost_after_send: {error}")
    let frame ← match ← readFrame wire.connection.child.stdout with
      | .ok frame => pure frame
      | .error error =>
        wire.close
        discard <| transaction.abort
        scope.retire
        return .error error
    unless (frame.getObjValAs? Nat "request_id").toOption == some lease.requestId do
      wire.close
      discard <| transaction.abort
      scope.retire
      return .error (.protocol "the reply does not answer its exact outstanding request")
    unless ← lease.readCompleted do
      lease.discardAfterDrain
      scope.retire
      return .error (unavailable "cancelled")
    let some current ← transaction.activeGraph
      | scope.retire; return .error (unavailable "cancelled")
    let result : Except PortError ImmediateReply ←
      if (frame.getObjValAs? String "status").toOption == some "ok" then
        try
          pure (.ok (← ImmediateReply.parseControl scope reservation current scope.wireId lease.requestId frame))
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
      discard <| transaction.abort
      scope.retire
      return .error error
  finally wire.release

end CasRuntime
