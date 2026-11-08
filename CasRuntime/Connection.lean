module

public import CasRuntime.Owner
public import CasRuntime.Deadline
public import CasContract.Port
public import Std.Sync.Semaphore

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

private inductive LeaseStatus
  | allocated | sent | draining | received | discardQueued | discarding | discarded
  | discardFailed (reason : String)
  | committed | abandoned

private structure RequestResource where
  status : LeaseStatus
  cleanup : Option (Task (Except IO.Error Unit)) := none

private structure FramedState where
  nextRequest : Nat := 0
  active : Option Nat := none
  closed : Bool := false
  requests : Std.HashMap Nat RequestResource := {}

/-- One actually negotiated process, one native frame permit and resource-only request status. -/
structure FramedConnection where
  private mk ::
  connection : Connection
  backend : String
  ready : ReadyV2
  private owners : OwnerRegistry
  private permit : Std.Semaphore
  private state : Std.Mutex FramedState

/-- Cleanup authority for one request; this stores no value graph or completed reply. -/
structure RequestLease where
  private mk ::
  requestId : Nat
  transaction : RuntimeId .transaction
  occurrence : RuntimeId .occurrence
  private wire : FramedConnection

def RequestLease.owner (lease : RequestLease) : ConnectionGeneration :=
  lease.wire.connection.generation

opaque FramedConnection.close (wire : FramedConnection) : IO Unit := do
  wire.state.atomically do modify fun state => { state with closed := true }
  wire.owners.close wire.connection.generation

/-- Race negotiation against the caller's explicit deadline, without a computational write.
Reuse: CasContract.negotiateV2 and the native task/event-loop deadline helper. -/
opaque FramedConnection.start (owners : OwnerRegistry) (backend : String)
    (arguments : IO.Process.SpawnArgs) (timeoutMs : UInt32) :
    IO (Except PortError FramedConnection) := do
  if timeoutMs == 0 then return .error (.unavailable backend "incompatible_protocol: deadline")
  let connection ← try owners.spawn arguments
    catch error => return .error (.unavailable backend s!"startup: {error}")
  let negotiation ← IO.asTask (prio := .dedicated) <|
    negotiateV2 backend connection.child.stdin connection.child.stdout
  let result ← awaitBefore negotiation timeoutMs
  match result with
  | some (.ok (.ok ready)) =>
    unless ← owners.isLive connection.generation do
      return .error (.unavailable backend "incompatible_protocol: connection_lost")
    return .ok ⟨connection, backend, ready, owners, ← Std.Semaphore.new 1, ← Std.Mutex.new {}⟩
  | none =>
    owners.close connection.generation
    return .error (.unavailable backend "incompatible_protocol: deadline")
  | some (.error error) =>
    owners.close connection.generation
    return .error (.unavailable backend s!"incompatible_protocol: {error}")
  | some (.ok (.error error)) =>
      owners.close connection.generation
      return .error error

/-- The semaphore covers complete frames and request-local cleanup, never a short state mutex. -/
opaque FramedConnection.acquire (wire : FramedConnection) : IO Unit := do
  let acquired ← wire.permit.acquire
  let some () ← IO.wait acquired.result?
    | throw <| IO.userError "the connection permit was dropped"

opaque FramedConnection.release (wire : FramedConnection) : BaseIO Unit := do
  wire.state.atomically do modify fun state => { state with active := none }
  wire.permit.release

def FramedConnection.isBusy (wire : FramedConnection) : BaseIO Bool := do
  return (← wire.permit.availablePermits) == 0

opaque FramedConnection.hasOutstanding (wire : FramedConnection) : BaseIO Bool :=
  wire.state.atomically do
    if (← get).closed then return false
    return (← get).requests.any fun _ resource => match resource.status with
      | .sent | .draining => true
      | _ => false

opaque FramedConnection.isDraining (wire : FramedConnection) : BaseIO Bool :=
  wire.state.atomically do
    if (← get).closed then return false
    return (← get).requests.any fun _ resource => match resource.status with
      | .draining | .discardQueued | .discarding => true
      | _ => false

/-- Allocate under the held frame permit. IDs remain consumed even if dispatch later fails. -/
opaque FramedConnection.beginRequest (wire : FramedConnection)
    (transaction : RuntimeId .transaction) (occurrence : RuntimeId .occurrence) :
    IO (Except PortError RequestLease) :=
  wire.state.atomically do
    let state ← get
    if state.closed then return .error (.unavailable wire.backend "stale_owner")
    unless state.active.isNone &&
        transaction.worker == wire.connection.generation.worker &&
        occurrence.worker == wire.connection.generation.worker do
      throw <| IO.userError "the connection cannot allocate this request"
    let id := state.nextRequest
    set { state with
      nextRequest := id + 1, active := some id,
      requests := state.requests.insert id { status := .allocated } }
    return .ok ⟨id, transaction, occurrence, wire⟩

opaque RequestLease.markSent (lease : RequestLease) : BaseIO Bool :=
  lease.wire.state.atomically do
    let state ← get
    let some resource := state.requests[lease.requestId]? | return false
    let .allocated := resource.status | return false
    set { state with requests := state.requests.insert lease.requestId { resource with status := .sent } }
    return true

opaque RequestLease.abandon (lease : RequestLease) : BaseIO Unit :=
  lease.wire.state.atomically do
    let state ← get
    let some resource := state.requests[lease.requestId]? | return
    let .allocated := resource.status | return
    set { state with requests := state.requests.insert lease.requestId { status := .abandoned } }

/-- Decide whether the completed frame still belongs to an active request or must be drained. -/
opaque RequestLease.readCompleted (lease : RequestLease) : BaseIO Bool :=
  lease.wire.state.atomically do
    let state ← get
    let some resource := state.requests[lease.requestId]? | return false
    match resource.status with
    | .sent =>
      set { state with requests := state.requests.insert lease.requestId { resource with status := .received } }
      return true
    | .draining =>
      set { state with requests := state.requests.insert lease.requestId { resource with status := .discarding } }
      return false
    | _ => return false

private def discardAck (id : Nat) (json : Json) : Except String Unit := do
  checkServiceFields #["request_id", "status", "disposed"] json
  unless (← json.getObjValAs? Nat "request_id") == id &&
      (← json.getObjValAs? String "status") == "ok" &&
      (← json.getObjValAs? Bool "disposed") do
    throw "the cleanup acknowledgement does not match its request"

/-- The caller holds the frame permit. A cleanup has its own fresh transport ID.
Reference: execution contract v2 section 7; reuse the existing framed byte transport. -/
private def discardOnPermit (lease : RequestLease) : IO Unit := do
  let wire := lease.wire
  let cleanupId ← wire.state.atomically do
    let state ← get
    let id := state.nextRequest
    set { state with nextRequest := id + 1 }
    return id
  let outcome ← try
    writeFrame wire.connection.child.stdin <| Json.mkObj [
      ("protocol", toJson (2 : Nat)), ("request_id", toJson cleanupId),
      ("op", .str "$cas.discard"), ("discard_request_id", toJson lease.requestId)]
    match ← readFrame wire.connection.child.stdout with
    | .ok frame => pure (discardAck cleanupId frame)
    | .error error =>
      wire.close
      pure (.error error.render)
  catch error =>
    wire.close
    pure (.error error.toString)
  wire.state.atomically do
    modify fun state => { state with requests := state.requests.insert lease.requestId {
      status := match outcome with | .ok () => .discarded | .error reason => .discardFailed reason } }

/-- Finish cleanup while retaining the original outstanding frame's permit. -/
opaque RequestLease.discardAfterDrain (lease : RequestLease) : IO Unit :=
  discardOnPermit lease

/-- Abort keeps sent readers running. Received replies instead schedule resource-only cleanup.
Only request identity, actual channels and lease status enter the cleanup task.
Lean IO tasks continue after their caller detaches; no mathematical payload is retained here. -/
opaque RequestLease.cancel (lease : RequestLease) : BaseIO Unit :=
  lease.wire.state.atomically do
    let state ← get
    let some resource := state.requests[lease.requestId]? | return
    if state.closed then
      set { state with requests := state.requests.insert lease.requestId {
        status := .discardFailed "connection_lost" } }
      return
    match resource.status with
    | .sent =>
      set { state with requests := state.requests.insert lease.requestId { resource with status := .draining } }
    | .received =>
      let task ← IO.asTask (prio := .dedicated) do
        lease.wire.acquire
        try discardOnPermit lease
        finally lease.wire.release
      set { state with requests := state.requests.insert lease.requestId {
        status := .discardQueued, cleanup := some task } }
    | .allocated =>
      set { state with requests := state.requests.insert lease.requestId { status := .abandoned } }
    | _ => pure ()

opaque RequestLease.canCommit (lease : RequestLease) : BaseIO Bool :=
  lease.wire.state.atomically do
    let some resource := (← get).requests[lease.requestId]? | return false
    return resource.status matches .received

private partial def commitLeaseGroups [Monad m] [MonadLiftT BaseIO m]
    [MonadLiftT (ST IO.RealWorld) m] [MonadFinally m]
    (leases : Array RequestLease) (action : m α) : m (Option α) := do
  let some first := leases[0]? | return some (← action)
  let group := leases.filter (·.owner == first.owner)
  let remaining := leases.filter (·.owner != first.owner)
  first.wire.state.atomically do
    let state ← get
    unless group.all (fun lease => match state.requests[lease.requestId]? with
        | some resource => (resource.status matches .received)
        | none => false) do return none
    let result ← commitLeaseGroups remaining action
    if result.isSome then
      let mut state := state
      for lease in group do
        state := { state with requests := state.requests.insert lease.requestId { status := .committed } }
      set state
    return result

/-- Promote every received request lease with one publication decision, or promote none.
Group a connection once and lock connections in generation order to prevent lock cycles.
Reuse: Lean Std.Mutex.atomically and the existing request-resource states. No engine I/O runs here.
Lock-order reference: Oracle Multithreaded Programming Guide, Using Locking Hierarchies,
https://docs.oracle.com/cd/E19455-01/806-5257/sync-ex-3/index.html . -/
opaque RequestLease.commitAll [Monad m] [MonadLiftT BaseIO m]
    [MonadLiftT (ST IO.RealWorld) m] [MonadFinally m]
    (transaction : RuntimeId .transaction) (leases : Array RequestLease) (action : m α) :
    m (Option α) := do
  unless leases.all (fun lease => lease.transaction == transaction &&
      lease.owner.worker == transaction.worker) do return none
  commitLeaseGroups (leases.qsort fun left right => left.owner.serial < right.owner.serial) action

opaque FramedConnection.cleanupFailures (wire : FramedConnection) : BaseIO (Array (Nat × String)) :=
  wire.state.atomically do
    return (← get).requests.fold (init := #[]) fun found id resource =>
      match resource.status with
      | .discardFailed reason => found.push (id, reason)
      | _ => found

end CasRuntime
