module

public import CasRuntime.Value
public import CasContract.Registration

public section

namespace CasRuntime

/-- The already selected registration and frozen profile; this record performs no selection. -/
structure DispatchIdentity where
  manifestDigest : String
  registration : CasCatalogue.Registration
  profileDigest : String
  deriving DecidableEq, Repr

structure DispatchReservation where
  private mk ::
  occurrence : RuntimeId .occurrence
  transaction : RuntimeId .transaction
  selected : DispatchIdentity
  connection : ConnectionGeneration
  dependencies : Array ConnectionGeneration

inductive ReservationFailure
  | wrongWorker | unknownOccurrence | consumed | staleOwner | referenceOutsideGraph
  deriving BEq, Repr

private inductive OccurrenceStatus
  | fresh
  | pending (reservation : DispatchReservation)
  | consumed (reservation : DispatchReservation)

/-- Only resource status and pending locators live here; completed payloads belong to ValueGraph.
Reference: Lean v4.33.0 Std.Sync.Mutex and Std.HashMap. -/
structure OccurrenceLedger where
  private mk ::
  owners : OwnerRegistry
  private state : Std.Mutex (Std.HashMap (RuntimeId .occurrence) OccurrenceStatus)

opaque OccurrenceLedger.new (owners : OwnerRegistry) : BaseIO OccurrenceLedger := do
  return ⟨owners, ← Std.Mutex.new {}⟩

/-- Allocate an invocation before elaboration, normalization or realization selection can merge it. -/
opaque OccurrenceLedger.allocate (ledger : OccurrenceLedger) : BaseIO (RuntimeId .occurrence) := do
  let id ← ledger.owners.identities.fresh .occurrence
  ledger.state.atomically do
    modify fun state => state.insert id .fresh
  return id

/-- Owner retirement and the one-use reservation cannot interleave.
The nested ledger section holds no engine I/O and stores no value or completion payload. -/
opaque OccurrenceLedger.reserve (ledger : OccurrenceLedger) (id : RuntimeId .occurrence)
    (transaction : RuntimeId .transaction) (selected : DispatchIdentity) (connection : Connection)
    (graph : ValueGraph) (arguments : Array ValueBinding) :
    BaseIO (Except ReservationFailure DispatchReservation) := do
  unless id.worker == ledger.owners.worker && transaction.worker == ledger.owners.worker &&
      graph.worker == ledger.owners.worker && connection.generation.worker == ledger.owners.worker do
    return .error .wrongWorker
  let .ok dependencies := graph.requiredOwners arguments
    | return .error .referenceOutsideGraph
  let dependencies := if dependencies.contains connection.generation then dependencies
    else dependencies.push connection.generation
  let result ← ledger.owners.atomicallyWhileLive dependencies <| ledger.state.atomically do
    let state ← get
    match state[id]? with
    | none => return .error .unknownOccurrence
    | some .fresh =>
      let reservation : DispatchReservation :=
        ⟨id, transaction, selected, connection.generation, dependencies⟩
      set (state.insert id (.pending reservation))
      return .ok reservation
    | some (.pending _) | some (.consumed _) => return .error .consumed
  match result with
  | some reserved => return reserved
  | none => return .error .staleOwner

/-- Return only the locator belonging to this exact active transaction. -/
opaque OccurrenceLedger.pendingFor (ledger : OccurrenceLedger) (id : RuntimeId .occurrence)
    (transaction : RuntimeId .transaction) : BaseIO (Option DispatchReservation) :=
  ledger.state.atomically do
    match (← get)[id]? with
    | some (.pending reservation) =>
      return if reservation.transaction == transaction then some reservation else none
    | _ => return none

/-- Retire once. The consumed tombstone remains outside all semantic snapshots. -/
opaque OccurrenceLedger.retire (ledger : OccurrenceLedger) (reservation : DispatchReservation) :
    BaseIO Bool :=
  ledger.state.atomically do
    let state ← get
    let some (.pending active) := state[reservation.occurrence]? | return false
    unless active.transaction == reservation.transaction &&
        active.connection == reservation.connection && decide (active.selected = reservation.selected) do
      return false
    set (state.insert reservation.occurrence (.consumed active))
    return true

end CasRuntime
