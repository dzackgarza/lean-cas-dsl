module

public import CasRuntime.Occurrence
public import CasRuntime.Connection
public import Lean.Environment
public import Lean.CoreM

public section

namespace CasRuntime

open Lean

structure OutputBatch where
  private mk ::
  id : RuntimeId .outputBatch
  commit : RuntimeId .commit
  transaction : RuntimeId .transaction
  events : Array Json

/-- The Environment owns the immutable published graph and complete output batches. -/
structure SessionSnapshot where
  private mk ::
  id : RuntimeId .snapshot
  graph : ValueGraph
  outputBatches : Array OutputBatch

/-- Runtime values are local to this worker and are not exported through .olean files.
Reference: Lean v4.33.0 Lean/Environment.lean, `registerEnvExtension` and `EnvExtension.setState`. -/
private initialize snapshotExtension : EnvExtension (Option SessionSnapshot) ←
  registerEnvExtension (pure none)

opaque SessionSnapshot.current : CoreM SessionSnapshot := do
  let some snapshot := snapshotExtension.getState (← getEnv)
    | throwError "the runtime Environment has not been initialized"
  return snapshot

opaque SessionSnapshot.initialize (owners : OwnerRegistry) : CoreM SessionSnapshot := do
  let environment ← getEnv
  if (snapshotExtension.getState environment).isSome then
    throwError "the runtime Environment is already initialized"
  let snapshot : SessionSnapshot :=
    ⟨← owners.identities.fresh .snapshot, ValueGraph.empty owners.identities, #[]⟩
  setEnv (snapshotExtension.setState environment (some snapshot))
  return snapshot

private structure ActiveCell where
  parent : SessionSnapshot
  graph : ValueGraph
  roots : Array ValueBinding := #[]
  events : Array Json := #[]
  reservations : Array DispatchReservation := #[]
  leases : Array RequestLease := #[]

private inductive CellState
  | active (cell : ActiveCell)
  | committed (snapshot : RuntimeId .snapshot)
  | aborted

/-- Isolated tentative reply fields, rooted in one exact active graph revision.
This is storage for validation, not evidence that validation has succeeded. -/
structure CellDraft where
  private mk ::
  private transaction : RuntimeId .transaction
  private identities : IdentitySupply
  private base : ValueGraph
  private graph : ValueGraph
  private roots : Array ValueBinding

def CellDraft.view (draft : CellDraft) : ValueGraph := draft.graph

/-- Append only to this immutable draft; the active transaction remains unchanged.
Reuse: ValueGraph.stage, including fresh identities and derived capture owners. -/
opaque CellDraft.stage (draft : CellDraft) (origin : ValueOrigin) (payload : ValuePayload) :
    IO (CellDraft × ValueBinding) := do
  let (graph, binding) ← draft.graph.stage draft.identities origin payload
  return ({ draft with graph, roots := draft.roots.push binding }, binding)

inductive TransactionFailure
  | settled | staleSnapshot | staleOwner | pendingCalls | referenceOutsideGraph
  | staleDraft | emptyDraft
  | reservation (failure : ReservationFailure)
  deriving BEq, Repr

/-- Active staging is cleared on settlement; only status remains in this object. -/
structure CellTransaction where
  private mk ::
  id : RuntimeId .transaction
  private ledger : OccurrenceLedger
  private state : Std.Mutex CellState

def CellTransaction.owners (transaction : CellTransaction) : OwnerRegistry :=
  transaction.ledger.owners

opaque CellTransaction.begin (ledger : OccurrenceLedger) : CoreM CellTransaction := do
  let parent ← SessionSnapshot.current
  unless parent.graph.worker == ledger.owners.worker do
    throwError "the transaction belongs to a different worker"
  let id ← ledger.owners.identities.fresh .transaction
  return ⟨id, ledger, ← Std.Mutex.new (.active { parent, graph := parent.graph })⟩

opaque CellTransaction.activeGraph (transaction : CellTransaction) : BaseIO (Option ValueGraph) :=
  transaction.state.atomically do
    let .active cell ← get | return none
    return some cell.graph

opaque CellTransaction.view (transaction : CellTransaction) : IO ValueGraph := do
  let some graph ← transaction.activeGraph
    | throw <| IO.userError "the transaction has settled"
  return graph

/-- Begin a reply delta at the currently visible graph, without exposing any new field. -/
opaque CellTransaction.draft (transaction : CellTransaction) : IO CellDraft :=
  transaction.state.atomically do
    let .active cell ← get
      | throw <| IO.userError "the transaction has settled"
    return ⟨transaction.id, transaction.ledger.owners.identities, cell.graph, cell.graph, #[]⟩

/-- Install the complete isolated delta in one owner-checked active-state update.
The caller validates the whole promised interface before this storage transition.
Revision comparison prevents replacing an intervening append or installing a delta twice.
Reuse: the existing transaction/owner lock order and persistent ValueGraph operations. -/
opaque CellTransaction.installDraft (transaction : CellTransaction) (draft : CellDraft) :
    BaseIO (Except TransactionFailure Unit) :=
  transaction.state.atomically do
    let .active cell ← get | return .error .settled
    unless draft.transaction == transaction.id && cell.graph.sameRevision draft.base do
      return .error .staleDraft
    if draft.roots.isEmpty then return .error .emptyDraft
    let .ok dependencies := draft.graph.requiredOwners draft.roots
      | return .error .referenceOutsideGraph
    let installed ← transaction.ledger.owners.atomicallyWhileLive
        (m := Std.AtomicT CellState BaseIO) dependencies do
      set (CellState.active { cell with graph := draft.graph, roots := cell.roots ++ draft.roots })
    return if installed.isSome then .ok () else .error .staleOwner

opaque CellTransaction.stage (transaction : CellTransaction) (origin : ValueOrigin)
    (payload : ValuePayload) : IO ValueBinding :=
  transaction.state.atomically do
    let .active cell ← get
      | throw <| IO.userError "the transaction has settled"
    let (graph, binding) ← cell.graph.stage transaction.ledger.owners.identities origin payload
    set (CellState.active { cell with graph, roots := cell.roots.push binding })
    return binding

/-- Retain an existing visible root for this cell's commit-time owner check.
Reuse: ValueGraph.requiredOwners and the same active transaction gate as new staging. -/
opaque CellTransaction.retain (transaction : CellTransaction) (binding : ValueBinding) : IO Unit :=
  transaction.state.atomically do
    let .active cell ← get
      | throw <| IO.userError "the transaction has settled"
    discard <| IO.ofExcept <| (cell.graph.requiredOwners #[binding]).mapError IO.userError
    set (CellState.active { cell with roots := cell.roots.push binding })

opaque CellTransaction.emit (transaction : CellTransaction) (event : Json) : IO Unit :=
  transaction.state.atomically do
    let .active cell ← get
      | throw <| IO.userError "the transaction has settled"
    set (CellState.active { cell with events := cell.events.push event })

/-- Track the actual reservation so abort can retire its pending locator.
Lock order is transaction, owner registry, then occurrence ledger; no engine I/O enters it. -/
opaque CellTransaction.reserve (transaction : CellTransaction) (occurrence : RuntimeId .occurrence)
    (selected : DispatchIdentity) (connection : Connection) (arguments : Array ValueBinding) :
    BaseIO (Except TransactionFailure DispatchReservation) :=
  transaction.state.atomically do
    let .active cell ← get | return .error .settled
    match ← transaction.ledger.reserve occurrence transaction.id selected connection cell.graph arguments with
    | .error failure => return .error (.reservation failure)
    | .ok reservation =>
      set (CellState.active { cell with reservations := cell.reservations.push reservation })
      return .ok reservation

/-- Arbitrate the one-use send decision against whole-cell abort before any engine write.
Reuse: the reserve lock order, active-cell gate and occurrence send commitment. -/
opaque CellTransaction.commitSend (transaction : CellTransaction)
    (reservation : DispatchReservation) (lease : RequestLease) :
    BaseIO (Except TransactionFailure Unit) :=
  transaction.state.atomically do
    let .active cell ← get | return .error .settled
    unless reservation.transaction == transaction.id && lease.transaction == transaction.id &&
        lease.occurrence == reservation.occurrence && lease.owner == reservation.connection &&
        cell.reservations.any (fun tracked =>
        tracked.occurrence == reservation.occurrence && tracked.connection == reservation.connection &&
        decide (tracked.selected = reservation.selected)) do
      return .error (.reservation .unknownOccurrence)
    match ← transaction.ledger.commitSend reservation with
    | .error failure => return .error (.reservation failure)
    | .ok () =>
      unless ← lease.markSent do return .error (.reservation .consumed)
      set (CellState.active { cell with leases := cell.leases.push lease })
      return .ok ()

/-- Abort discards staging and leaves every reserved dispatch right consumed. -/
opaque CellTransaction.abort (transaction : CellTransaction) : BaseIO Bool :=
  transaction.state.atomically do
    let .active cell ← get | return false
    for reservation in cell.reservations do
      discard <| transaction.ledger.retire reservation
    for lease in cell.leases do lease.cancel
    set CellState.aborted
    return true

/-- Publish the graph and output batch in one Environment update.
The command worker owns the CoreM Environment. Its transaction gate arbitrates commit/abort;
the owner lock covers the liveness check and the decision. Settlement drops active staging. -/
opaque CellTransaction.commit (transaction : CellTransaction) :
    CoreM (Except TransactionFailure SessionSnapshot) := do
  let environment ← getEnv
  let current := snapshotExtension.getState environment
  let outcome : Except TransactionFailure SessionSnapshot ←
      liftM (m := BaseIO) <| transaction.state.atomically do
    let .active cell ← get | return .error .settled
    let some current := current | return .error .staleSnapshot
    unless current.id == cell.parent.id do
      return .error .staleSnapshot
    unless cell.reservations.isEmpty do return .error .pendingCalls
    let .ok dependencies := cell.graph.requiredOwners cell.roots
      | return .error .referenceOutsideGraph
    let owners := transaction.ledger.owners
    let result ← owners.atomicallyWhileLive (m := Std.AtomicT CellState BaseIO) dependencies do
      let commit ← owners.identities.fresh .commit
      let batch : OutputBatch :=
        ⟨← owners.identities.fresh .outputBatch, commit, transaction.id, cell.events⟩
      let snapshot : SessionSnapshot := ⟨← owners.identities.fresh .snapshot,
        cell.graph, cell.parent.outputBatches.push batch⟩
      set (CellState.committed snapshot.id)
      return snapshot
    match result with
    | none =>
      for lease in cell.leases do lease.cancel
      set CellState.aborted
      return .error .staleOwner
    | some snapshot => return .ok snapshot
  match outcome with
  | .error failure => return .error failure
  | .ok snapshot =>
    setEnv (snapshotExtension.setState environment (some snapshot))
    return .ok snapshot

end CasRuntime
