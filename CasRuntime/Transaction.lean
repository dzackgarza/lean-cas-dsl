module

public import CasRuntime.Occurrence
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

private inductive CellState
  | active (cell : ActiveCell)
  | committed (snapshot : RuntimeId .snapshot)
  | aborted

inductive TransactionFailure
  | settled | staleSnapshot | staleOwner | pendingCalls | referenceOutsideGraph
  | reservation (failure : ReservationFailure)
  deriving BEq, Repr

/-- Active staging is cleared on settlement; only status remains in this object. -/
structure CellTransaction where
  private mk ::
  id : RuntimeId .transaction
  private ledger : OccurrenceLedger
  private state : Std.Mutex CellState

opaque CellTransaction.begin (ledger : OccurrenceLedger) : CoreM CellTransaction := do
  let parent ← SessionSnapshot.current
  unless parent.graph.worker == ledger.owners.worker do
    throwError "the transaction belongs to a different worker"
  let id ← ledger.owners.identities.fresh .transaction
  return ⟨id, ledger, ← Std.Mutex.new (.active { parent, graph := parent.graph })⟩

opaque CellTransaction.view (transaction : CellTransaction) : IO ValueGraph :=
  transaction.state.atomically do
    let .active cell ← get
      | throw <| IO.userError "the transaction has settled"
    return cell.graph

opaque CellTransaction.stage (transaction : CellTransaction) (origin : ValueOrigin)
    (payload : ValuePayload) : IO ValueBinding :=
  transaction.state.atomically do
    let .active cell ← get
      | throw <| IO.userError "the transaction has settled"
    let (graph, binding) ← cell.graph.stage transaction.ledger.owners.identities origin payload
    set (CellState.active { cell with graph, roots := cell.roots.push binding })
    return binding

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

/-- Abort discards staging and leaves every reserved dispatch right consumed. -/
opaque CellTransaction.abort (transaction : CellTransaction) : BaseIO Bool :=
  transaction.state.atomically do
    let .active cell ← get | return false
    for reservation in cell.reservations do
      discard <| transaction.ledger.retire reservation
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
      set CellState.aborted
      return .error .staleOwner
    | some snapshot => return .ok snapshot
  match outcome with
  | .error failure => return .error failure
  | .ok snapshot =>
    setEnv (snapshotExtension.setState environment (some snapshot))
    return .ok snapshot

end CasRuntime
