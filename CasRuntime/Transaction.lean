module

public import CasRuntime.Occurrence
public import CasRuntime.Connection
public import CasCompiler.Program
public import CasRuntime.Reply
public import Lean.Environment
public import Lean.CoreM

public section

namespace CasRuntime

open Lean

/-- Completed native interface admission and its exact invocation provenance.
References point into the ordinary graph; this record owns no second payload heap. -/
structure CompletionAssociation where
  private mk ::
  request : CasCompiler.PreparedRequest
  response : CasCompiler.PreparedResponse request
  inputs : InputRoleMap
  dispatch : DispatchReservation
  scope : RuntimeId .scope
  requestId : Nat

structure StagedCompletion where
  private mk ::
  transaction : RuntimeId .transaction
  private association : CompletionAssociation

structure CommittedReceipt where
  private mk ::
  association : CompletionAssociation
  commit : RuntimeId .commit
  snapshot : RuntimeId .snapshot
  outputBatch : RuntimeId .outputBatch

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
  private receipts : Std.HashMap (RuntimeId .occurrence) CommittedReceipt

/-- Inert receipt visibility belongs to this exact immutable Environment snapshot. -/
def SessionSnapshot.receipt (snapshot : SessionSnapshot) (occurrence : RuntimeId .occurrence) :
    Option CommittedReceipt := snapshot.receipts[occurrence]?

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
    ⟨← owners.identities.fresh .snapshot, ValueGraph.empty owners.identities, #[], {}⟩
  setEnv (snapshotExtension.setState environment (some snapshot))
  return snapshot

private structure ActiveCell where
  parent : SessionSnapshot
  graph : ValueGraph
  roots : Array ValueBinding := #[]
  events : Array Json := #[]
  reservations : Array DispatchReservation := #[]
  leases : Array RequestLease := #[]
  installedDrafts : Std.HashSet (RuntimeId .draft) := {}
  completions : Array StagedCompletion := #[]

private inductive CellState
  | active (cell : ActiveCell)
  | committed (snapshot : RuntimeId .snapshot)
  | aborted

/-- Isolated tentative reply fields, rooted in one exact active graph revision.
This is storage for validation, not evidence that validation has succeeded. -/
structure CellDraft where
  private mk ::
  private id : RuntimeId .draft
  private transaction : RuntimeId .transaction
  private identities : IdentitySupply
  private base : ValueGraph
  private graph : ValueGraph
  private roots : Array ValueBinding

def CellDraft.view (draft : CellDraft) : ValueGraph := draft.graph

/-- Retain an existing visible root without allocating a replacement node or installing it.
Reuse: ValueGraph.requiredOwners; installation performs the atomic owner recheck. -/
opaque CellDraft.retain (draft : CellDraft) (binding : ValueBinding) : IO CellDraft := do
  discard <| IO.ofExcept <| (draft.graph.requiredOwners #[binding]).mapError IO.userError
  return { draft with roots := draft.roots.push binding }

/-- Append only to this immutable draft; the active transaction remains unchanged.
Reuse: ValueGraph.stage, including fresh identities and derived capture owners. -/
opaque CellDraft.stage (draft : CellDraft) (origin : ValueOrigin) (payload : ValuePayload) :
    IO (CellDraft × ValueBinding) := do
  let (graph, binding) ← draft.graph.stage draft.identities origin payload
  return ({ draft with graph, roots := draft.roots.push binding }, binding)

/-- Register a field role only in this isolated reply delta.
Reuse: RecordPrefix.bind and the draft's immutable graph extension. -/
opaque CellDraft.bindField (draft : CellDraft) (record : RecordPrefix) (value : ValueBinding) :
    IO (CellDraft × RecordPrefix × ValueBinding) := do
  let (graph, record, binding) ← record.bind draft.graph value
  return ({ draft with graph, roots := draft.roots.push binding }, record, binding)

/-- Retain a reused result and its prepared stored-field views in this isolated reply.
Reuse: ValueGraph.bindApplication and atomic draft installation. -/
opaque CellDraft.bindApplication (draft : CellDraft) (origin : ValueOrigin)
    (value : ValueBinding) (fields : Array ValueBinding) : IO (CellDraft × ValueBinding) := do
  let (graph, binding) ← draft.graph.bindApplication draft.identities origin value fields
  return ({ draft with graph, roots := draft.roots.push binding }, binding)

inductive TransactionFailure
  | settled | staleSnapshot | staleOwner | pendingCalls | referenceOutsideGraph
  | staleDraft | emptyDraft | invalidCompletion
  | reservation (failure : ReservationFailure)
  deriving BEq, Repr

inductive ReuseDecision
  | ready (binding : ValueBinding)
  | pending (reservation : DispatchReservation)
  | unavailable

private def CompletionAssociation.select (association : CompletionAssociation)
    (graph : ValueGraph) (owners : OwnerRegistry) (role : CasCompiler.RoleId) :
    BaseIO (Except TransactionFailure ValueBinding) := do
  unless graph.worker == owners.worker do return .error (.reservation .wrongWorker)
  let .ok value := association.response.roles.lookup graph role
    | return .error .referenceOutsideGraph
  unless ← graph.isAvailable owners value do return .error .staleOwner
  return .ok value

/-- Reuse a visible committed result at the demanded role's own owner closure. -/
opaque SessionSnapshot.reuse (snapshot : SessionSnapshot) (owners : OwnerRegistry)
    (occurrence : RuntimeId .occurrence) (role : CasCompiler.RoleId) :
    BaseIO (Except TransactionFailure (Option ValueBinding)) := do
  let some receipt := snapshot.receipt occurrence | return .ok none
  return (← receipt.association.select snapshot.graph owners role).map some

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

/-- Visible committed receipt, then this cell's completion, then its exact pending locator.
Consumed occurrences never recover a result from the resource ledger. -/
opaque CellTransaction.reuse (transaction : CellTransaction) (occurrence : RuntimeId .occurrence)
    (role : CasCompiler.RoleId) : BaseIO (Except TransactionFailure ReuseDecision) :=
  transaction.state.atomically do
    let .active cell ← get | return .error .settled
    if let some receipt := cell.parent.receipt occurrence then
      return (← receipt.association.select cell.graph transaction.owners role).map .ready
    if let some completion := cell.completions.find? (·.association.request.occurrence == occurrence) then
      return (← completion.association.select cell.graph transaction.owners role).map .ready
    if let some pending ← transaction.ledger.pendingFor occurrence transaction.id then
      return .ok (.pending pending)
    return .ok .unavailable

/-- Begin a reply delta at the currently visible graph, without exposing any new field. -/
opaque CellTransaction.draft (transaction : CellTransaction) : IO CellDraft :=
  transaction.state.atomically do
    let .active cell ← get
      | throw <| IO.userError "the transaction has settled"
    let identities := transaction.ledger.owners.identities
    return ⟨← identities.fresh .draft, transaction.id, identities, cell.graph, cell.graph, #[]⟩

/-- Install the complete isolated delta in one owner-checked active-state update.
The caller validates the whole promised interface before this storage transition.
Revision comparison prevents replacing an intervening append or installing a delta twice.
Reuse: the existing transaction/owner lock order and persistent ValueGraph operations. -/
opaque CellTransaction.installDraft (transaction : CellTransaction) (draft : CellDraft) :
    BaseIO (Except TransactionFailure Unit) :=
  transaction.state.atomically do
    let .active cell ← get | return .error .settled
    unless draft.transaction == transaction.id && cell.graph.sameRevision draft.base &&
        !cell.installedDrafts.contains draft.id do
      return .error .staleDraft
    if draft.roots.isEmpty then return .error .emptyDraft
    let .ok dependencies := draft.graph.requiredOwners draft.roots
      | return .error .referenceOutsideGraph
    let installed ← transaction.ledger.owners.atomicallyWhileLive
        (m := Std.AtomicT CellState BaseIO) dependencies do
      set (CellState.active { cell with
        graph := draft.graph
        roots := cell.roots ++ draft.roots
        installedDrafts := cell.installedDrafts.insert draft.id })
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

/-- Track a retained native export's actual owner and code under the same abort boundary.
Reuse: OccurrenceLedger.reserveExport and the primitive reservation lock order. -/
opaque CellTransaction.reserveExport (transaction : CellTransaction)
    (occurrence : RuntimeId .occurrence) (callable : ValueBinding) (connection : Connection)
    (arguments : Array ValueBinding) : BaseIO (Except TransactionFailure DispatchReservation) :=
  transaction.state.atomically do
    let .active cell ← get | return .error .settled
    match ← transaction.ledger.reserveExport occurrence transaction.id callable connection
        cell.graph arguments with
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
        tracked.selected == reservation.selected) do
      return .error (.reservation .unknownOccurrence)
    match ← transaction.ledger.commitSend reservation with
    | .error failure => return .error (.reservation failure)
    | .ok () =>
      unless ← lease.markSent do return .error (.reservation .consumed)
      set (CellState.active { cell with leases := cell.leases.push lease })
      return .ok ()

/-- Install an admitted whole reply and its transaction-local completion together.
Reuse: prepared input/result admission, isolated drafts, actual received leases and owner gating.
The parsed reply and request scope identify the exact transport invocation. -/
opaque CellTransaction.completeReply (transaction : CellTransaction) (draft : CellDraft)
    (request : CasCompiler.PreparedRequest) (response : CasCompiler.PreparedResponse request)
    (scope : RequestScope) (reply : ImmediateReply) : MetaM (Except TransactionFailure CompletionAssociation) := do
  let inputs ← request.admitInputs draft.view
  let response ← request.admitResult draft.view response.root
  discard <| scope.resolveMany scope.reservation draft.view scope.wireId #[]
  liftM (m := BaseIO) <| transaction.state.atomically do
    let .active cell ← get | return .error .settled
    let dispatch := scope.reservation
    unless reply.scopeId == scope.id && dispatch.transaction == transaction.id &&
        dispatch.occurrence == request.occurrence && request.program.worker == transaction.id.worker &&
        draft.transaction == transaction.id && cell.graph.sameRevision draft.base &&
        !cell.installedDrafts.contains draft.id do return .error .invalidCompletion
    if cell.completions.any (·.association.request.occurrence == request.occurrence) ||
        (cell.parent.receipt request.occurrence).isSome then return .error .invalidCompletion
    unless cell.reservations.any (fun tracked => tracked.occurrence == dispatch.occurrence &&
        tracked.connection == dispatch.connection && tracked.selected == dispatch.selected) do
      return .error .invalidCompletion
    let some lease := cell.leases.find? (fun lease => lease.requestId == reply.requestId &&
        lease.occurrence == request.occurrence && lease.owner == dispatch.connection)
      | return .error .invalidCompletion
    unless ← lease.canCommit do return .error .invalidCompletion
    let outputs := response.roles.references
    let .ok dependencies := draft.graph.requiredOwners
        (draft.roots ++ outputs ++ inputs.references ++ reply.exports.flatMap (·.captures))
      | return .error .referenceOutsideGraph
    let dependencies := dependencies ++ dispatch.dependencies
    let outcome : Option (Except TransactionFailure CompletionAssociation) ← transaction.owners.atomicallyWhileLive
        (m := Std.AtomicT CellState BaseIO) dependencies do
      unless ← transaction.ledger.retire dispatch do return .error .invalidCompletion
      let association : CompletionAssociation :=
        ⟨request, response, inputs, dispatch, scope.id, reply.requestId⟩
      let completion : StagedCompletion := ⟨transaction.id, association⟩
      set (CellState.active { cell with
        graph := draft.graph
        roots := cell.roots ++ draft.roots ++ outputs
        reservations := cell.reservations.filter (·.occurrence != request.occurrence)
        installedDrafts := cell.installedDrafts.insert draft.id
        completions := cell.completions.push completion })
      return .ok association
    if let some (.ok _) := outcome then scope.retire
    return outcome.getD (.error .staleOwner)

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
      RequestLease.commitAll transaction.id cell.leases do
        let commit ← owners.identities.fresh .commit
        let snapshotId ← owners.identities.fresh .snapshot
        let batch : OutputBatch :=
          ⟨← owners.identities.fresh .outputBatch, commit, transaction.id, cell.events⟩
        let mut receipts := cell.parent.receipts
        for completion in cell.completions do
          let association := completion.association
          receipts := receipts.insert association.request.occurrence
            ⟨association, commit, snapshotId, batch.id⟩
        let snapshot : SessionSnapshot :=
          ⟨snapshotId, cell.graph, cell.parent.outputBatches.push batch, receipts⟩
        set (CellState.committed snapshot.id)
        return snapshot
    match result with
    | none =>
      for lease in cell.leases do lease.cancel
      set CellState.aborted
      return .error .staleOwner
    | some none =>
      for lease in cell.leases do lease.cancel
      set CellState.aborted
      return .error .invalidCompletion
    | some (some snapshot) => return .ok snapshot
  match outcome with
  | .error failure => return .error failure
  | .ok snapshot =>
    setEnv (snapshotExtension.setState environment (some snapshot))
    return .ok snapshot

end CasRuntime
