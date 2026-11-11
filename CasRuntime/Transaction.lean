module

public import CasRuntime.Occurrence
public import CasRuntime.Connection
public import CasCompiler.Program
public import CasRuntime.Reply
public import Lean.Environment
public import Lean.CoreM
public import Init.System.Promise

public section

namespace CasRuntime

open Lean

inductive TransactionFailure
  | settled | staleSnapshot | staleOwner | pendingCalls | referenceOutsideGraph
  | staleDraft | emptyDraft | invalidCompletion | detached
  | reservation (failure : ReservationFailure)
  | producerError (stratumTag : Option Name) (message : String)
  | producerInternal (id : Nat) (extra : List (Name × DataValue))
  deriving BEq, Repr

/-- The actual producer of a completed demand: one framed provider invocation, or the kernel's
own evaluation of retained code and stored fields, which sends no frame. -/
inductive CompletionProducer
  | invocation (dispatch : DispatchReservation) (scope : RuntimeId .scope) (requestId : Nat)
  | kernel

/-- Completed native interface admission and its exact provenance.
References point into the ordinary graph; this record owns no second payload heap. -/
structure CompletionAssociation where
  private mk ::
  request : CasCompiler.PreparedRequest
  response : CasCompiler.PreparedResponse request
  inputs : InputRoleMap
  producer : CompletionProducer

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
  readySignals : Std.HashMap (RuntimeId .occurrence) (IO.Promise Unit) := {}
  claims : Std.HashMap (RuntimeId .occurrence) CasCompiler.RoleScope := {}

private inductive CellState
  | active (cell : ActiveCell)
  | committed (snapshot : RuntimeId .snapshot)
  | aborted (failure : TransactionFailure)

private def CellState.failure : CellState → TransactionFailure
  | .aborted failure => failure
  | _ => .settled

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

inductive ReuseDecision
  | ready (binding : ValueBinding)
  | pending (reservation : DispatchReservation)
  | running
  | unavailable

inductive DemandClaim
  | producer | waiter

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
    let state ← get
    let .active cell := state | return .error state.failure
    if let some receipt := cell.parent.receipt occurrence then
      return (← receipt.association.select cell.graph transaction.owners role).map .ready
    if let some completion := cell.completions.find? (·.association.request.occurrence == occurrence) then
      return (← completion.association.select cell.graph transaction.owners role).map .ready
    if let some claimed := cell.claims[occurrence]? then
      unless claimed == role.scope do return .error .referenceOutsideGraph
    if let some pending ← transaction.ledger.pendingFor occurrence transaction.id then
      return .ok (.pending pending)
    if cell.claims.contains occurrence then return .ok .running
    return .ok .unavailable

/-- Claim one producer for the retained preparation before realization reservation.
Other demands share its signal; this grants no wire-send right and stores no payload. -/
opaque CellTransaction.claim (transaction : CellTransaction) (scope : CasCompiler.RoleScope) :
    BaseIO (Except TransactionFailure DemandClaim) := transaction.state.atomically do
  let state ← get
  let .active cell := state | return .error state.failure
  unless scope.program.worker == transaction.id.worker && scope.occurrence.worker == transaction.id.worker &&
      scope.preparation.worker == transaction.id.worker do return .error (.reservation .wrongWorker)
  if let some claimed := cell.claims[scope.occurrence]? then
    unless claimed == scope do return .error .referenceOutsideGraph
    return .ok .waiter
  if let some receipt := cell.parent.receipt scope.occurrence then
    unless receipt.association.request.roles.scope == scope do return .error .referenceOutsideGraph
    return .ok .waiter
  if let some completion := cell.completions.find? (·.association.request.occurrence == scope.occurrence) then
    unless completion.association.request.roles.scope == scope do return .error .referenceOutsideGraph
    return .ok .waiter
  if (← transaction.ledger.pendingFor scope.occurrence transaction.id).isSome then return .ok .waiter
  unless ← transaction.ledger.isFresh scope.occurrence do return .error (.reservation .consumed)
  let signal : IO.Promise Unit ← IO.Promise.new
  set (CellState.active { cell with
    claims := cell.claims.insert scope.occurrence scope
    readySignals := cell.readySignals.insert scope.occurrence signal })
  return .ok .producer

opaque CellTransaction.isFresh (transaction : CellTransaction) (occurrence : RuntimeId .occurrence) :
    BaseIO (Except TransactionFailure Bool) := transaction.state.atomically do
  let state ← get
  let .active _ := state | return .error state.failure
  return .ok (← transaction.ledger.isFresh occurrence)

/-- One waiter has its own detach signal. The shared signal contains no completed result data. -/
structure CompletionWaiter where
  private mk ::
  private transaction : CellTransaction
  private occurrence : RuntimeId .occurrence
  private role : CasCompiler.RoleId
  private ready : IO.Promise Unit
  private detached : IO.Promise Unit

/-- Attach to this transaction's exact occurrence without retaining a completed-value cache.
Reuse: Lean v4.33.0 Init/System/Promise.lean, Promise.new/resolve/result?. -/
opaque CellTransaction.watch (transaction : CellTransaction) (occurrence : RuntimeId .occurrence)
    (role : CasCompiler.RoleId) : BaseIO (Except TransactionFailure CompletionWaiter) :=
  transaction.state.atomically do
    let state ← get
    let .active cell := state | return .error state.failure
    unless role.scope.occurrence == occurrence && role.scope.program.worker == transaction.id.worker do
      return .error .referenceOutsideGraph
    if let some claimed := cell.claims[occurrence]? then
      unless claimed == role.scope do return .error .referenceOutsideGraph
    let ready ← if (cell.parent.receipt occurrence).isSome ||
        cell.completions.any (·.association.request.occurrence == occurrence) then do
      let signal : IO.Promise Unit ← IO.Promise.new
      signal.resolve ()
      pure (some signal)
    else pure cell.readySignals[occurrence]?
    let some ready := ready | return .error (.reservation .consumed)
    return .ok ⟨transaction, occurrence, role, ready, ← IO.Promise.new⟩

/-- Detach only this waiter; the shared producer and other waiters remain active. -/
opaque CompletionWaiter.detach (waiter : CompletionWaiter) : BaseIO Unit :=
  waiter.detached.resolve ()

/-- Wait for a signal, then read the actual result from the still-active transaction.
Settled cells expose no completed data through their waiter handles. -/
opaque CompletionWaiter.wait (waiter : CompletionWaiter) : IO (Except TransactionFailure ValueBinding) := do
  let ready := waiter.ready.result?.map fun _ => false
  let detached := waiter.detached.result?.map fun _ => true
  discard <| IO.waitAny [ready, detached]
  if ← waiter.detached.isResolved then return .error .detached
  match ← waiter.transaction.reuse waiter.occurrence waiter.role with
  | .error failure => return .error failure
  | .ok (.ready value) => return .ok value
  | .ok (.pending _) | .ok .running => return .error .invalidCompletion
  | .ok .unavailable => return .error (.reservation .consumed)

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
      let signal ← match cell.readySignals[occurrence]? with
        | some signal => pure signal
        | none => IO.Promise.new
      set (CellState.active { cell with
        reservations := cell.reservations.push reservation
        readySignals := cell.readySignals.insert occurrence signal })
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
      let signal ← match cell.readySignals[occurrence]? with
        | some signal => pure signal
        | none => IO.Promise.new
      set (CellState.active { cell with
        reservations := cell.reservations.push reservation
        readySignals := cell.readySignals.insert occurrence signal })
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
    if let some claimed := cell.claims[request.occurrence]? then
      unless claimed == request.roles.scope do return .error .invalidCompletion
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
        ⟨request, response, inputs, .invocation dispatch scope.id reply.requestId⟩
      let completion : StagedCompletion := ⟨transaction.id, association⟩
      if let some signal := cell.readySignals[request.occurrence]? then signal.resolve ()
      set (CellState.active { cell with
        graph := draft.graph
        roots := cell.roots ++ draft.roots ++ outputs
        reservations := cell.reservations.filter (·.occurrence != request.occurrence)
        installedDrafts := cell.installedDrafts.insert draft.id
        completions := cell.completions.push completion
        readySignals := cell.readySignals.erase request.occurrence
        claims := cell.claims.erase request.occurrence })
      return .ok association
    if let some (.ok _) := outcome then scope.retire
    return outcome.getD (.error .staleOwner)

/-- Complete a claimed demand that the kernel evaluated from retained code or stored fields.
No dispatch right is consumed and no frame exists. The occurrence leaves the fresh state,
so a later demand cannot dispatch it. Later demands in this cell reuse this completion.
Reuse: the claim, owner gate and completion table of completeReply. -/
opaque CellTransaction.completeKernel (transaction : CellTransaction)
    (request : CasCompiler.PreparedRequest) (response : CasCompiler.PreparedResponse request) :
    MetaM (Except TransactionFailure CompletionAssociation) := do
  let graph ← transaction.view
  let inputs ← request.admitInputs graph
  let response ← request.admitResult graph response.root
  liftM (m := BaseIO) <| transaction.state.atomically do
    let .active cell ← get | return .error .settled
    unless request.program.worker == transaction.id.worker &&
        cell.graph.sameRevision graph do return .error .invalidCompletion
    if cell.completions.any (·.association.request.occurrence == request.occurrence) ||
        (cell.parent.receipt request.occurrence).isSome then return .error .invalidCompletion
    unless cell.claims[request.occurrence]? == some request.roles.scope do
      return .error .invalidCompletion
    if (← transaction.ledger.pendingFor request.occurrence transaction.id).isSome then
      return .error .invalidCompletion
    let outputs := response.roles.references
    let .ok dependencies := cell.graph.requiredOwners (outputs ++ inputs.references)
      | return .error .referenceOutsideGraph
    let outcome : Option CompletionAssociation ← transaction.owners.atomicallyWhileLive
        (m := Std.AtomicT CellState BaseIO) dependencies do
      transaction.ledger.abandon request.occurrence
      let association : CompletionAssociation := ⟨request, response, inputs, .kernel⟩
      if let some signal := cell.readySignals[request.occurrence]? then signal.resolve ()
      set (CellState.active { cell with
        roots := cell.roots ++ outputs
        completions := cell.completions.push ⟨transaction.id, association⟩
        readySignals := cell.readySignals.erase request.occurrence
        claims := cell.claims.erase request.occurrence })
      return association
    return match outcome with
      | some association => .ok association
      | none => .error .staleOwner

/-- Settle with plain diagnostic/status metadata, dropping every staged value and completion.
The first settlement wins. Native exception data use Lean's literal KVMap entries, not message callbacks. -/
opaque CellTransaction.fail (transaction : CellTransaction) (failure : TransactionFailure) : BaseIO Bool :=
  transaction.state.atomically do
    let .active cell ← get | return false
    for claimed in cell.claims.toArray do transaction.ledger.abandon claimed.1
    for reservation in cell.reservations do
      discard <| transaction.ledger.retire reservation
    for lease in cell.leases do lease.cancel
    for signal in cell.readySignals.toArray do signal.2.resolve ()
    set (CellState.aborted failure)
    return true

/-- Abort discards staging and leaves every reserved dispatch right consumed. -/
opaque CellTransaction.abort (transaction : CellTransaction) : BaseIO Bool :=
  transaction.fail .settled

/-- Preserve the released port classifier when a wire failure settles the producer. -/
opaque CellTransaction.failPort (transaction : CellTransaction) (failure : CasCatalogue.Backend.PortError) :
    BaseIO Bool := transaction.fail (.producerError (some failure.stratum.tag)
      s!"{failure.stratum.label}: {failure.render}")

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
    unless cell.reservations.isEmpty && cell.claims.isEmpty do return .error .pendingCalls
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
      set (CellState.aborted .staleOwner)
      return .error .staleOwner
    | some none =>
      for lease in cell.leases do lease.cancel
      set (CellState.aborted .invalidCompletion)
      return .error .invalidCompletion
    | some (some snapshot) => return .ok snapshot
  match outcome with
  | .error failure => return .error failure
  | .ok snapshot =>
    setEnv (snapshotExtension.setState environment (some snapshot))
    return .ok snapshot

end CasRuntime
