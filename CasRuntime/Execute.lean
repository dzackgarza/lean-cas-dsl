module

public import CasRuntime.PreparedRequest
public import CasRuntime.Transaction
public import CasRuntime.Association
public import PolyFun.PFunctor.Handler.Stateful

public section

namespace CasRuntime.Execute

open Lean Meta CasCompiler

/-- Check only the actual retained root's transitive owners, including direct kernel returns. -/
def requireAvailable (transaction : CellTransaction) (graph : ValueGraph)
    (binding : ValueBinding) : MetaM Unit := do
  unless ← graph.isAvailable transaction.owners binding do
    CasCatalogue.throwStratum .unavailable "stale_owner"

private def retainResponse (request : PreparedRequest) (transaction : CellTransaction)
    (binding : ValueBinding) : MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  let candidate ← request.admitResult graph binding
  requireAvailable transaction graph candidate.root
  transaction.retain candidate.root
  return candidate

/-- Preserve the transaction failure's existing stratum at execution and final publication. -/
def completionFailure (failure : TransactionFailure) : MetaM α :=
  match failure with
  | .settled => CasCatalogue.throwStratum .unavailable "cancelled"
  | .staleOwner => CasCatalogue.throwStratum .unavailable "stale_owner"
  | .reservation .consumed => CasCatalogue.throwStratum .unavailable "reserved_without_receipt"
  | .detached => CasCatalogue.throwStratum .unavailable "waiter_detached"
  | .producerError tag message =>
    throwError (match tag with
      | some tag => MessageData.tagged tag message
      | none => message)
  | .producerInternal id extra => throw (Exception.internal ⟨id⟩ ⟨extra⟩)
  | .referenceOutsideGraph =>
    throwError "internal: the occurrence belongs to a different prepared request"
  | failure => throwError "internal: completion reuse failed: {repr failure}"

private def reuseResponse (request : PreparedRequest) (transaction : CellTransaction) :
    MetaM (Option (PreparedResponse request)) := do
  let some role := request.roles.results[0]?
    | throwError "internal: a prepared result has no root role"
  match ← transaction.reuse request.occurrence role.role.id with
  | .error failure => completionFailure failure
  | .ok (.ready value) => return some (← retainResponse request transaction value)
  | .ok .unavailable => return none
  | .ok (.pending _) | .ok .running =>
    let waiter ← match ← transaction.watch request.occurrence role.role.id with
      | .error failure => completionFailure failure
      | .ok waiter => pure waiter
    match ← waiter.wait with
    | .error failure => completionFailure failure
    | .ok value => return some (← retainResponse request transaction value)

private def requireFresh (request : PreparedRequest) (transaction : CellTransaction) : MetaM Unit := do
  match ← transaction.isFresh request.occurrence with
  | .error failure => completionFailure failure
  | .ok true => pure ()
  | .ok false => CasCatalogue.throwStratum .unavailable "reserved_without_receipt"

private def executeDemand
    (executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature)
    (request : PreparedRequest) (transaction : CellTransaction) :
    MetaM (PreparedResponse request × CellTransaction) := do
  if let some response ← reuseResponse request transaction then return (response, transaction)
  match ← transaction.claim request.roles.scope with
  | .error failure => completionFailure failure
  | .ok .waiter =>
    let some response ← reuseResponse request transaction
      | throwError "internal: a claimed occurrence lost its producer"
    return (response, transaction)
  | .ok .producer => pure ()
  requireFresh request transaction
  let graph ← transaction.view
  discard <| request.admitInputs graph
  for binding in request.scope do requireAvailable transaction graph binding
  let (response, state) ← executor request transaction
  unless state.id == transaction.id do
    throwError "internal: execution changed the active transaction"
  return (← retainResponse request state response.root, state)

/-- A stored field is a completed demand with its own occurrence and receipt.
Claim it before selection, and publish the same node under its prepared result role.
The completion derives owner dependencies from the selected field, not its whole parent. -/
private def projectStored (request : PreparedRequest) (transaction : CellTransaction)
    (operand : ValueBinding) (index : Nat) :
    MetaM (PreparedResponse request × CellTransaction) := do
  if let some response ← reuseResponse request transaction then return (response, transaction)
  match ← transaction.claim request.roles.scope with
  | .error failure => completionFailure failure
  | .ok .waiter =>
    let some response ← reuseResponse request transaction
      | throwError "internal: a claimed occurrence lost its producer"
    return (response, transaction)
  | .ok .producer => pure ()
  requireFresh request transaction
  let graph ← transaction.view
  let binding ← IO.ofExcept <| (graph.project operand index).mapError IO.userError
  let draft ← transaction.draft
  let (draft, binding) ← request.associateResult transaction.owners.identities
    request.source draft binding
  let response ← request.admitResult draft.view binding
  match ← transaction.installDraft draft with
  | .error failure => completionFailure failure
  | .ok () => pure ()
  match ← transaction.completeKernel request response with
  | .error failure => completionFailure failure
  | .ok association =>
    return (← retainResponse request transaction association.response.root, transaction)

/-- Interpret prepared value actions against the active transaction and current owners.
Visible receipts and staged completions supply actual roots; pending occurrences share a waiter.
Stored projection selects its exact field node before checking that field's dependencies.
Other effects use the required executor under the same prepared request and transaction.
Every returned node passes the prepared environment's native type and dependency checks.
Reuse: PolyFun a5895e45 Handler.Stateful over MetaM, RuntimeEnvironment.checkResult,
ValueGraph and CellTransaction transitions. -/
def interpreter
    (executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature) :
    PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
  fun request transaction => do
    unless request.program.worker == transaction.id.worker &&
        request.occurrence.worker == transaction.id.worker &&
        request.environment.worker == transaction.id.worker do
      throwError "internal: execution belongs to a different worker"
    if let some response ← reuseResponse request transaction then return (response, transaction)
    match request.action with
    | .apply .. | .primitive .. => requireFresh request transaction
    | .project .. => pure ()
    let graph ← transaction.view
    discard <| IO.ofExcept <|
      (graph.requiredOwners (request.scope ++ request.environment.references)).mapError IO.userError
    match request.action with
    | .project operand field =>
      discard <| request.environment.checkResult graph operand.role operand
      let some node := graph.find operand.value
        | throwError "unavailable: the projected value is outside the active graph"
      match node.payload.data with
      | .product _ | .container _ =>
        let some index := field.wireIndex
          | throwError "internal: a proof field reached computational execution"
        projectStored request transaction operand index
      | .closure _ _ | .ownedToken _ _ _ => executeDemand executor request transaction
      | .portable _ =>
        throwError "malformed: the retained value has no record access interface"
    | .apply callable _ _ =>
      discard <| request.environment.checkResult graph callable.role callable
      executeDemand executor request transaction
    | .primitive _ _ => executeDemand executor request transaction

/-- Run the imported dependent FreeM interpreter; failure aborts this cell's entire staging.
Source: PolyFun Handler.Stateful.run, which delegates to CSLib FreeM.liftM. -/
def run {α : Type}
    (executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature)
    (program : OperationalProgram α) (transaction : CellTransaction) : MetaM α := do
  try
    discard <| transaction.view
    let (result, _) ← (interpreter executor).run program transaction
    return result
  catch error =>
    let failure : TransactionFailure ← match error with
      | .error _ message => do
        pure (.producerError ((CasCatalogue.Exception.stratum? error).map (·.tag))
          (← message.toString))
      | .internal id extra => pure (.producerInternal id.idx extra.entries)
    discard <| transaction.fail failure
    throw error

end CasRuntime.Execute
