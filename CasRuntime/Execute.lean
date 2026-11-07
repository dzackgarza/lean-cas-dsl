module

public import CasCompiler.Program
public import CasRuntime.Transaction
public import PolyFun.PFunctor.Handler.Stateful

public section

namespace CasRuntime.Execute

open Lean Meta CasCompiler

private def requireAvailable (transaction : CellTransaction) (graph : ValueGraph)
    (binding : ValueBinding) : MetaM Unit := do
  unless ← graph.isAvailable transaction.owners binding do
    throwError "unavailable: stale_owner"

private def retainResponse (request : PreparedRequest) (transaction : CellTransaction)
    (binding : ValueBinding) : MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  let candidate ← request.admitResult graph binding
  requireAvailable transaction graph candidate.root
  transaction.retain candidate.root
  return candidate

private def executeDemand
    (executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature)
    (request : PreparedRequest) (transaction : CellTransaction) :
    MetaM (PreparedResponse request × CellTransaction) := do
  let graph ← transaction.view
  discard <| request.admitInputs graph
  for binding in request.scope do requireAvailable transaction graph binding
  let (response, state) ← executor request transaction
  unless state.id == transaction.id do
    throwError "internal: execution changed the active transaction"
  return (← retainResponse request state response.root, state)

/-- Interpret prepared value actions against the active transaction and current owners.
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
        let binding ← IO.ofExcept <| (graph.project operand index).mapError IO.userError
        return (← retainResponse request transaction binding, transaction)
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
    discard <| transaction.abort
    throw error

end CasRuntime.Execute
