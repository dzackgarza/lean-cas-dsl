module

public import CasCompiler.Program
public import CasRuntime.Transaction
public import PolyFun.PFunctor.Handler.Stateful

public section

namespace CasRuntime.Execute

open CasCompiler

private def requireAvailable (transaction : CellTransaction) (graph : ValueGraph)
    (binding : ValueBinding) : IO Unit := do
  unless ← graph.isAvailable transaction.owners binding do
    throw <| IO.userError "unavailable: stale_owner"

private def retainResponse (request : PreparedRequest) (transaction : CellTransaction)
    (binding : ValueBinding) : IO (CandidateResponse request.source) := do
  let graph ← transaction.view
  let candidate ← IO.ofExcept <|
    (CandidateResponse.ofValue request.source graph binding).mapError IO.userError
  requireAvailable transaction graph candidate.root
  transaction.retain candidate.root
  return candidate

private def executeDemand
    (executor : PFunctor.Handler.Stateful IO CellTransaction OperationalSignature)
    (request : PreparedRequest) (transaction : CellTransaction) :
    IO (CandidateResponse request.source × CellTransaction) := do
  let graph ← transaction.view
  for binding in request.scope do requireAvailable transaction graph binding
  let (response, state) ← executor request transaction
  unless state.id == transaction.id do
    throw <| IO.userError "internal: execution changed the active transaction"
  return (← retainResponse request state response.root, state)

/-- Interpret prepared value actions against the active transaction and current owners.
Stored projection selects its exact field node before checking that field's dependencies.
Other effects use the required executor under the same prepared request and transaction.
Reuse: PolyFun a5895e45 Handler.Stateful, ValueGraph and CellTransaction transitions. -/
def interpreter
    (executor : PFunctor.Handler.Stateful IO CellTransaction OperationalSignature) :
    PFunctor.Handler.Stateful IO CellTransaction OperationalSignature :=
  fun request transaction => do
    unless request.program.worker == transaction.id.worker &&
        request.occurrence.worker == transaction.id.worker &&
        request.environment.worker == transaction.id.worker do
      throw <| IO.userError "internal: execution belongs to a different worker"
    let graph ← transaction.view
    discard <| IO.ofExcept <|
      (graph.requiredOwners (request.scope ++ request.environment.references)).mapError IO.userError
    match request.action with
    | .project operand field =>
      let some node := graph.find operand.value
        | throw <| IO.userError "unavailable: the projected value is outside the active graph"
      match node.payload.data with
      | .product _ | .container _ =>
        let some index := field.wireIndex
          | throw <| IO.userError "internal: a proof field reached computational execution"
        let binding ← IO.ofExcept <| (graph.project operand index).mapError IO.userError
        return (← retainResponse request transaction binding, transaction)
      | .closure _ _ | .ownedToken _ _ _ => executeDemand executor request transaction
      | .portable _ =>
        throw <| IO.userError "malformed: the retained value has no record access interface"
    | .apply callable _ _ =>
      discard <| IO.ofExcept <|
        (CandidateResponse.ofValue callable.role graph callable).mapError IO.userError
      executeDemand executor request transaction
    | .primitive _ _ => executeDemand executor request transaction

/-- Run the imported dependent FreeM interpreter; failure aborts this cell's entire staging.
Source: PolyFun Handler.Stateful.run, which delegates to CSLib FreeM.liftM. -/
def run {α : Type}
    (executor : PFunctor.Handler.Stateful IO CellTransaction OperationalSignature)
    (program : OperationalProgram α) (transaction : CellTransaction) : IO α := do
  try
    discard <| transaction.view
    let (result, _) ← (interpreter executor).run program transaction
    return result
  catch error =>
    discard <| transaction.abort
    throw error

end CasRuntime.Execute
