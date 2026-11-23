module

public import CasRuntime.Demand
public import CasRuntime.Execute
public import CasCompiler.Lower

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

mutual

private partial def Kernel.evaluateSource (kernel : Kernel) : SourceEvaluation :=
  fun sourceSnapshot transaction program context bound expression =>
    lowerTerm {
      ledger := kernel.ledger, transaction, codes := kernel.codes, marks := kernel.marks
      sourceSnapshot
      run := fun program => Execute.run kernel.executor program transaction }
      program context bound expression

/-- Compose prepared demand execution with checked-source lowering for subsequent calls. -/
partial def Kernel.executor (kernel : Kernel) :
    PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
  fun request transaction => do
    return (← kernel.execute kernel.evaluateSource request transaction, transaction)

end

/-- Lower and execute a checked term in the active cell with its actual source bindings
and the original frontend snapshot, when supplied by the source session. Validate the returned
root even when lowering performs no demand, and retain it for the commit-time owner check. -/
opaque Kernel.run (kernel : Kernel) (transaction : CellTransaction) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (sourceSnapshot : Option Json) : MetaM ValueBinding := do
  try
    let program ← kernel.ledger.owners.identities.fresh .program
    let value ← kernel.evaluateSource sourceSnapshot transaction program context bound expression
    let graph ← transaction.view
    Execute.requireAvailable transaction graph value
    transaction.retain value
    return value
  catch error =>
    discard <| (transaction.abort : BaseIO Bool)
    throw error

end CasRuntime
