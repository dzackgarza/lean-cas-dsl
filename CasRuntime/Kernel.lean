module

public import CasRuntime.Demand
public import CasRuntime.Execute
public import CasCompiler.Lower

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

mutual

private partial def Kernel.evaluateSource (kernel : Kernel) (sourceSnapshot : Option Json) :
    SourceEvaluation :=
  fun transaction program context bound expression =>
    lowerTerm {
      ledger := kernel.ledger, transaction, codes := kernel.codes, marks := kernel.marks
      sourceSnapshot
      run := fun computation => Execute.run kernel.executor computation transaction
        (some (kernel.resolveFixedInput (kernel.evaluateSource sourceSnapshot) transaction program)) }
      program context bound expression

/-- Compose prepared demand execution with checked-source lowering for subsequent calls. -/
partial def Kernel.executor (kernel : Kernel) :
    PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
  fun request transaction => do
    return (← kernel.execute (kernel.evaluateSource request.observation.sourceSnapshot)
      request transaction, transaction)

end

/-- Lower and execute a checked term in the active cell with its actual source bindings. -/
opaque Kernel.run (kernel : Kernel) (transaction : CellTransaction) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (sourceSnapshot : Option Json := none) : MetaM ValueBinding := do
  let program ← kernel.ledger.owners.identities.fresh .program
  kernel.evaluateSource sourceSnapshot transaction program context bound expression

end CasRuntime
