module

public import CasRuntime.Demand
public import CasRuntime.Execute
public import CasCompiler.Lower

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

mutual

private partial def Kernel.evaluateSource (kernel : Kernel) (sourceSnapshot : Option Json)
    (validatedEnvironment : Option RuntimeEnvironment := none) :
    SourceEvaluation :=
  fun transaction program context bound selections expression =>
    lowerTerm {
      ledger := kernel.ledger, transaction, codes := kernel.codes
      sourceSnapshot
      limitLeg := fun demand => do
        let graph ← transaction.view
        unless ← graph.isAvailable kernel.ledger.owners demand.cone do
          transactionFailure .staleOwner
        let selected := demand.selection.construction
        let apex := if selected.source.colimit then
          ``CategoryTheory.Limits.Cocone.pt else ``CategoryTheory.Limits.Cone.pt
        if demand.apexSource.isSome then
          let some _ ← IO.ofExcept <|
              (graph.projectionBasis demand.receiver demand.cone #[apex]).mapError IO.userError
            | throwError "the selected leg changed its actual receiver/cone projection"
        else
          let field := if selected.source.colimit then
            ``CategoryTheory.Limits.ColimitCocone.cocone else
            ``CategoryTheory.Limits.LimitCone.cone
          let retained ← match ← transaction.selectedAt selected.source.construction field
              demand.receiver with
            | .ok value => pure value
            | .error failure => transactionFailure failure
          let some retained := retained
            | throwError "the selected leg lost its exact receiver-scoped completed cone"
          unless retained.value == demand.cone.value &&
              retained.associationIds == demand.cone.associationIds do
            throwError "the selected leg changed its original completed cone occurrence"
        let component ← demand.component.inContext demand.context
        kernel.evaluateSource sourceSnapshot (some demand.contextEnvironment)
          transaction program demand.context demand.bound demand.selections component
      run := fun computation => Execute.run kernel.executor computation transaction
        (some (kernel.resolveFixedInput
          (kernel.evaluateSource sourceSnapshot validatedEnvironment) transaction program)) }
      program context bound expression validatedEnvironment selections


partial def Kernel.executor (kernel : Kernel) :
    PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
  fun request transaction => do
    return (← kernel.execute
      (kernel.evaluateSource request.observation.sourceSnapshot (some request.environment))
      request transaction, transaction)

end


opaque Kernel.run (kernel : Kernel) (transaction : CellTransaction) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (sourceSnapshot : Option Json := none) (selections : SourceSelectionScope Expr := {}) :
    MetaM ValueBinding := do
  let program ← kernel.ledger.owners.identities.fresh .program
  kernel.evaluateSource sourceSnapshot none transaction program context bound selections expression

end CasRuntime
