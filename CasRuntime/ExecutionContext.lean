module

public import CasRuntime.KernelState
public import CasRuntime.Transaction
public import CasRuntime.Association

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Execute a checked term in an existing cell, preserving its original source snapshot,
program and binding identities. Native callers explicitly supply no frontend snapshot. -/
abbrev SourceEvaluation := Option Json → CellTransaction → RuntimeId .program → OpenContext →
  Std.HashMap BindingId ValueBinding → Expr → MetaM ValueBinding


def portFailure (error : PortError) : MetaM α :=
  throwStratum error.stratum error.render

def transactionFailure (failure : TransactionFailure) : MetaM α :=
  match failure with
  | .settled => throwStratum .unavailable "cancelled"
  | .staleOwner | .reservation .staleOwner => throwStratum .unavailable "stale_owner"
  | .reservation .consumed => throwStratum .unavailable "reserved_without_receipt"
  | .reservation .wrongConnection => throwStratum .unavailable "stale_owner"
  | failure => throwError "internal: the active transaction rejected a completion: {repr failure}"

def kernelCompletion (request : PreparedRequest) (transaction : CellTransaction)
    (value : ValueBinding) (resolve : Option (FixedInput → MetaM ValueBinding) := none) :
    MetaM (PreparedResponse request) := do
  let fixed ← request.resolveFixedResults transaction request.source value resolve
  let draft ← transaction.draft
  let (draft, value) ← request.associateResult transaction.owners.identities
    request.source draft value fixed (complete := true)
  let response ← request.admitResult draft.view value
  match ← transaction.installDraft draft with
  | .error failure => transactionFailure failure
  | .ok () => pure ()
  match ← transaction.completeKernel request response with
  | .error failure => transactionFailure failure
  | .ok association => request.admitResult (← transaction.view) association.response.root

def withSourceScope (request : PreparedRequest)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → MetaM α) : MetaM α :=
  request.environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let mut bound : Std.HashMap BindingId ValueBinding := {}
    for (entry, value) in request.environment.context.entries.zip request.environment.values do
      if let some value := value then bound := bound.insert entry.id value
    action context bound

def projectTerm (value : Expr) (field : FieldLayout) : MetaM Expr := do
  let some info := (← getEnv).getProjectionFnInfo? field.projection
    | throwError "internal: a prepared field has no native projection"
  return .proj (← getConstInfoCtor info.ctorName).induct info.i value

/-- Resolve the selected input in its own retained source scope through ordinary marked
projections. Return the enriched access, so input-side validation can recover its original
baseline before output association adds any new access or application wrappers. -/
def Kernel.resolveFixedInput (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (sourceSnapshot : Option Json)
    (transaction : CellTransaction) (program : RuntimeId .program) (input : FixedInput) :
    MetaM ValueBinding := do
  input.source.withOpen fun bindings expression => do
    unless input.parameters.size == input.source.context.entries.size do
      throwError "a fixed input lost its original source context table"
    let context ← ContextTelescope.capture bindings
    let mut bound : Std.HashMap BindingId ValueBinding := {}
    for (entry, value) in input.source.context.entries.zip input.parameters do
      if let some value := value then bound := bound.insert entry.id value
    let mut parent := input.parent
    let mut term := expression
    for projection in input.path do
      let some field := parent.role.fields.find? (·.projection == projection)
        | throwError "a fixed input lost its prepared native projection"
      let marked ← markValue kernel.marks parent term
      let value ← evaluateSource sourceSnapshot transaction program context bound (← projectTerm marked field)
      let graph ← transaction.view
      let some _ ← IO.ofExcept <|
          (graph.projectionBasis value parent #[projection]).mapError IO.userError
        | throwError "a fixed input demand lost its actual projection association"
      parent := value
      term ← projectTerm term field
    return parent

end CasRuntime
