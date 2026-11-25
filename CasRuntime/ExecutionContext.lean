module

public import CasRuntime.KernelState
public import CasRuntime.Transaction
public import CasRuntime.Association

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Execute a checked term in an existing cell, preserving its program and binding identities. -/
abbrev SourceEvaluation := CellTransaction → RuntimeId .program → OpenContext →
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

/-- Open original application inputs by their exact retained parameter positions.
The caller admits the unchanged input table before use; no source/type search chooses values. -/
opaque PreparedRequest.markedArguments (request : PreparedRequest)
    (marks : IO.Ref (Array ValueBinding)) (context : OpenContext) (count : Nat) : MetaM (Array Expr × Array (Option ValueBinding)) := do
  let formal := request.application.map (·.arguments.map (·.source.source)) |>.getD #[]
  let values := request.origin.application.map (·.arguments) |>.getD #[]
  unless formal.size == values.size && count ≤ formal.size do
    throwError "the categorical family lost its complete original input table"
  let mut actual := #[]
  for index in [:count] do
    let some original := formal[index]?
      | throwError "the categorical family lost an original input position"
    let source ← original.inContext context
    actual := actual.push (← match values[index]?.bind id with
      | some value => markValue marks value source
      | none => pure source)
  return (actual, values.extract 0 count)

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

/-- Resolve an already selected input in a compatible source context through ordinary marked
projections. Every step retains its original baseline before output associations are added. -/
def FixedInput.resolveInContext (input : FixedInput) (context : OpenContext)
    (graphView : MetaM ValueGraph) (marks : IO.Ref (Array ValueBinding))
    (evaluate : Expr → MetaM ValueBinding) : MetaM ValueBinding := do
  let mut parent := input.parent
  let mut term ← input.source.inContext context
  for projection in input.path do
    let some field := parent.role.fields.find? (·.projection == projection)
      | throwError "a fixed input lost its prepared native projection"
    let marked ← markValue marks parent term
    let value ← evaluate (← projectTerm marked field)
    let graph ← graphView
    let some _ ← IO.ofExcept <|
        (graph.projectionBasis value parent #[projection]).mapError IO.userError
      | throwError "a fixed input demand lost its actual projection association"
    parent := value
    term ← projectTerm term field
  return parent

/-- Resolve the selected input in its own retained source scope through ordinary marked
projections. Return the enriched access, so input-side validation can recover its original
baseline before output association adds any new access or application wrappers. -/
def Kernel.resolveFixedInput (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (transaction : CellTransaction) (program : RuntimeId .program) (input : FixedInput) :
    MetaM ValueBinding := do
  input.source.withOpen fun bindings _ => do
    unless input.parameters.size == input.source.context.entries.size do
      throwError "a fixed input lost its original source context table"
    let context ← ContextTelescope.capture bindings
    let mut bound : Std.HashMap BindingId ValueBinding := {}
    for (entry, value) in input.source.context.entries.zip input.parameters do
      if let some value := value then bound := bound.insert entry.id value
    input.resolveInContext context (liftM (m := IO) transaction.view) kernel.marks
      (evaluateSource transaction program context bound)

end CasRuntime
