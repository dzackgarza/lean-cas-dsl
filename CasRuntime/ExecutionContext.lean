module

public import CasRuntime.KernelState
public import CasRuntime.Transaction

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
    (value : ValueBinding) : MetaM (PreparedResponse request) := do
  let response ← request.admitResult (← transaction.view) value
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

end CasRuntime
