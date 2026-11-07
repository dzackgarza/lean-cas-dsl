module

public import CasRuntime.Value

public section

namespace CasRuntime

open Lean Meta CasCompiler

/-- An actual value associated with an explicitly identified source binder. -/
structure RuntimeParameter where
  private mk ::
  source : BindingId
  value : ValueBinding
  private origin : ValueOrigin

/-- Read the actual producing provenance from the caller's visible immutable graph.
Reuse: ValueGraph.requiredOwners and ValueGraph.find; no payload copy enters this table. -/
opaque RuntimeParameter.ofValue (graph : ValueGraph) (source : BindingId) (value : ValueBinding) :
    Except String RuntimeParameter := do
  discard <| graph.requiredOwners #[value]
  let some node := graph.find value.value
    | throw "the runtime parameter is outside the visible graph"
  return ⟨source, value, node.origin⟩

/-- The complete semantic telescope and its separate ordered runtime-binding table.
Formal-only entries retain their source definitions, hypotheses and selected instances.
Source: data model section 2, ContextTelescope and its runtime-binding table. -/
structure RuntimeEnvironment where
  private mk ::
  worker : String
  context : ContextTelescope
  values : Array (Option ValueBinding)

def RuntimeEnvironment.references (environment : RuntimeEnvironment) : Array ValueBinding :=
  environment.values.filterMap id

def RuntimeEnvironment.lookup (environment : RuntimeEnvironment) (source : BindingId) :
    Except String (Option ValueBinding) := do
  for (entry, value) in environment.context.entries.zip environment.values do
    if entry.id == source then return value
  throw "the runtime binding identity is outside its source telescope"

/-- Associate existing nodes by stable source identity and native source type.
This checks both current and producing source types, not a coarse kind or display name.
Reuse: ClosedTerm.inContext and Lean.Meta.isDefEq. No payload is decoded into a source term.
Dependent runtime qualifiers and whole-reply admission remain separate checks. -/
opaque RuntimeEnvironment.capture (worker : String) (context : OpenContext)
    (parameters : Array RuntimeParameter) : MetaM RuntimeEnvironment := do
  if worker.isEmpty then throwError "runtime association requires an actual worker identity"
  let mut supplied : Std.HashMap BindingId ValueBinding := {}
  for parameter in parameters do
    if supplied.contains parameter.source then
      throwError "a source binder has duplicate runtime associations"
    unless parameter.value.value.worker == worker do
      throwError "a runtime source binding belongs to a different worker"
    let some source := context.bindings.find? (·.id == parameter.source)
      | throwError "a runtime association names a source binder outside the complete telescope"
    let expected ← inferType source.expression
    if ← isProp expected then
      throwError "a source proof has no runtime value association"
    let original ← parameter.value.role.source.inContext context
    unless ← isDefEq (← inferType original) expected do
      throwError "the runtime value has an incompatible complete source type"
    let producing ← parameter.origin.role.source.inContext context
    unless ← isDefEq (← inferType producing) expected do
      throwError "the producing runtime value has an incompatible complete source type"
    supplied := supplied.insert parameter.source parameter.value
  let values := context.bindings.map fun binding => supplied[binding.id]?
  return ⟨worker, context.telescope, values⟩

end CasRuntime
