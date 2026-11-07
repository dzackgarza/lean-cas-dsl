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

/-- Associate existing nodes by stable source identity, native type and retained type dependencies.
Check the complete table before comparing each actual producing dependency with its current
binding. Reuse: ClosedTerm.inContext, Lean.Meta.isDefEq and SourceLayout.contextDependencies.
Whole-reply admission and consuming record qualifiers remain separate checks. -/
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
  for parameter in parameters do
    let origin := parameter.origin
    for index in origin.role.contextDependencies do
      let some dependency := origin.role.source.context.entries[index]?
        | throwError "a producing runtime dependency is outside its source telescope"
      let some original := origin.parameters[index]?
        | throwError "a producing runtime dependency is outside its complete reference table"
      if let some original := original then
        let some current := supplied[dependency.id]?
          | throwError "the runtime value is missing a retained dependent reference"
        unless original.value == current.value &&
            original.instantiations.map (·.id) == current.instantiations.map (·.id) do
          throwError "the runtime value has a different retained dependent reference"
  let values := context.bindings.map fun binding => supplied[binding.id]?
  return ⟨worker, context.telescope, values⟩

/-- Stamp a produced node with its complete ordered actual context references.
Reuse: SourceLayout.inContext transports the checked role by stable source identities.
Result-type dependency selection is mechanical source metadata, not candidate decoding. -/
opaque RuntimeEnvironment.origin (environment : RuntimeEnvironment)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence)
    (role : SourceLayout) : MetaM ValueOrigin := do
  unless program.worker == environment.worker && occurrence.worker == environment.worker do
    throwError "the producing runtime context belongs to a different worker"
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let role ← role.inContext context
    return { program, occurrence, role, parameters := environment.values }

end CasRuntime
