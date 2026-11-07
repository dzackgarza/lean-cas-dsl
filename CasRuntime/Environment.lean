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

private def sameReference (original current : ValueBinding) : Bool :=
  original.value == current.value &&
    original.instantiations.map (·.id) == current.instantiations.map (·.id)

private def checkNativeType (context : OpenContext) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin) : MetaM Unit := do
  let original ← value.role.source.inContext context
  unless ← isDefEq (← inferType original) expected do
    throwError "the runtime value has an incompatible complete source type"
  let producing ← origin.role.source.inContext context
  unless ← isDefEq (← inferType producing) expected do
    throwError "the producing runtime value has an incompatible complete source type"

private def checkDependencies (context : OpenContext)
    (supplied : Std.HashMap BindingId ValueBinding) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin) : MetaM Unit := do
  for index in origin.role.contextDependencies do
    let some dependency := origin.role.source.context.entries[index]?
      | throwError "a producing runtime dependency is outside its source telescope"
    let some original := origin.parameters[index]?
      | throwError "a producing runtime dependency is outside its complete reference table"
    if let some original := original then
      let some current := supplied[dependency.id]?
        | throwError "the runtime value is missing a retained dependent reference"
      unless sameReference original current do
        throwError "the runtime value has a different retained dependent reference"
  let dependencies ← CasCompiler.contextDependencies context.bindings expected
  for instantiation in value.instantiations do
    for index in instantiation.field.precedingDependencies do
      let some previous := instantiation.preceding[index]?
        | throwError "a consuming runtime dependency is outside its complete field prefix"
      if let some original := previous then
        let some prepared := instantiation.association.layout.fields[index]?
          | throwError "a consuming runtime dependency is outside its source record"
        let formal ← prepared.field.source.inContext context
        for index in dependencies do
          let some dependency := context.bindings[index]?
            | throwError "a consuming runtime dependency is outside its current source telescope"
          if ← isDefEq (← inferType dependency.expression) (← inferType formal) <&&>
              isDefEq dependency.expression formal then
            let some current := supplied[dependency.id]?
              | throwError "the runtime value is missing a consuming dependent reference"
            unless sameReference original current do
              throwError "the runtime value has a different consuming dependent reference"

/-- Associate existing nodes by stable source identity, native type and retained type dependencies.
Check the complete table before comparing each actual producing dependency with its current
binding. Reuse: ClosedTerm.inContext, Lean.Meta.isDefEq and SourceLayout.contextDependencies.
Consuming field dependencies use their actual source projections and retained prefix references.
Whole-reply admission remains a separate check. -/
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
    checkNativeType context expected parameter.value parameter.origin
    supplied := supplied.insert parameter.source parameter.value
  for parameter in parameters do
    let some source := context.bindings.find? (·.id == parameter.source)
      | throwError "a consuming runtime binding is outside its source telescope"
    checkDependencies context supplied (← inferType source.expression) parameter.value parameter.origin
  let values := context.bindings.map fun binding => supplied[binding.id]?
  return ⟨worker, context.telescope, values⟩

/-- Check a retained candidate at the prepared result's complete native type and actual indexes.
Reuse: the source-binding type/dependency checks and CandidateResponse's operational shape check.
The graph supplies the immutable producing provenance; liveness and publication are later gates. -/
opaque RuntimeEnvironment.checkResult (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding) : MetaM (CandidateResponse source) := do
  unless graph.worker == environment.worker do
    throwError "the prepared result belongs to a different worker"
  let .ok _ := graph.requiredOwners (environment.references.push value)
    | throwError "the prepared result or its runtime context is outside the visible graph"
  let some node := graph.find value.value
    | throwError "the prepared result is outside the visible graph"
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let expected ← inferType (← source.source.inContext context)
    checkNativeType context expected value node.origin
    let mut supplied : Std.HashMap BindingId ValueBinding := {}
    for (entry, value) in environment.context.entries.zip environment.values do
      if let some value := value then supplied := supplied.insert entry.id value
    checkDependencies context supplied expected value node.origin
    let .ok candidate := CandidateResponse.ofValue source graph value
      | throwError "the prepared result has an incompatible computational interface"
    return candidate

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
