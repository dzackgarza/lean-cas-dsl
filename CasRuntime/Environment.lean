module

public import CasRuntime.Value

public section

namespace CasRuntime

open Lean Meta CasCompiler

initialize registerTraceClass `cas.environment

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

/-- An actual operand at an explicit position in the complete source argument list. -/
structure RuntimeArgument where
  private mk ::
  index : Nat
  value : ValueBinding
  private origin : ValueOrigin
  private graph : ValueGraph
  private marks : Array ValueBinding

/-- Retain operand provenance from the visible graph before native application preparation.
Reuse: the same graph visibility and immutable producing-origin checks as RuntimeParameter. -/
opaque RuntimeArgument.ofValue (graph : ValueGraph) (index : Nat) (value : ValueBinding)
    (marks : Array ValueBinding := #[]) :
    Except String RuntimeArgument := do
  discard <| graph.requiredOwners #[value]
  let some node := graph.find value.value
    | throw "the runtime argument is outside the visible graph"
  return ⟨index, value, node.origin, graph, marks⟩

/-- Read every native metadata occurrence, including equal terms carrying different marks. -/
private partial def sourceMarkKeys (expression : Expr) (keys : Array Nat) : Array Nat :=
  match expression with
  | .mdata data body =>
    let keys := match markedKey? data with
      | some key => if keys.contains key then keys else keys.push key
      | none => keys
    sourceMarkKeys body keys
  | .app function argument => sourceMarkKeys argument (sourceMarkKeys function keys)
  | .lam _ type body _ | .forallE _ type body _ =>
    sourceMarkKeys body (sourceMarkKeys type keys)
  | .letE _ type value body _ =>
    sourceMarkKeys body (sourceMarkKeys value (sourceMarkKeys type keys))
  | .proj _ _ body => sourceMarkKeys body keys
  | _ => keys

/-- Resolve only marks present in this argument's retained native source and complete context.
The captured argument table is authoritative; observation never consults mutable global marks.
Reuse: ClosedTerm's existing expression/type/context data and exact ValueBinding references. -/
opaque RuntimeArgument.sourceMarks (argument : RuntimeArgument) (source : ClosedTerm) :
    Except String (Array (Nat × ValueBinding)) := do
  let mut keys := sourceMarkKeys source.type (sourceMarkKeys source.expression #[])
  for entry in source.context.entries do
    keys := sourceMarkKeys entry.type keys
    if let some value := entry.value then keys := sourceMarkKeys value keys
  keys.mapM fun key => do
    let some value := argument.marks[key]?
      | throw "the source observation lost a retained occurrence mark"
    return (key, value)

/-- The complete semantic telescope and its separate ordered runtime-binding table.
Formal-only entries retain their source definitions, hypotheses and selected instances.
Source: data model section 2, ContextTelescope and its runtime-binding table. -/
structure RuntimeEnvironment where
  private mk ::
  worker : String
  context : ContextTelescope
  values : Array (Option ValueBinding)
  private inputProjections : Std.HashMap BindingId InputProjection

def RuntimeEnvironment.references (environment : RuntimeEnvironment) : Array ValueBinding :=
  environment.values.filterMap id

def RuntimeEnvironment.lookup (environment : RuntimeEnvironment) (source : BindingId) :
    Except String (Option ValueBinding) := do
  for (entry, value) in environment.context.entries.zip environment.values do
    if entry.id == source then return value
  throw "the runtime binding identity is outside its source telescope"

private def RuntimeEnvironment.bindingMap (environment : RuntimeEnvironment) :
    Std.HashMap BindingId ValueBinding := Id.run do
  let mut supplied := {}
  for (entry, value) in environment.context.entries.zip environment.values do
    if let some value := value then supplied := supplied.insert entry.id value
  return supplied

/-- The same actual occurrence, seen at either end of one association chain: a later projection
extends the original's chain, and a record field holding a binding extends the binding's own
chain (a lift record's source object). A different value is never the same reference. -/
private def sameReference (original current : ValueBinding) : Bool :=
  original.value == current.value &&
    (original.associationIds.toList.isPrefixOf current.associationIds.toList ||
      current.associationIds.toList.isPrefixOf original.associationIds.toList)

/-- A supplied operand retains a source binding's value when it is that node and carries every
association of the binding. A view of the node without one of them (the value before a consuming
application) is not the bound value. -/
private def retainsReference (bound operand : ValueBinding) : Bool :=
  bound.value == operand.value &&
    bound.associationIds.toList.isPrefixOf operand.associationIds.toList

private def checkNativeType (context : OpenContext) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin) : MetaM Unit := do
  let original ← value.role.source.inContext context
  unless ← isDefEq (← inferType original) expected do
    trace[cas.environment] "{original} : {← inferType original}, expected {expected}"
    throwError "the runtime value has an incompatible complete source type"
  let producing ← origin.role.source.inContext context
  unless ← isDefEq (← inferType producing) expected do
    trace[cas.environment] "{producing} : {← inferType producing}, expected {expected}"
    throwError "the producing runtime value has an incompatible complete source type"

/-- The tag of the failure "the source binding `id` has no runtime value". A session uses it to
report the statement as the gap of that definition. -/
def missingValueTag (id : BindingId) : Name :=
  .num (.str `CasRuntime.missingValue id.session) id.serial

/-- Whether the failure is a missing runtime value of the source binding `id`. -/
def missingValueOf (error : Exception) (id : BindingId) : Bool :=
  error.toMessageData.hasTag (· == missingValueTag id)

private def checkDependencies (context : OpenContext)
    (inputProjections : Std.HashMap BindingId InputProjection)
    (supplied : Std.HashMap BindingId ValueBinding) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin) : MetaM Unit := do
  for index in origin.role.contextDependencies do
    let some dependency := origin.role.source.context.entries[index]?
      | throwError "a producing runtime dependency is outside its source telescope"
    let some original := origin.parameters[index]?
      | throwError "a producing runtime dependency is outside its complete reference table"
    if let some original := original then
      let some current := supplied[dependency.id]?
        | throwError (MessageData.tagged (missingValueTag dependency.id)
            m!"the runtime value is missing a retained dependent reference")
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
        let some formal := prepared.layout.inputProjection | continue
        for index in dependencies do
          let some dependency := context.bindings[index]?
            | throwError "a consuming runtime dependency is outside its current source telescope"
          let some projection := inputProjections[dependency.id]?
            | throwError "a consuming runtime dependency is outside its retained source-position table"
          if projection == formal then
            let some current := supplied[dependency.id]?
              | throwError (MessageData.tagged (missingValueTag dependency.id)
                  m!"the runtime value is missing a consuming dependent reference \
                    ({dependency.expression})")
            unless sameReference original current do
              throwError "the runtime value has a different consuming dependent reference \
                ({dependency.expression})"

/-- Associate existing nodes by stable source identity, native type and retained type dependencies.
Check the complete table before comparing each actual producing dependency with its current
binding. Reuse: ClosedTerm.inContext, Lean.Meta.isDefEq and SourceLayout.contextDependencies.
Consuming field dependencies join their retained source positions to the original context
projection table, then compare the actual retained prefix references.
Later consuming roles may extend the original reference's complete instantiation chain.
Whole-reply admission remains a separate check. -/
opaque RuntimeEnvironment.capture (worker : String) (context : OpenContext)
    (parameters : Array RuntimeParameter) : MetaM RuntimeEnvironment := do
  if worker.isEmpty then throwError "runtime association requires an actual worker identity"
  let inputProjections ← context.inputProjections
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
    let role ← SourceLayout.ofTerm (← context.close source.expression)
    let .ok value := parameter.value.withRole role
      | throwError "the source binder has no computational runtime role"
    supplied := supplied.insert parameter.source value
  for parameter in parameters do
    let some source := context.bindings.find? (·.id == parameter.source)
      | throwError "a consuming runtime binding is outside its source telescope"
    checkDependencies context inputProjections supplied
      (← inferType source.expression) parameter.value parameter.origin
  let values := context.bindings.map fun binding => supplied[binding.id]?
  return ⟨worker, context.telescope, values, inputProjections⟩

/-- Whether a source parent already has an explicit runtime occurrence.
Formal selected instances have none; runtime-bound class values keep the same exact identity
as other values. Reuse: stable binding lookup, retained-value marks and native projections. -/
partial def RuntimeEnvironment.hasRetainedSource (environment : RuntimeEnvironment)
    (context : OpenContext) (specified : Expr) : MetaM Bool := do
  if let .mdata data body := specified then
    if (markedKey? data).isSome then return true
    if (data.find `CasCompiler.source.kind).isSome ||
        (data.find `CasCompiler.selection).isSome then return false
    return ← environment.hasRetainedSource context body
  if specified.isFVar then
    let some binding := context.bindings.find? (·.expression == specified)
      | throwError "the source argument is outside the complete runtime telescope"
    match environment.lookup binding.id with
    | .ok (some _) => return true
    | .ok none =>
      if let some definition := (← specified.fvarId!.getDecl).value? then
        return ← environment.hasRetainedSource context definition
      return false
    | .error reason => throwError "the source argument is outside its telescope: {reason}"
  if let some projection ← SourceProjection.ofExpr? specified then
    return ← environment.hasRetainedSource context projection.parent
  return false

/-- Check an operand's retained source selection. Projection names describe the already
selected path; the parent comes only from that value's association or producing origin.
Native conversion may check other expressions, but never chooses a projected parent. -/
private partial def RuntimeEnvironment.retainsSourceReference (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph) (marks : Array ValueBinding)
    (specified : Expr) (value : ValueBinding) (requireAnchor : Bool := false)
    (anchored : Bool := false) : MetaM Bool := do
  if let .mdata data body := specified then
    if let some key := markedKey? data then
      let some selected := marks[key]?
        | throwError "the source argument lost its retained occurrence mark"
      let .ok _ := graph.requiredOwners #[selected]
        | throwError "the source argument's marked occurrence is outside the visible graph"
      unless retainsReference selected value do return false
      -- A mark adds an identity constraint; it cannot replace a variable or field constraint.
      return ← environment.retainsSourceReference context graph marks body value requireAnchor true
    if (data.find `CasCompiler.source.kind).isNone &&
        (data.find `CasCompiler.selection).isNone then
      return ← environment.retainsSourceReference context graph marks body value requireAnchor anchored
  if specified.isFVar then
    let some binding := context.bindings.find? (·.expression == specified)
      | throwError "the source argument is outside the complete runtime telescope"
    match environment.lookup binding.id with
    | .ok (some retained) => return retainsReference retained value
    | .ok none =>
      let some definition := (← specified.fvarId!.getDecl).value?
        | throwError "the source argument has no retained runtime binding"
      return ← environment.retainsSourceReference context graph marks definition value requireAnchor anchored
    | .error reason => throwError "the source argument is outside its telescope: {reason}"
  let projection ← SourceProjection.ofExpr? specified
  let runtimeProjection ← match projection with
    | none => pure false
    | some projection =>
      if !projection.info.fromClass then pure true
      else environment.hasRetainedSource context projection.parent
  if runtimeProjection then
    let some node := graph.find value.value
      | throwError "the runtime argument is outside the visible graph"
    let mut selected := value.projectionAccesses
    if let some parent := node.origin.access then
      selected := selected.push (parent, node.origin.accessPath)
    for (parent, path) in selected do
      if path.isEmpty then continue
      let mut original := specified
      let mut matchedPath := true
      for projection in path.reverse do
        let some step ← SourceProjection.ofExpr? original
          | matchedPath := false; break
        unless step.declaration == projection do
          matchedPath := false
          break
        original := step.parent
      if matchedPath then
        if ← environment.retainsSourceReference context graph marks original parent true then return true
    return false
  if requireAnchor && !anchored then return false
  let original ← value.role.source.inContext context
  return ← isDefEq original specified

/-- Bind the supplied operand to its actual source argument, rather than a same-typed value.
Source variables use their stable-ID runtime association. A projection retains the exact path
and selected parent. Reuse: complete type/dependency checks and native projection metadata. -/
opaque RuntimeEnvironment.checkArgument (environment : RuntimeEnvironment) (source : ClosedTerm)
    (argument : RuntimeArgument) : MetaM ValueBinding := do
  unless argument.value.value.worker == environment.worker do
    throwError "the runtime argument belongs to a different worker"
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let specified ← source.inContext context
    let expected ← inferType specified
    if ← isProp expected then throwError "a formal proof argument has no runtime value binding"
    checkNativeType context expected argument.value argument.origin
    checkDependencies context environment.inputProjections environment.bindingMap
      expected argument.value argument.origin
    unless ← environment.retainsSourceReference context argument.graph argument.marks
        specified argument.value do
      trace[cas.environment] "argument {argument.index}: {specified}; retained source {← argument.value.role.source.inContext context}"
      throwError "the runtime argument does not retain its specified source value"
    let role ← SourceLayout.ofTerm (← context.close specified)
    let .ok value := argument.value.withRole role
      | throwError "the source argument has no computational runtime role"
    return value

/-- Check a retained candidate at the prepared result's complete native type and actual indexes.
Reuse: the source-binding type/dependency checks and CandidateResponse's operational shape check.
The graph supplies the immutable producing provenance; liveness and publication are later gates. -/
private partial def checkResultValue (environment : RuntimeEnvironment) (graph : ValueGraph)
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
    checkDependencies context environment.inputProjections environment.bindingMap
      expected value node.origin
    let candidate ← match CandidateResponse.ofValue source graph value with
      | .ok candidate => pure candidate
      | .error reason =>
        throwError "the prepared result has an incompatible computational interface: {reason} \
          at {← source.source.inContext context}"
    let stored := match node.payload.data with
      | .product _ | .container _ => true
      | _ => false
    if source.kind == .record && stored then
      let layout ← RecordLayout.ofSource source
      for prepared in layout.fields do
        if let some index := prepared.field.wireIndex then
          let field ← IO.ofExcept <| (graph.project candidate.root index).mapError IO.userError
          discard <| checkResultValue environment graph prepared.layout field
    return candidate

/-- Validate the complete stored result through its source-derived native field layouts.
Reuse: RecordLayout, graph projection and the same native type/dependency check at every node.
Exported records retain their lazy interface; stored records validate all retained children. -/
opaque RuntimeEnvironment.checkResult (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding) : MetaM (CandidateResponse source) :=
  checkResultValue environment graph source value

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
