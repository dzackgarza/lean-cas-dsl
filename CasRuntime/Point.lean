module

public import CasRuntime.ExecutionContext
public import CasRuntime.Encode
public import CasRuntime.DeclaredInput
public import CasCompiler.PointFamily
public import CasCatalogue.Admission

@[expose] public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Follow only the actual projection ancestry of this callable, backwards along the checked
native field path. The terminal node must carry the same original prepared family occurrence;
an equal type or endpoint never selects a different arrow. -/
private partial def namedPointRoot? (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (family : PreparedRequest)
    (value : ValueBinding) (path : Array Name) : MetaM (Option InputDescriptorView) := do
  if path.isEmpty then
    let some descriptorView ← InputDescriptorView.namedMorphism? graph codes value | return none
    let some original := descriptorView.family | return none
    if original.program != family.program || original.occurrence != family.occurrence then
      return none
    return some descriptorView
  let some node := graph.find value.value
    | throwError "the named point callable is outside its visible graph"
  let mut accesses := value.projectionAccesses.reverse
  if let some parent := node.origin.access then
    accesses := accesses.push (parent, node.origin.accessPath)
  for (parent, suffix) in accesses do
    if suffix.isEmpty || suffix.size > path.size then continue
    let parentPath := path.extract 0 (path.size - suffix.size)
    unless path.extract parentPath.size path.size == suffix do continue
    let some _ ← IO.ofExcept <| (graph.projectionBasis value parent suffix).mapError IO.userError
      | continue
    if let some original ← namedPointRoot? graph codes family parent parentPath then
      return some original
  return none

/-- Complete original inputs of a released named arrow applied to an explicitly retained
generalized point. The arrow descriptor is a checked view of its actual input node. -/
structure PreparedPointInvocation where
  private mk ::
  operation : String
  parameters : Array ValueBinding
  arrow : ValueBinding
  domain : ValueBinding
  source : ValueBinding
  target : ValueBinding
  argument : ValueBinding
  forms : Array String
  dependencies : Array ValueBinding
  views : Array InputDescriptorView

/-- Prepare the named-point dialect only at its checked native carrier action and an original
point map retained by the reader. Other native/opaque actions keep their existing path. All
original inputs are admitted before lowering the source-declared descriptor captures. -/
opaque PreparedPointInvocation.prepare? (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request family : PreparedRequest) (path : Array FieldLayout)
    (transaction : CellTransaction) : MetaM (Option PreparedPointInvocation) := do
  let .primitive (.registered declared) universes := family.action | return none
  let .morphism morphismId := declared.source.reference | return none
  let .apply callable arguments _ := request.action | return none
  let #[argumentSource] := arguments | return none
  let retainsPoint ← withSourceScope request fun context _ => do
    return (← sourcePointOrigin? (← argumentSource.inContext context)).isSome
  unless retainsPoint do return none
  let some entry := (← semanticState).morphisms.find? (·.id == morphismId)
    | throwError "the named point action lost its released morphism"
  let selected ← PointFamily.forEntry entry
  unless path.map (·.projection) == selected.path do return none
  let graph ← transaction.view
  discard <| family.admitInputs graph
  let inputs ← request.admitInputs graph
  let #[argument] ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    | throwError "the named point action lost its complete original operand"
  let codes ← kernel.codes.get
  let some arrowView ← namedPointRoot? graph codes family callable selected.path
    | throwError "the named point action lost its exact original arrow and field relation"
  withSourceScope request fun context bound => do
    let pointSource ← argumentSource.inContext context
    let some point ← sourcePointOrigin? pointSource | return none
    let supplied ← selected.request? pointSource
    let mut actual : Array Expr := #[]
    if let some application := family.application then
      let some original := family.origin.application
        | throwError "the named arrow lost its original native parameter table"
      for parameter in application.arguments do
        let source ← parameter.source.source.inContext context
        let source ← match original.arguments[parameter.sourceIndex]?.bind id with
          | some value => markValue kernel.marks value source
          | none => pure source
        actual := actual.push source
    let head := selected.family.instantiateLevelParams selected.universeParams universes
    let originalArrow := mkAppN head actual
    let (source, target) ← selected.endpoints originalArrow
    let domain ← sourceNamedObjectAlias CategoryId.sets point.domain
    if let some supplied := supplied then
      let expected := supplied.arrow.getAppArgs
      unless expected.size == actual.size do
        throwError "the named point request changed its complete declaration parameter arity"
      let values := family.origin.application.map (·.arguments) |>.getD #[]
      unless values.size == expected.size do
        throwError "the named point request lost its original parameter value table"
      for source in expected, index in [:expected.size] do
        if let some value := values[index]?.bind id then
          request.environment.checkDeclaredInput context graph (← kernel.marks.get) source value
        else
          unless ← isProof source do
            throwError "the named point request is missing an original computational parameter"
    let function ← selected.function originalArrow
    let .forallE _ expected _ _ ← whnfR (← inferType function)
      | throwError "the named arrow lost its native point-function interface"
    checkRegisteredDomains (← inferType pointSource) expected
    unless ← isDefEq (← inferType pointSource) expected do
      throwError "the original point has a different named-arrow source"
    let retain := fun (source expected : Expr) (index : Nat) => do
      let value ← evaluateSource transaction request.program context bound source
      let graph ← transaction.view
      let .ok actual := RuntimeArgument.ofValue graph index value (← kernel.marks.get)
        | throwError "a named point descriptor is outside its original graph"
      let checked ← request.environment.checkArgument (← context.close expected) actual
      request.environment.checkDeclaredInput context graph (← kernel.marks.get) expected value
      return checked
    let domain ← retain (supplied.map (·.domain) |>.getD domain) domain 0
    let source ← retain (supplied.map (·.source) |>.getD source) source 1
    let target ← retain (supplied.map (·.target) |>.getD target) target 2
    let graph ← transaction.view
    discard <| family.admitInputs graph
    discard <| request.admitInputs graph
    let mut forms := #[entry.id.raw]
    if let some (objectId, _) ← sourceObjectReference? (← source.role.source.inContext context) then
      let registry : RegistryState := { toSemanticState := ← semanticState }
      let some form := registry.form? objectId.raw
        | throwError "the named point source lost its registered object form"
      if let some reason := registry.rejects (.morphism entry) form then
        throwError "the named point source has an incompatible input form: {reason}"
      let some object := registry.objects.find? (·.id == objectId)
        | throwError "the named point source lost its original object category"
      forms := forms ++ #[objectId.raw, object.category.raw]
    let roots := arrowView.parameters ++ #[arrowView.binding, domain, source, target, argument]
    let views ← InputDescriptorView.collect graph codes roots #[arrowView]
    return some ⟨entry.id.raw, arrowView.parameters, arrowView.binding, domain, source,
      target, argument, forms, family.scope ++ request.scope ++ roots ++
        views.flatMap (·.dependencies), views⟩

/-- Original roots in the released seven-field PointInvocation packet. Nested named-arrow
parameters are encoded beneath its own args field and retain their exact input authorities. -/
def PreparedPointInvocation.roots (invocation : PreparedPointInvocation) : Array InputPosition :=
  invocation.parameters.mapIdx (fun index binding =>
    { path := #[.field "args", .index 1, .index index], binding }) ++ #[
    { path := #[.field "args", .index 2], binding := invocation.arrow },
    { path := #[.field "args", .index 3], binding := invocation.domain },
    { path := #[.field "args", .index 4], binding := invocation.source },
    { path := #[.field "args", .index 5], binding := invocation.target },
    { path := #[.field "args", .index 6], binding := invocation.argument }]

def PreparedPointInvocation.encode (invocation : PreparedPointInvocation)
    (graph : ValueGraph) (receiver : ConnectionGeneration) :
    Except String (EncodedInputs × Json) := do
  let encoded ← graph.encodeInputs receiver invocation.roots invocation.views
  let count := invocation.parameters.size
  let #[arrow, domain, source, target, argument] := encoded.values.extract count encoded.values.size
    | throw "the named point packet lost a complete original input"
  let packet : PointInvocation := {
    operation := invocation.operation
    parameters := encoded.values.extract 0 count
    arrow := arrow
    domain := domain
    source := source
    target := target
    argument := argument
  }
  return (encoded, packet.encode)

end CasRuntime
