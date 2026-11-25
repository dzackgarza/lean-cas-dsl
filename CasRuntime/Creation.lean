module

public import CasRuntime.ExecutionContext
public import CasRuntime.Encode
public import CasRuntime.NativeMapEndpoints
public import CasRuntime.ConstructionSource
public import CasCompiler.PreparedCreationFamily

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- One complete fixed creation request retains the actual target cone, its universal
data and the original source owner, followed by every declared computational capture. -/
structure PreparedCreationInvocation where
  private mk ::
  preparation : RoleScope
  family : PreparedCreationFamily
  parameters : ValueContainer
  forms : Array String
  dependencies : Array ValueBinding
  views : Array InputDescriptorView
  private inputs : InputRoleMap

/-- Preserve a fixed native source capture without evaluating its definition. Direct
retained inputs keep their original binding. Compound source data keep the complete
original native application table, so later source admission sees those same positions.
The existing term closure supplies only its ordinary delayed native interface. -/
private partial def retainCreationCapture (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (context : OpenContext) (source : ClosedTerm) :
    MetaM ValueBinding := do
  let expression ← source.inContext context
  if ← isProof expression then
    throwError "a creation capture cannot replace an original formal proof with runtime data"
  let graph ← transaction.view
  let marks ← IO.ofExcept <|
    (captureSourceMarks (← kernel.marks.get) source).mapError IO.userError
  let environment ← request.environment.withSourceMarks marks (some graph)
  if let some retained ← environment.endpointValue? context graph expression then
    environment.checkDeclaredInput context graph (← kernel.marks.get) expression retained
    return retained
  let native := expression.consumeMData
  let mut arguments : Array (Option ValueBinding) := #[]
  let application ← if native.getAppNumArgs == 0 then pure none else do
    let originals ← native.getAppArgs.mapM fun argument => context.close argument
    let head ← SourceLayout.ofTerm (← context.close native.getAppFn)
    let (_, layout) ← ApplicationLayout.ofSource head context originals
    unless layout.arguments.size == originals.size do
      throwError "a passive creation capture lost its complete native application telescope"
    for argument in layout.arguments do
      if argument.wireIndex.isSome then
        arguments := arguments.push (some (← retainCreationCapture kernel request transaction
          context argument.source.source))
      else
        arguments := arguments.push none
    let origin ← IO.ofExcept <|
      (ApplicationOrigin.ofArguments layout environment.values arguments none).mapError IO.userError
    pure (some origin)
  let graph ← transaction.view
  let environment ← environment.withSourceMarks #[] (some graph)
  let mut captures ← markedContextReferences (some graph) context environment.sourceMarks expression
  let positions ← computationalDependencies (context.bindings.map (·.expression)) expression
  for position in positions do
    let some binding := context.bindings[position]?
      | throwError "a passive creation capture lost an original source-context position"
    let value ← IO.ofExcept <| (environment.lookup binding.id).mapError IO.userError
    if let some value := value then captures := captures.push value
  captures := captures ++ arguments.filterMap id
  discard <| IO.ofExcept <| (graph.requiredOwners captures).mapError IO.userError
  let role ← SourceLayout.ofTerm source
  let program ← kernel.ledger.owners.identities.fresh .program
  let occurrence ← kernel.ledger.owners.identities.fresh .occurrence
  let origin ← environment.origin request.program occurrence role
  let origin := { origin with application }
  kernel.codes.modify (·.insert program (.term source))
  let value ← transaction.stage origin (.closure program captures)
  environment.checkDeclaredInput context (← transaction.view) (← kernel.marks.get) expression value
  return value

/-- The supplied universal record must retain this actual cone at its original native
predecessor slot. The check is independent of the record's portable/owned/callable payload. -/
private def requireCreationUniversal (family : PreparedCreationFamily) (graph : ValueGraph)
    (cone universal : ValueBinding) : MetaM Unit := do
  let some node := graph.find universal.value
    | throwError "the creation request lost its actual universal data"
  let some nativePrefix := node.origin.fieldPrefix
    | throwError "the creation universal data lost its original actual-cone predecessor"
  discard <| IO.ofExcept <|
    (nativePrefix.requireOrigin node.origin.program node.origin.occurrence node.origin.role).mapError
      IO.userError
  let #[frame] := nativePrefix.frames.filter
      (·.field.projection == ``CategoryTheory.Limits.LimitCone.isLimit)
    | throwError "the creation universal data changed its original limit-presentation field"
  let #[field] := frame.association.layout.fields.filter
      (·.field.projection == family.target.coneProjection)
    | throwError "the creation universal data lost its native preceding cone slot"
  let some preceding := frame.preceding[field.field.sourceIndex]?.bind id
    | throwError "the creation universal data has no actual original cone predecessor"
  unless preceding.value == cone.value &&
      cone.associationIds.toList.isPrefixOf preceding.associationIds.toList do
    throwError "the creation universal data belongs to another actual cone occurrence"
  discard <| IO.ofExcept <| (graph.requiredOwners #[cone, universal, preceding]).mapError IO.userError

/-- The explicit target cone must come from the selected original raw construction.
Every original target parameter position is checked against its own retained supplier. -/
private def requireCreationTarget (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (context : OpenContext) (family : PreparedCreationFamily)
    (cone universal : ValueBinding) : MetaM Unit := do
  let graph ← transaction.view
  let (original, _, selected, _) ←
    kernel.retainedRawConstructionCone transaction graph context cone
  let .primitive (.limit target _) universes := original.action
    | throwError "the creation target lost its original raw-cone request"
  unless target.entry.id == family.target.entry.id &&
      universes == family.targetUniverses &&
      selected.source.row == family.target.entry.id.raw &&
      selected.source.construction == family.construction do
    throwError "the creation request changed its original target construction"
  family.target.requireInterface selected.source
  let supplied := original.origin.application.map (·.arguments) |>.getD #[]
  let native := original.application.map (·.arguments) |>.getD #[]
  let expected := family.inputs.target.arguments
  unless supplied.size == expected.size && native.size == expected.size do
    throwError "the creation target changed its complete original parameter table"
  for argument in expected, position in [:expected.size] do
    let some actual := supplied[position]?
      | throwError "the creation target lost an original declaration position"
    let some source := native[position]?
      | throwError "the creation target lost its original native argument schema"
    unless argument.sourceIndex == position && source.sourceIndex == position &&
        argument.wireIndex.isSome == actual.isSome &&
        source.wireIndex.isSome == actual.isSome do
      throwError "the creation target changed an original proof or computational position"
    if let some actual := actual then
      request.environment.checkDeclaredInput context graph (← kernel.marks.get)
        (← argument.source.source.inContext context) actual
    else
      unless ← isDefEq (← inferType (← argument.source.source.inContext context))
          (← inferType (← source.source.source.inContext context)) do
        throwError "the creation target changed an original formal hypothesis"
  requireCreationUniversal family graph cone universal

/-- Prepare the root creation operation with unchanged c/t and the exact retained owner.
Only the source diagram's original declared ports are evaluated here. Fixed native captures
are retained as source data, including implicit categories, dictionaries and mapped diagrams. -/
opaque PreparedCreationInvocation.prepare (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) :
    MetaM PreparedCreationInvocation := do
  let .primitive (.creation family) _ := request.action
    | throwError "a creation invocation requires its original fixed source boundary"
  let inputs ← request.admitInputs (← transaction.view)
  let #[cone, universal] ← IO.ofExcept <|
      (inputs.arguments (← transaction.view)).mapError IO.userError
    | throwError "the creation invocation changed its original two native data inputs"
  withSourceScope request fun context bound => do
    let graph ← transaction.view
    let ownerSource ← family.owner.inContext context
    let sourceMarks ← IO.ofExcept <|
      (captureSourceMarks (← kernel.marks.get) family.owner).mapError IO.userError
    let environment ← request.environment.withSourceMarks sourceMarks (some graph)
    let some owner ← environment.endpointValue? context graph ownerSource
      | throwError "the creation invocation lost its explicit original source-owner binding"
    environment.checkDeclaredInput context graph (← kernel.marks.get) ownerSource owner
    let some node := graph.find owner.value
      | throwError "the creation owner is outside the current value graph"
    let some selected ← NativeLimitSelection.ofExpr?
        (← node.origin.role.source.inContext context)
      | throwError "the creation owner lost its immutable original native selection"
    let some creation := selected.source.creation
      | throwError "the original source owner has no accepted creation interface"
    unless selected.source.construction == family.construction &&
        selected.source.row == family.target.entry.id.raw &&
        creation.lift == family.family.entry.id do
      throwError "the creation invocation changed its original source owner or lift"
    requireCreationTarget kernel request transaction context family cone universal
    let mut diagramValues := #[]
    for argument in family.inputs.diagramPorts, index in [:family.inputs.diagramPorts.size] do
      let source ← argument.source.source.inContext context
      let value ← evaluateSource transaction request.program context bound source
      let graph ← transaction.view
      let actual ← IO.ofExcept <|
        (RuntimeArgument.ofValue graph index value (← kernel.marks.get)).mapError IO.userError
      let value ← request.environment.checkArgument argument.source.source actual
      request.environment.checkDeclaredInput context graph (← kernel.marks.get) source value
      diagramValues := diagramValues.push value
    let mut captures := #[]
    for source in family.captureSources do
      captures := captures.push (← retainCreationCapture kernel request transaction context source)
    let diagram := Json.mkObj [
      ("ctor", toJson family.inputs.diagramTag),
      ("args", .arr (Array.replicate diagramValues.size .null))]
    let template := Json.arr (#[.null, .null, .null, diagram] ++
      Array.replicate captures.size .null)
    let slots : Array ContainerSlot :=
      #[{ path := #[.index 0], binding := cone, fieldIndex := none },
        { path := #[.index 1], binding := universal, fieldIndex := none },
        { path := #[.index 2], binding := owner, fieldIndex := none }] ++
      diagramValues.mapIdx (fun index binding =>
        { path := #[.index 3, .field "args", .index index], binding, fieldIndex := none }) ++
      captures.mapIdx (fun index binding =>
        { path := #[.index (4 + index)], binding, fieldIndex := none })
    let payload ← IO.ofExcept <| (ValuePayload.descriptor template slots).mapError IO.userError
    let .container parameters := payload.data
      | throwError "the creation invocation lost its complete parameter packet"
    let graph ← transaction.view
    discard <| IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    let roots := slots.map (·.binding)
    let views ← InputDescriptorView.collect graph (← kernel.codes.get) roots
    return ⟨request.roles.scope, family, parameters, #[family.input],
      request.scope ++ roots ++ views.flatMap (·.dependencies), views, inputs⟩

/-- Reuse the original sealed inputs and recheck all actual capture owners in the current graph. -/
opaque PreparedCreationInvocation.requireInputs (invocation : PreparedCreationInvocation)
    (request : PreparedRequest) (graph : ValueGraph) : MetaM Unit := do
  request.requirePreparation invocation.preparation
  request.requirePreparation invocation.inputs.telescope.scope
  discard <| IO.ofExcept <| (invocation.inputs.arguments graph).mapError IO.userError
  discard <| IO.ofExcept <| (graph.requiredOwners invocation.dependencies).mapError IO.userError

/-- Encode the whole fixed parameter vector in one scope, preserving every original root path. -/
def PreparedCreationInvocation.encode (invocation : PreparedCreationInvocation)
    (graph : ValueGraph) (receiver : ConnectionGeneration) :
    Except String (EncodedInputs × Array Json) := do
  let roots := invocation.parameters.slots.map fun slot =>
    ({ path := #[.field "parameters"] ++ slot.path, binding := slot.binding } : InputPosition)
  let encoded ← graph.encodeInputs receiver roots invocation.views
  let parameters ← (← invocation.parameters.fill encoded.values).getArr?
  return (encoded, parameters)

end CasRuntime
