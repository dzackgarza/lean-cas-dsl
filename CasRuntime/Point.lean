module

public import CasRuntime.ExecutionContext
public import CasRuntime.Encode
public import CasRuntime.DeclaredInput
public import CasCompiler.PointFamily
public import CasRuntime.CategoricalPointPacket
public import CasCatalogue.Admission
public import CasRuntime.ResultCodec
public import CasRuntime.Literal
public import CasRuntime.NativeMapEndpoints
public import CasRuntime.ConstructionSource
public import CasCompiler.PublishedSource

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
    let some descriptorView ← InputDescriptorView.namedPoint? graph codes value | return none
    let some original := descriptorView.family | return none
    if original.roles.scope != family.roles.scope then return none
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
  preparation : RoleScope
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
  private inputs : InputRoleMap
  parameterPacket : Option ValueContainer
  symbolic : Option ValueContainer

private def categoricalInput (kernel : Kernel) (request : PreparedRequest)
    (context : OpenContext) (graph : ValueGraph) (expected selected : Expr) :
    MetaM ValueBinding := do
  let .mdata data _ := selected
    | throwError "the categorical request lost an original retained input"
  let some key := markedKey? data
    | throwError "the categorical request has no actual input identity"
  let marks ← kernel.marks.get
  let some value := marks[key]?
    | throwError "the categorical request names an unavailable input"
  request.environment.checkDeclaredInput context graph marks expected value
  return value

private def categoricalForms (family : CategoricalPointFamily) (source : Expr) :
    MetaM (Array String) := do
  let mut forms := #[family.owner.input]
  let admitted : Option CasCatalogue.Operation := match family.owner with
    | .named (.morphism entry) => some (.morphism entry)
    | .named (.application entry) => some (.application entry)
    | _ => none
  if let .named (.application entry) := family.owner then
    forms := forms ++ #[entry.id.raw, entry.category.raw]
  if let some admitted := admitted then
    if let some (id, _) ← sourceObjectReference? source then
      let registry : RegistryState := { toSemanticState := ← semanticState }
      let some form := registry.form? id.raw
        | throwError "the categorical point source lost its selected object form"
      if let some reason := registry.rejects admitted form then
        throwError "the categorical point has an incompatible original source form: {reason}"
      let #[entry] := registry.objects.filter (·.id == id)
        | throwError "the categorical point lost its selected source category"
      forms := forms ++ #[id.raw, entry.category.raw]
  return forms

/-- Prepare only the original complete categorical request produced by the common lowerer.
Every packet position is a bound original value; endpoint actions are never rerun here. -/
opaque PreparedPointInvocation.prepare (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM PreparedPointInvocation := do
  let .primitive (.point family) _ := request.action
    | throwError "a complete point packet requires its original categorical boundary"
  unless family.invocation do throwError "an arrow reference is not a whole point demand"
  let graph ← transaction.view
  let inputs ← request.admitInputs graph
  withSourceScope request fun context _ => do
    let (actual, values) ← request.markedArguments kernel.marks context family.parameterCount
    let formal := request.application.map (·.arguments.map (·.source.source)) |>.getD #[]
    unless formal.size == family.parameterCount + 2 do
      throwError "the categorical request lost its original domain and generalized point"
    let some domainTerm := formal[family.parameterCount]?
      | throwError "the categorical request lost its original domain input"
    let some pointTerm := formal[family.parameterCount + 1]?
      | throwError "the categorical request lost its original generalized point input"
    let domainSource ← domainTerm.inContext context
    let pointSource ← pointTerm.inContext context
    let some supplied ← family.request? pointSource
      | throwError "the categorical request lost its original complete descriptor inputs"
    let levels := request.universeArguments.getD []
    let (nativeArrow, _) ← family.arrowAt levels actual
    let (nativeSource, nativeTarget) ← categoricalPointEndpoints nativeArrow
    let arrow ← categoricalInput kernel request context graph nativeArrow supplied.arrow
    let domain ← categoricalInput kernel request context graph domainSource supplied.domain
    let source ← categoricalInput kernel request context graph nativeSource supplied.source
    let target ← categoricalInput kernel request context graph nativeTarget supplied.target
    let argument ← categoricalInput kernel request context graph pointSource supplied.point
    discard <| family.withRequest levels actual supplied.arrow supplied.domain
      supplied.source supplied.target supplied.point
    let packet ← CategoricalPointPacket.prepare family values
    let parameters := packet.parameters.slots.map (·.binding)
    let roots := parameters ++ #[arrow, domain, source, target, argument]
    let views ← InputDescriptorView.collect graph (← kernel.codes.get) roots
    let symbolic ← if family.whole then do
        let .container packet := packet.arrow.data
          | throwError "the native arrow descriptor lost its complete original packet"
        pure packet
      else do
        let payload ← IO.ofExcept <| (ValuePayload.descriptor
          (Json.mkObj [("ctor", toJson "compose"), ("args", .arr #[.null, .null])]) #[
            { path := #[.field "args", .index 0], binding := argument, fieldIndex := none },
            { path := #[.field "args", .index 1], binding := arrow, fieldIndex := none }]).mapError IO.userError
        let .container packet := payload.data
          | throwError "the native composite lost its original descriptor operands"
        pure packet
    return ⟨request.roles.scope, family.operation, parameters, arrow, domain, source, target,
      argument, ← categoricalForms family supplied.source,
      request.scope ++ roots ++ views.flatMap (·.dependencies), views, inputs,
      some packet.parameters, some symbolic⟩

private def prepareCategoricalScalar (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request familyRequest : PreparedRequest) (family : CategoricalPointFamily)
    (levels : List Level) (path : Array FieldLayout) (transaction : CellTransaction) :
    MetaM (Option PreparedPointInvocation) := do
  unless !family.invocation do return none
  let .apply callable arguments _ := request.action | return none
  let #[argumentSource] := arguments | return none
  let some carrier ← family.carrierFamily? | return none
  unless path.map (·.projection) == carrier.path do return none
  let graph ← transaction.view
  let familyInputs ← familyRequest.admitInputs graph
  let inputs ← request.admitInputs graph
  let #[argument] ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    | throwError "the scalar categorical request lost its original point value"
  let codes ← kernel.codes.get
  request.requireFamily familyRequest path graph codes
  let some arrowView ← namedPointRoot? graph codes familyRequest callable carrier.path
    | throwError "the scalar categorical action lost its original arrow and native field path"
  withSourceScope request fun context bound => do
    let pointSource ← argumentSource.inContext context
    let some point ← sourcePointOrigin? pointSource | return none
    let supplied ← family.request? pointSource
    let (actual, values) ← familyRequest.markedArguments kernel.marks context family.parameterCount
    let (nativeArrow, bundle) ← family.arrowAt levels actual
    let (nativeSource, nativeTarget) ← categoricalPointEndpoints nativeArrow
    let function ← family.function levels actual nativeArrow
    let .forallE _ expected _ _ ← whnfR (← inferType function)
      | throwError "the original categorical scalar action has no native function interface"
    checkRegisteredDomains (← inferType pointSource) expected
    unless ← isDefEq (← inferType pointSource) expected do
      throwError "the original point has another selected categorical source"
    let selected ← selectMorphism
      (← markValue kernel.marks arrowView.binding nativeArrow) (some bundle)
    let stated ← inferType selected
    unless stated.isAppOfArity ``Quiver.Hom 4 do
      throwError "the original arrow lost its retained native endpoint projections"
    let originalDomain ← sourceNamedObjectAlias CategoryId.sets point.domain
    let retain := fun (expression expected : Expr) => do
      let value ← evaluateSource transaction request.program context bound expression
      request.environment.checkDeclaredInput context (← transaction.view)
        (← kernel.marks.get) expected value
      pure value
    let domain ← retain (supplied.map (·.domain) |>.getD originalDomain) originalDomain
    let source ← retain (supplied.map (·.source) |>.getD stated.getAppArgs[2]!) nativeSource
    let target ← retain (supplied.map (·.target) |>.getD stated.getAppArgs[3]!) nativeTarget
    if let some supplied := supplied then
      discard <| family.withScalarRequest levels actual supplied.arrow supplied.domain
        supplied.source supplied.target supplied.point
      let selected ← retain supplied.arrow nativeArrow
      unless selected.value == arrowView.binding.value &&
          selected.associationIds.toList.isPrefixOf arrowView.binding.associationIds.toList do
        throwError "the scalar point packet changed its actual selected arrow occurrence"
    let packet ← CategoricalPointPacket.prepare family values
    let parameters := packet.parameters.slots.map (·.binding)
    let graph ← transaction.view
    discard <| IO.ofExcept <| (familyInputs.arguments graph).mapError IO.userError
    discard <| IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    let roots := parameters ++ #[arrowView.binding, domain, source, target, argument]
    let views ← InputDescriptorView.collect graph codes roots #[arrowView]
    return some ⟨request.roles.scope, family.operation, parameters, arrowView.binding,
      domain, source, target, argument, ← categoricalForms family
        (← source.role.source.inContext context),
      familyRequest.scope ++ request.scope ++ roots ++ views.flatMap (·.dependencies),
      views, inputs, some packet.parameters, none⟩

/-- Prepare the named-point dialect only at its checked native carrier action and an original
point map retained by the reader. Other native/opaque actions keep their existing path. All
original inputs are admitted before lowering the source-declared descriptor captures. -/
opaque PreparedPointInvocation.prepare? (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request family : PreparedRequest) (path : Array FieldLayout)
    (transaction : CellTransaction) : MetaM (Option PreparedPointInvocation) := do
  let .primitive boundary universes := family.action | return none
  if let .point selected := boundary then
    return ← prepareCategoricalScalar kernel evaluateSource request family selected universes path transaction
  let .apply callable arguments _ := request.action | return none
  let #[argumentSource] := arguments | return none
  let retainsPoint ← withSourceScope request fun context _ => do
    return (← sourcePointOrigin? (← argumentSource.inContext context)).isSome
  unless retainsPoint do return none
  let selected : Option PointFamily ← match boundary with
    | .registered declared => do
      let .morphism morphismId := declared.source.reference | pure none
      let some entry := (← semanticState).morphisms.find? (·.id == morphismId)
        | throwError "the named point action lost its released morphism"
      pure (some (← PointFamily.forEntry entry))
    | .application selected => pure (some selected)
    | _ => pure none
  let some selected := selected | return none
  unless path.map (·.projection) == selected.path do return none
  let graph ← transaction.view
  let familyInputs ← family.admitInputs graph
  let inputs ← request.admitInputs graph
  let #[argument] ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    | throwError "the named point action lost its complete original operand"
  let codes ← kernel.codes.get
  request.requireFamily family path graph codes
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
    discard <| IO.ofExcept <| (familyInputs.arguments graph).mapError IO.userError
    discard <| IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    let admittedOperation : CasCatalogue.Operation := match selected.owner with
      | .morphism entry => .morphism entry
      | .application entry => .application entry
    let mut forms := match selected.owner with
      | .morphism _ => #[selected.operation]
      | .application entry => #[selected.operation, entry.id.raw, entry.category.raw]
    if let some (objectId, _) ← sourceObjectReference? (← source.role.source.inContext context) then
      let registry : RegistryState := { toSemanticState := ← semanticState }
      let some form := registry.form? objectId.raw
        | throwError "the named point source lost its registered object form"
      if let some reason := registry.rejects admittedOperation form then
        throwError "the named point source has an incompatible input form: {reason}"
      let some object := registry.objects.find? (·.id == objectId)
        | throwError "the named point source lost its original object category"
      forms := forms ++ #[objectId.raw, object.category.raw]
    let roots := arrowView.parameters ++ #[arrowView.binding, domain, source, target, argument]
    let views ← InputDescriptorView.collect graph codes roots #[arrowView]
    return some ⟨request.roles.scope, selected.operation, arrowView.parameters, arrowView.binding,
      domain, source, target, argument, forms, family.scope ++ request.scope ++ roots ++
        views.flatMap (·.dependencies), views, inputs, none, none⟩

/-- Recheck the same sealed input map in the current graph before dispatch. Native roles and
actual immutable bindings were checked at preparation; graph extension requires visibility
and owner checks, not a new source elaboration of the unchanged complete input telescope. -/
opaque PreparedPointInvocation.requireInputs (invocation : PreparedPointInvocation)
    (request : PreparedRequest) (graph : ValueGraph) : MetaM Unit := do
  request.requirePreparation invocation.preparation
  request.requirePreparation invocation.inputs.telescope.scope
  discard <| IO.ofExcept <| (invocation.inputs.arguments graph).mapError IO.userError

/-- Original roots in the released seven-field PointInvocation packet. Nested named-arrow
parameters are encoded beneath its own args field and retain their exact input authorities. -/
def PreparedPointInvocation.roots (invocation : PreparedPointInvocation) : Array InputPosition :=
  (match invocation.parameterPacket with
    | none => invocation.parameters.mapIdx (fun index binding =>
        { path := #[.field "args", .index 1, .index index], binding })
    | some packet => packet.slots.map fun slot =>
        { path := #[.field "args", .index 1] ++ slot.path, binding := slot.binding }) ++ #[
    { path := #[.field "args", .index 2], binding := invocation.arrow },
    { path := #[.field "args", .index 3], binding := invocation.domain },
    { path := #[.field "args", .index 4], binding := invocation.source },
    { path := #[.field "args", .index 5], binding := invocation.target },
    { path := #[.field "args", .index 6], binding := invocation.argument }]

def PreparedPointInvocation.encode (invocation : PreparedPointInvocation)
    (graph : ValueGraph) (receiver : ConnectionGeneration) :
    Except String (EncodedInputs × Json) := do
  let encoded ← graph.encodeInputs receiver invocation.roots invocation.views
  let count := invocation.parameterPacket.map (·.slots.size) |>.getD invocation.parameters.size
  let #[arrow, domain, source, target, argument] := encoded.values.extract count encoded.values.size
    | throw "the named point packet lost a complete original input"
  let parameters ← match invocation.parameterPacket with
    | none => pure (encoded.values.extract 0 count)
    | some packet => (← packet.fill (encoded.values.extract 0 count)).getArr?
  let packet : PointInvocation := {
    operation := invocation.operation
    parameters := parameters
    arrow := arrow
    domain := domain
    source := source
    target := target
    argument := argument
  }
  return (encoded, packet.encode)

/-- Complete original object-action packet at one already prepared source boundary. -/
structure PreparedObjectAction where
  private mk ::
  preparation : RoleScope
  operation : String
  forms : Array String
  packet : ValueContainer
  dependencies : Array ValueBinding
  views : Array InputDescriptorView
  private inputs : InputRoleMap

opaque PreparedObjectAction.prepare (kernel : Kernel) (request : PreparedRequest)
    (graph : ValueGraph) : MetaM PreparedObjectAction := do
  let .primitive (.objectAction family) _ := request.action
    | throwError "an object packet requires its original complete native action"
  let inputs ← request.admitInputs graph
  let values := request.origin.application.map (·.arguments) |>.getD #[]
  let packet ← CategoricalPointPacket.action family values
  let roots := packet.slots.map (·.binding)
  let views ← InputDescriptorView.collect graph (← kernel.codes.get) roots
  let mut forms := #[family.operation ++ "#input"]
  if let .functor _ := family.edge then
    let extra ← withSourceScope request fun context _ => do
      let some receiver := values[family.parameterCount]?.bind id
        | throwError "the object request lost its original receiver"
      if let some (id, _) ← sourceObjectReference? (← receiver.role.source.inContext context) then
        let #[entry] := (← semanticState).objects.filter (·.id == id)
          | throwError "the native object receiver lost its original registered category"
        return #[id.raw, entry.category.raw]
      return #[]
    forms := forms ++ extra
  return ⟨request.roles.scope, family.operation, forms, packet,
    request.scope ++ roots ++ views.flatMap (·.dependencies), views, inputs⟩

opaque PreparedObjectAction.requireInputs (invocation : PreparedObjectAction)
    (request : PreparedRequest) (graph : ValueGraph) : MetaM Unit := do
  request.requirePreparation invocation.preparation
  request.requirePreparation invocation.inputs.telescope.scope
  discard <| IO.ofExcept <| (invocation.inputs.arguments graph).mapError IO.userError

def PreparedObjectAction.encode (invocation : PreparedObjectAction) (graph : ValueGraph)
    (receiver : ConnectionGeneration) : Except String (EncodedInputs × Json) := do
  let roots := invocation.packet.slots.map fun slot =>
    ({ path := slot.path, binding := slot.binding } : InputPosition)
  let encoded ← graph.encodeInputs receiver roots invocation.views
  return (encoded, ← invocation.packet.fill encoded.values)


/-- Validate a whole symbolic tree against its exact source roles and explicit packet
positions. Cross-node endpoints retain their original native occurrence dependencies after
temporary interface unification; no graph search or fabricated mathematical value is used. -/
def preparedSymbolicCheck (kernel : Kernel) (_request : PreparedRequest)
    (transaction : CellTransaction) : PreparedSymbolicCheck := fun graph nodes => do
  let some first := nodes[0]? | return
  let kernel ← kernel.fork
  let nativeScope := nodes.foldl (fun selected node =>
    if selected.source.source.context.entries.size < node.source.source.context.entries.size
      then node else selected) first
  nativeScope.source.source.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let base := nodes.foldl (fun selected node =>
      if selected.environment.context.entries.size < node.environment.context.entries.size
        then node else selected) first
    let compatible := fun (left right : ValueBinding) =>
      left.value == right.value &&
        (left.associationIds.toList.isPrefixOf right.associationIds.toList ||
          right.associationIds.toList.isPrefixOf left.associationIds.toList)
    let marks ← IO.mkRef (#[] : Array (Nat × ValueBinding))
    let retainMarks := fun selected => do
      let previous ← marks.get
      marks.set (← IO.ofExcept <|
        (mergeSourceMarks previous selected).mapError IO.userError)
    for node in nodes do
      retainMarks node.environment.sourceMarks
      if let some prior := node.fieldPrefix then retainMarks prior.sourceMarks
    let remember : ValueBinding → Expr → MetaM Expr := fun value source => do
      discard <| IO.ofExcept <| (graph.requiredOwners #[value]).mapError IO.userError
      let some node := graph.find value.value
        | throwError "a symbolic operand lost its original visible occurrence"
      retainMarks value.sourceMarks
      retainMarks node.origin.sourceMarks
      let source ← markValue kernel.marks value source
      let .mdata data _ := source
        | throwError "a symbolic operand lost its retained native marker"
      let some key := markedKey? data
        | throwError "a symbolic operand has no original occurrence marker"
      retainMarks #[(key, value)]
      return source
    let originalLocals := bindings.map (·.expression)
    let mut markedLocals := originalLocals
    for binding in bindings, index in [:bindings.size] do
      let mut retained : Option ValueBinding := none
      for node in nodes do
        unless node.environment.context.entries.any (·.id == binding.id) do continue
        let current ← IO.ofExcept <| (node.environment.lookup binding.id).mapError IO.userError
        if let some current := current then
          if let some previous := retained then
            unless compatible previous current do
              throwError "one symbolic source binder changed its actual retained occurrence"
          retained := some current
      if let some actual := retained then
        markedLocals := markedLocals.set! index (← remember actual binding.expression)
    let markContext := fun expression => expression.replaceFVars originalLocals markedLocals
    let native := fun value => do
      remember value (markContext (← value.role.source.inContext context))
    let packets := nodes.flatMap fun node => node.inputActions ++ node.action.toArray
    let (descriptors, slots, parameters) ← IO.ofExcept <|
      (ValueContainer.nativeFraming packets).mapError IO.userError
    for exported in packets.flatMap (·.packetExports) do
      unless ← kernel.ledger.owners.isLive exported.owner do transactionFailure .staleOwner
      let owners ← IO.ofExcept <| (graph.requiredOwners exported.captures).mapError IO.userError
      unless ← kernel.ledger.owners.allAlive owners do transactionFailure .staleOwner
    let slotSources ← slots.mapM native
    let parameterPosition? : Json → MetaM (Option Nat) := fun packet => do
      match ScopedReference.parse? packet with
      | .ok (some (.scope index)) =>
        if slots.size ≤ index && index < slots.size + parameters.size then
          pure (some (index - slots.size))
        else pure none
      | _ => pure none
    let readRetained := fun packet => do
      match ScopedReference.parse? packet with
      | .ok none => pure none
      | .ok (some (.scope index)) =>
        if let some source := slotSources[index]? then return some source
        if (← parameterPosition? packet).isSome then return none
        throwError "the symbolic descriptor lost an original packet position"
      | _ => throwError "the symbolic descriptor contains another reference authority"
    let checkDeclared := fun (environment : RuntimeEnvironment) (expected : Expr)
        (value : ValueBinding) => do
      let mut checked := false
      for node in nodes do
        if let some prior := node.fieldPrefix then
          if ← prior.checkEndpoint environment context graph (← kernel.marks.get) expected value then
            checked := true
      unless checked do
        environment.checkDeclaredInput context graph (← kernel.marks.get) expected value
    let shared := fun (left right : Expr) => do
      checkRegisteredDomains left right
      unless ← isDefEq left right do
        throwError "the symbolic maps changed their shared native endpoint"
      let environment ← base.environment.withSourceMarks (← marks.get) (some graph)
      let first ← environment.endpointValue? context graph left
      let second ← environment.endpointValue? context graph right
      match first, second with
      | some first, some second =>
        unless compatible first second do
          throwError "the symbolic maps share different original endpoint occurrences"
        checkDeclared environment left second
        checkDeclared environment right first
      | some first, none =>
        checkDeclared environment right first
      | none, some second =>
        checkDeclared environment left second
      | none, none =>
        let leftInputs ← markedContextReferences (some graph) context (← marks.get) left
        let rightInputs ← markedContextReferences (some graph) context (← marks.get) right
        unless leftInputs.size == rightInputs.size &&
            (leftInputs.zip rightInputs).all (fun (first, second) => compatible first second) do
          throwError "the symbolic maps changed an original endpoint dependency position"
    let unavailable : {α : Type} → MetaM α := fun {_} =>
      throwError "symbolic map admission cannot select or execute another source request"
    let sourceContext : PublishedSourceContext := {
      scope := context
      retained := readRetained
      literal := ScalarLiteral.readAt
      bind := pure
      rebind := fun _ selected => pure selected
      methodParameters := fun _ _ _ => unavailable
      checkInput := fun expected selected => do
        shared expected selected
        let environment ← base.environment.withSourceMarks (← marks.get) (some graph)
        if let some value ← environment.endpointValue? context graph selected then
          checkDeclared environment expected value
      admitMethod := fun _ _ _ => unavailable
      admitProperty := fun _ _ _ => unavailable
      admitPoint := fun _ _ => unavailable
      admitCategorical := fun _ _ _ => unavailable
      projection := fun _ _ => unavailable }
    let retained : Json → MetaM (Option ValueBinding) := fun packet => do
      match ScopedReference.parse? packet with
      | .ok none => pure none
      | .ok (some (.scope index)) =>
        let some value := slots[index]?
          | throwError "the construction leg lost its original symbolic packet position"
        pure (some value)
      | _ => throwError "the construction leg contains another reference authority"
    let sourceContext := { sourceContext with
      constructionCone := fun packet => do
        let result ← kernel.retainedConstructionCone transaction graph context retained packet
        retainMarks ((← kernel.marks.get).mapIdx fun key value => (key, value))
        return result
      creationOwner := fun packet => do
        let result ← kernel.retainedCreationOwner graph context retained packet
        retainMarks ((← kernel.marks.get).mapIdx fun key value => (key, value))
        return result
      constructionEndpoint := fun original target candidate => do
        let environment ← base.environment.withSourceMarks (← marks.get) (some graph)
        kernel.checkConstructionEndpoint transaction graph context environment
          original target candidate }
    let endpoint : PreparedSymbolicEndpoint → MetaM PublishedSource.NativeSymbolicEndpoint :=
      fun endpoint => match endpoint with
        | .value value => return .value (← native value)
        | .inline position => pure (.inline position)
    let asNativeMap : Expr → MetaM Expr := fun expression => do
      let type ← inferType expression
      if type.isAppOfArity ``Quiver.Hom 4 then return expression
      let type ← whnfR type
      if type.isAppOfArity ``Quiver.Hom 4 then return expression
      let .forallE _ _ range _ := type
        | throwError "the symbolic callable has no original native function or Hom interface"
      if range.hasLooseBVars then
        throwError "a dependent callable requires its independently supplied native map interface"
      mkAppM ``TypeCat.ofHom #[expression]
    let rec prepareNodes : List PreparedSymbolicNode → Nat →
        Array PublishedSource.NativeSymbolicNode → MetaM Unit
      | [], _, nativeNodes => do
        Elab.Term.TermElabM.run' do
          Elab.Term.withSynthesize do
            PublishedSource.validateSymbolicBatch sourceContext nativeNodes
              (fun first second => do shared first second)
              (parameterCount := parameters.size) (parameterPosition? := parameterPosition?)
      | node :: remaining, descriptorIndex, nativeNodes => do
        let inputActions := descriptors.extract descriptorIndex
          (descriptorIndex + node.inputActions.size)
        let descriptorIndex := descriptorIndex + node.inputActions.size
        let descriptor := if node.action.isSome then descriptors[descriptorIndex]? else none
        let descriptorIndex := descriptorIndex + if node.action.isSome then 1 else 0
        let operands ← node.operands.mapM fun operand => match operand with
          | .value value => do
            let expression ← native value
            let expression ← if node.tag == "compose" || node.tag == "map" then
                asNativeMap expression else pure expression
            pure (PublishedSource.NativeSymbolicOperand.value expression)
          | .objectData value => return .objectData (← endpoint value)
          | .mapData source target => return .mapData (← endpoint source) (← endpoint target)
        let framed := some (← endpoint node.framed.1, ← endpoint node.framed.2)
        let nextNode := fun expected => prepareNodes remaining descriptorIndex
          (nativeNodes.push { expected, tag := node.tag, operands, descriptor, framed, inputActions })
        match node.fieldPrefix with
        | none =>
          nextNode (← asNativeMap (markContext (← node.source.source.inContext context)))
        | some prior =>
          let originalMarks ← marks.get
          prior.withMarkedType graph originalMarks (fun original type captured => do
            let type ← (← original.close type).inContext context
            let mut keyRenaming : Array (Nat × Nat) := #[]
            for (key, value) in captured do
              if originalMarks.any (·.1 == key) then continue
              let fresh ← kernel.marks.modifyGet fun values => (values.size, values.push value)
              keyRenaming := keyRenaming.push (key, fresh)
              retainMarks #[(fresh, value)]
            let rec rekey : Expr → Expr
              | .mdata data body =>
                let data := match markedKey? data with
                  | none => data
                  | some key => match keyRenaming.find? (·.1 == key) with
                    | none => data
                    | some (_, fresh) => data.setNat `CasCompiler.lower.value fresh
                .mdata data (rekey body)
              | .app function argument => .app (rekey function) (rekey argument)
              | .lam name type body info => .lam name (rekey type) (rekey body) info
              | .forallE name type body info => .forallE name (rekey type) (rekey body) info
              | .letE name type value body nonDependent =>
                .letE name (rekey type) (rekey value) (rekey body) nonDependent
              | .proj owner index body => .proj owner index (rekey body)
              | expression => expression
            let type := markContext (rekey type)
            check type
            withLocalDeclD (← mkFreshUserName `nativeFieldInterface) type fun arrow => do
              nextNode (← asNativeMap arrow))
            (reservedSources := nodes.map (·.source.source))
            (minimumKey := (← kernel.marks.get).size)
    prepareNodes nodes.toList 0 #[]

/-- Seal the complete map result and a continuation at its independently checked native
carrier path. The continuation captures the actual returned packet and original selection,
not a reconstructed map or a provider lookup. -/
opaque PreparedPointInvocation.resultCodec (invocation : PreparedPointInvocation)
    (kernel : Kernel) (request : PreparedRequest) (transaction : CellTransaction)
    (registration : Registration) : MetaM (Option (PreparedResultCodec request.roles.scope)) := do
  let .primitive (.point family) levels := request.action | return none
  unless family.invocation do return none
  request.requirePreparation invocation.preparation
  let some parameters := invocation.parameterPacket
    | throwError "the complete point result lost its original public parameters"
  let path ← (← family.carrierFamily?).mapM fun carrier => do
    let arguments := request.application.map (·.arguments.map (·.source.source)) |>.getD #[]
    carrier.specialize request.source levels arguments
  let makeCallable := path.map fun path =>
    (fun graph source packet => do
      unless source.address == request.source.address ++ path.path && source.kind == .function do
        throwError "the map callable transport changed its exact native field"
      let captures := parameters.slots.map (·.binding) ++ #[invocation.domain, invocation.target] ++
        packet.slots.map (·.binding)
      discard <| IO.ofExcept <|
        (graph.requiredOwners captures).mapError IO.userError
      let program ← kernel.ledger.owners.identities.fresh .program
      kernel.codes.modify (·.insert program (.retainedPoint request registration parameters
        invocation.domain invocation.target packet path))
      return (.closure program captures : ValuePayload) : PreparedCallableTransport)
  let codec ← PreparedResultCodec.forMap request (← transaction.view)
    invocation.domain invocation.target (← kernel.marks.get) makeCallable path invocation.symbolic
    #[(invocation.arrow, invocation.source, invocation.target),
      (invocation.argument, invocation.domain, invocation.source)]
    (some (preparedSymbolicCheck kernel request transaction))
  return some codec

/-- Continue one actual returned native map. Its original completion, supplier, packet and
carrier ancestry are checked before the same selected point operation receives a new point. -/
opaque PreparedPointInvocation.retained (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (original : PreparedRequest)
    (registration : Registration) (parameters : ValueContainer) (source target : ValueBinding)
    (packet : ValueContainer) (path : NativePointPath original.source)
    (captures : Array ValueBinding) : MetaM PreparedPointInvocation := do
  let .apply callable arguments _ := request.action
    | throwError "a returned map continuation requires its actual callable"
  let #[argumentSource] := arguments
    | throwError "a returned map requires its unchanged original point argument"
  let graph ← transaction.view
  let inputs ← request.admitInputs graph
  let #[argument] ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    | throwError "the returned map lost its complete current operand"
  let some completion ← transaction.completionFor? original.occurrence
    | throwError "the returned map lost its original producing completion"
  original.requirePreparation completion.request.roles.scope
  let .invocation dispatch _ _ := completion.producer
    | throwError "the returned point code has no original provider invocation"
  let .primitive selected := dispatch.selected
    | throwError "the returned point code changed its original dispatch kind"
  unless selected.registration == registration &&
      selected.manifestDigest == kernel.manifestDigest && selected.profileDigest == kernel.profile.sha256 do
    throwError "the returned map changed its originally selected realization"
  let expectedCaptures := parameters.slots.map (·.binding) ++ #[source, target] ++
    packet.slots.map (·.binding)
  unless captures.size == expectedCaptures.size &&
      (captures.zip expectedCaptures).all (fun (left, right) =>
        left.value == right.value && left.associationIds == right.associationIds) do
    throwError "the returned map changed its complete original captures"
  let arrow := completion.response.root
  let some node := graph.find arrow.value | throwError "the returned map lost its actual root"
  let .container returned := node.payload.data
    | throwError "the inline returned map lost its complete original packet"
  unless returned.retainsOriginalPacket packet do
    throwError "the returned map changed its admitted original packet or reference slots"
  let some _ ← IO.ofExcept <|
      (graph.projectionBasis callable arrow path.path).mapError IO.userError
    | throwError "the returned callable has another native root or carrier path"
  withSourceScope request fun context bound => do
    let expression ← argumentSource.inContext context
    let some point ← sourcePointOrigin? expression
      | throwStratum .noImplementation "the returned map requires an original source-prepared point"
    let domainSource ← sourceNamedObjectAlias CategoryId.sets point.domain
    let domain ← evaluateSource transaction request.program context bound domainSource
    request.environment.checkDeclaredInput context (← transaction.view) (← kernel.marks.get)
      domainSource domain
    let originalParameters := parameters.slots.map (·.binding)
    let roots := originalParameters ++ #[arrow, domain, source, target, argument]
    let graph ← transaction.view
    discard <| IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    let views ← InputDescriptorView.collect graph (← kernel.codes.get) roots
    return ⟨request.roles.scope, registration.operation, originalParameters,
      arrow, domain, source, target, argument, #[registration.input],
      request.scope ++ roots ++ captures ++ views.flatMap (·.dependencies), views, inputs,
      some parameters, none⟩

end CasRuntime

