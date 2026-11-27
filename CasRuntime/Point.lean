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


private def selectPointSource (identities : IdentitySupply) (selection : SourceSelection Expr)
    (declaredType : Option Expr := none) :
    StateCpsT (OpenContext × SourceSelectionScope Expr) MetaM Expr :=
  fun _ state continuation =>
    SourceSelectionScope.withBinding identities state.2 state.1 selection
      (fun context selections value => continuation value (context, selections))
      (declaredType := declaredType)

private def namedPointRequest? (family : PointFamily) (selected : SourceSelection Expr) :
    MetaM (Option NativePointRequest) := do
  match selected.pointRequest with
  | none => return none
  | some (.named original request) =>
    unless (SelectedApplicationFamily.application family).exactlyMatches (.application original) do
      throwError "the point request names a different released callable family"
    return some request
  | some (.categorical ..) =>
    throwError "the named point request changed its original owner kind"

private def categoricalPointRequest? (family : CategoricalPointFamily)
    (selected : SourceSelection Expr) : MetaM (Option CategoricalPointRequest) := do
  match selected.pointRequest with
  | none => return none
  | some (.categorical original request) =>
    unless (SelectedApplicationFamily.point family).exactlyMatches (.point original) do
      throwError "the retained generalized point changed its selected operation"
    return some request
  | some (.named ..) =>
    throwError "the categorical point request changed its original owner kind"




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

private def categoricalInput (request : PreparedRequest)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (graph : ValueGraph) (expected selected : Expr) : MetaM ValueBinding := do
  let .fvar localId := selected.consumeMData
    | throwError "the categorical request lost an original retained input binder"
  let some binding := context.bindings.find? (·.expression.fvarId! == localId)
    | throwError "the categorical request names a binder outside its complete source context"
  let some value := bound[binding.id]?
    | throwError "the categorical request names an unavailable bound input"
  let environment ← RuntimeEnvironment.captureBound request.environment.worker context bound graph
    (some request.environment)
  environment.checkDeclaredInput context graph expected value
  return value

private def categoricalForms (context : OpenContext) (selections : SourceSelectionScope Expr)
    (family : CategoricalPointFamily) (source : Expr) : MetaM (Array String) := do
  let mut forms := #[family.owner.input]
  let admitted : Option CasCatalogue.Operation := match family.owner with
    | .named (.morphism entry) => some (.morphism entry)
    | .named (.application entry) => some (.application entry)
    | _ => none
  if let .named (.application entry) := family.owner then
    forms := forms ++ #[entry.id.raw, entry.category.raw]
  if let some admitted := admitted then
    if let some (entry, _) ← sourceObjectSelection? context selections source then
      let registry : RegistryState := { toSemanticState := ← semanticState }
      let some form := registry.form? entry.id.raw
        | throwError "the categorical point source lost its selected object form"
      if let some reason := registry.rejects admitted form then
        throwError "the categorical point has an incompatible original source form: {reason}"
      forms := forms ++ #[entry.id.raw, entry.category.raw]
  return forms



opaque PreparedPointInvocation.prepare (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM PreparedPointInvocation := do
  let .primitive (.point family) _ := request.action
    | throwError "a complete point packet requires its original categorical boundary"
  unless family.invocation do throwError "an arrow reference is not a whole point demand"
  let graph ← transaction.view
  let inputs ← request.admitInputs graph
  withSourceScope request fun context bound => do
    request.withArguments kernel.ledger.owners.identities context bound family.parameterCount
        fun context bound actual values => do
      let formal := request.application.map (·.arguments.map (·.source.source)) |>.getD #[]
      unless formal.size == family.parameterCount + 2 do
        throwError "the categorical request lost its original domain and generalized point"
      let some domainTerm := formal[family.parameterCount]?
        | throwError "the categorical request lost its original domain input"
      let some pointTerm := formal[family.parameterCount + 1]?
        | throwError "the categorical request lost its original generalized point input"
      let domainSource ← domainTerm.inContext context
      let pointSource ← pointTerm.inContext context
      let some selected ← request.source.selected? context
        | throwError "the categorical request lost its exact selected source binding"
      let some supplied ← categoricalPointRequest? family selected
        | throwError "the categorical request lost its original complete descriptor inputs"
      let selections ← request.selections.inContext context
      let levels := request.universeArguments.getD []
      let (nativeArrow, _) ← family.arrowAt levels actual
      let (nativeSource, nativeTarget) ← categoricalPointEndpoints nativeArrow
      let arrow ← categoricalInput request context bound graph nativeArrow supplied.arrow
      let domain ← categoricalInput request context bound graph domainSource supplied.domain
      let source ← categoricalInput request context bound graph nativeSource supplied.source
      let target ← categoricalInput request context bound graph nativeTarget supplied.target
      let argument ← categoricalInput request context bound graph pointSource supplied.point
      context.withOriginalSources (actual ++
          #[supplied.arrow, supplied.domain, supplied.source, supplied.target, supplied.point])
          fun native => do
        let parameters := native.extract 0 actual.size
        let inputs := native.extract actual.size native.size
        discard <| family.withRequest levels parameters
          inputs[0]! inputs[1]! inputs[2]! inputs[3]! inputs[4]!
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
        argument, ← categoricalForms context selections family supplied.source,
        request.scope ++ roots ++ views.flatMap (·.dependencies), views, inputs,
        some packet.parameters, some symbolic⟩

private def prepareCategoricalScalar (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request familyRequest : PreparedRequest) (family : CategoricalPointFamily)
    (levels : List Level) (path : Array FieldLayout) (transaction : CellTransaction) :
    MetaM (Option PreparedPointInvocation) := do
  unless !family.invocation do return none
  let .apply callable arguments _ := request.action | return none
  unless arguments.size == 1 do return none
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
    withBindingContext graph context bound argument fun context bound => do
      let pointSource ← argument.selectedSource context
      let some pointSelection ← argument.role.selected? context | return none
      let some point := pointSelection.pointOrigin | return none
      let supplied ← categoricalPointRequest? family pointSelection
      familyRequest.withArguments kernel.ledger.owners.identities context bound family.parameterCount
          fun context bound actual values => do
        let selections ← SourceSelectionScope.merge (← request.environment.selections.inContext context)
          (← familyRequest.environment.selections.inContext context)
        let selections ← SourceSelectionScope.merge selections (← argument.role.selections.inContext context)
        let (nativeArrow, bundle) ← family.arrowAt levels actual
        let (nativeSource, nativeTarget) ← categoricalPointEndpoints nativeArrow
        let function ← family.function levels actual nativeArrow
        let .forallE _ expected _ _ ← whnfR (← inferType function)
          | throwError "the original categorical scalar action has no native function interface"
        context.withOriginalSources #[← inferType pointSource, expected] fun native => do
          checkRegisteredDomains native[0]! native[1]!
          unless ← isDefEq native[0]! native[1]! do
            throwError "the original point has another selected categorical source"
        withBindingContext graph context bound arrowView.binding fun context bound => do
          withBoundValue kernel.ledger.owners.identities context bound
              (← arrowView.binding.selectedSource context) arrowView.binding fun context bound arrowSource => do
            let some arrowSelection ← arrowView.binding.role.selected? context
              | throwError "the scalar categorical action lost its complete selected arrow"
            let select := fun selection expected =>
              selectPointSource kernel.ledger.owners.identities selection expected
            (selectMorphism { arrowSelection with value := arrowSource } select (some bundle)).runK
                (context, selections) fun selected state => do
              let (context, selections) := state
              let stated ← inferType selected
              unless stated.isAppOfArity ``Quiver.Hom 4 do
                throwError "the original arrow lost its retained native endpoint projections"
              let originalDomain := point.domain
              let environment ← RuntimeEnvironment.captureBound request.environment.worker
                context bound (← transaction.view) (some request.environment) selections
              let retain := fun (expression expected : Expr) => do
                let value ← environment.evaluateSource evaluateSource transaction request.program
                  context bound expression selections
                environment.checkDeclaredInput context (← transaction.view) expected value
                pure value
              let domain ← retain (supplied.map (·.domain) |>.getD originalDomain) originalDomain
              let source ← retain (supplied.map (·.source) |>.getD stated.getAppArgs[2]!) nativeSource
              let target ← retain (supplied.map (·.target) |>.getD stated.getAppArgs[3]!) nativeTarget
              if let some supplied := supplied then
                context.withOriginalSources (actual ++ #[supplied.arrow, supplied.domain,
                    supplied.source, supplied.target, supplied.point, point.domain]) fun native => do
                  let parameters := native.extract 0 actual.size
                  let fields := native.extract actual.size native.size
                  family.checkScalarRequest levels parameters
                    fields[0]! fields[1]! fields[2]! fields[3]! fields[4]! fields[5]!
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
                domain, source, target, argument, ← categoricalForms context selections family
                  (← source.selectedSource context),
                familyRequest.scope ++ request.scope ++ roots ++ views.flatMap (·.dependencies),
                views, inputs, some packet.parameters, none⟩




opaque PreparedPointInvocation.prepare? (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request family : PreparedRequest) (path : Array FieldLayout)
    (transaction : CellTransaction) : MetaM (Option PreparedPointInvocation) := do
  let .primitive boundary universes := family.action | return none
  if let .point selected := boundary then
    return ← prepareCategoricalScalar kernel evaluateSource request family selected universes path transaction
  let .apply callable arguments _ := request.action | return none
  unless arguments.size == 1 do return none
  let graph ← transaction.view
  let familyInputs ← family.admitInputs graph
  let inputs ← request.admitInputs graph
  let #[argument] ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    | throwError "the named point action lost its complete original operand"
  let retainsPoint ← withSourceScope request fun context bound =>
    withBindingContext graph context bound argument fun context _ => do
      return ((← argument.role.selected? context).bind (·.pointOrigin)).isSome
  unless retainsPoint do return none
  let selected : Option PointFamily ← match boundary with
    | .registered declared => do
      let .morphism morphismId := declared.source.reference | pure none
      let .named (.registered (.inr entry) _) := declared.selectedReference
        | throwError "the named point action lost its complete selected morphism row"
      unless entry.id == morphismId do
        throwError "the named point action changed its released morphism"
      let some selected := declared.pointFamily
        | throwUnsupportedSource "the named morphism has no native input-function path"
      let .morphism original := selected.owner
        | throwError "the named point action changed its released morphism"
      unless SelectedSourceReference.exactlyMatches declared.selectedReference
          (.named (.registered (.inr original) selected.category)) do
        throwError "the named point action changed its released morphism"
      pure (some selected)
    | .application selected => pure (some selected)
    | _ => pure none
  let some selected := selected | return none
  unless path.map (·.projection) == selected.path do return none
  let codes ← kernel.codes.get
  request.requireFamily family path graph codes
  let some arrowView ← namedPointRoot? graph codes family callable selected.path
    | throwError "the named point action lost its exact original arrow and field relation"
  withSourceScope request fun context bound => do
    withBindingContext graph context bound argument fun context bound => do
      let pointSource ← argument.selectedSource context
      let some pointSelection ← argument.role.selected? context | return none
      let some point := pointSelection.pointOrigin | return none
      let supplied ← namedPointRequest? selected pointSelection
      let count := family.application.map (·.arguments.size) |>.getD 0
      family.withArguments kernel.ledger.owners.identities context bound count
          fun context bound actual _ => do
        let selections ← SourceSelectionScope.merge (← request.environment.selections.inContext context)
          (← family.environment.selections.inContext context)
        let selections ← SourceSelectionScope.merge selections (← argument.role.selections.inContext context)
        let head := selected.family.instantiateLevelParams selected.universeParams universes
        let originalArrow := mkAppN head actual
        let select := fun selection => selectPointSource kernel.ledger.owners.identities selection none
        (selected.withEndpoints originalArrow select).runK (context, selections)
            fun (sourceSource, targetSource) state => do
          let (context, selections) := state
          let environment ← RuntimeEnvironment.captureBound request.environment.worker
            context bound graph (some request.environment) selections
          let domainSource := point.domain
          let function ← selected.function originalArrow
          let .forallE _ expected _ _ ← whnfR (← inferType function)
            | throwError "the named arrow lost its native point-function interface"
          context.withOriginalSources #[← inferType pointSource, expected] fun native => do
            checkRegisteredDomains native[0]! native[1]!
            unless ← isDefEq native[0]! native[1]! do
              throwError "the original point has a different named-arrow source"
          let retain := fun (source expected : Expr) (index : Nat) => do
            let value ← environment.evaluateSource evaluateSource transaction request.program
              context bound source selections
            let graph ← transaction.view
            let .ok actual := RuntimeArgument.ofValue graph index value
              | throwError "a named point descriptor is outside its original graph"
            let checked ← environment.checkArgument (← context.close expected) actual
            environment.checkDeclaredInput context graph expected value
            return checked
          if let some supplied := supplied then
            context.withOriginalSources #[supplied.arrow, supplied.domain, supplied.source,
                supplied.target, point.domain] fun native =>
              selected.checkRequest native[0]! native[1]! native[2]! native[3]! native[4]!
            let original ← retain supplied.arrow originalArrow 0
            unless original.value == arrowView.binding.value &&
                original.associationIds.toList.isPrefixOf arrowView.binding.associationIds.toList do
              throwError "the named point request changed its actual original arrow occurrence"
            let values := family.origin.application.map (·.arguments) |>.getD #[]
            unless values.size == actual.size do
              throwError "the named point request lost its original parameter value table"
            for source in actual, value in values do
              match value with
              | some value => environment.checkDeclaredInput context graph source value
              | none =>
                unless ← isProof source do
                  throwError "the named point request is missing an original computational parameter"
          let domain ← retain (supplied.map (·.domain) |>.getD domainSource) domainSource 0
          let source ← retain (supplied.map (·.source) |>.getD sourceSource) sourceSource 1
          let target ← retain (supplied.map (·.target) |>.getD targetSource) targetSource 2
          let graph ← transaction.view
          discard <| IO.ofExcept <| (familyInputs.arguments graph).mapError IO.userError
          discard <| IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
          let admittedOperation : CasCatalogue.Operation := match selected.owner with
            | .morphism entry => .morphism entry
            | .application entry => .application entry
          let mut forms := match selected.owner with
            | .morphism _ => #[selected.operation]
            | .application entry => #[selected.operation, entry.id.raw, entry.category.raw]
          if let some (object, _) ← sourceObjectSelection? context selections
              (← source.selectedSource context) then
            let registry : RegistryState := { toSemanticState := ← semanticState }
            let some form := registry.form? object.id.raw
              | throwError "the named point source lost its registered object form"
            if let some reason := registry.rejects admittedOperation form then
              throwError "the named point source has an incompatible input form: {reason}"
            forms := forms ++ #[object.id.raw, object.category.raw]
          let roots := arrowView.parameters ++ #[arrowView.binding, domain, source, target, argument]
          let views ← InputDescriptorView.collect graph codes roots #[arrowView]
          return some ⟨request.roles.scope, selected.operation, arrowView.parameters, arrowView.binding,
            domain, source, target, argument, forms, family.scope ++ request.scope ++ roots ++
              views.flatMap (·.dependencies), views, inputs, none, none⟩




opaque PreparedPointInvocation.requireInputs (invocation : PreparedPointInvocation)
    (request : PreparedRequest) (graph : ValueGraph) : MetaM Unit := do
  request.requirePreparation invocation.preparation
  request.requirePreparation invocation.inputs.telescope.scope
  discard <| IO.ofExcept <| (invocation.inputs.arguments graph).mapError IO.userError



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
    let extra ← withSourceScope request fun context bound => do
      let some receiver := values[family.parameterCount]?.bind id
        | throwError "the object request lost its original receiver"
      withBindingContext graph context bound receiver fun context _ => do
        let selections ← SourceSelectionScope.merge (← request.environment.selections.inContext context)
          (← receiver.role.selections.inContext context)
        if let some (entry, _) ← sourceObjectSelection? context selections
            (← receiver.selectedSource context) then
          return #[entry.id.raw, entry.category.raw]
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


private structure PointSourceState where
  context : OpenContext
  bound : Std.HashMap BindingId ValueBinding
  selections : SourceSelectionScope Expr




opaque preparedSymbolicCheck (kernel : Kernel) (_request : PreparedRequest)
    (transaction : CellTransaction) : PreparedSymbolicCheck := fun graph nodes => do
  let some first := nodes[0]? | return
  let kernel ← kernel.fork
  let base := nodes.foldl (fun selected node =>
    if selected.environment.context.entries.size < node.environment.context.entries.size
      then node else selected) first
  base.environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let compatible := fun (left right : ValueBinding) =>
      left.value == right.value &&
        (left.associationIds.toList.isPrefixOf right.associationIds.toList ||
          right.associationIds.toList.isPrefixOf left.associationIds.toList)
    let bound := base.environment.bound
    let packets := nodes.flatMap fun node => node.inputActions ++ node.action.toArray
    let (descriptors, slots, parameters) ← IO.ofExcept <|
      (ValueContainer.nativeFraming packets).mapError IO.userError
    for exported in packets.flatMap (·.packetExports) do
      unless ← kernel.ledger.owners.isLive exported.owner do transactionFailure .staleOwner
      let owners ← IO.ofExcept <| (graph.requiredOwners exported.captures).mapError IO.userError
      unless ← kernel.ledger.owners.allAlive owners do transactionFailure .staleOwner
    let withNative (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
        (value : ValueBinding)
        (action : OpenContext → Std.HashMap BindingId ValueBinding → Expr → MetaM Unit) :
        MetaM Unit := do
      discard <| IO.ofExcept <| (graph.requiredOwners #[value]).mapError IO.userError
      withBindingContext graph context bound value fun context bound => do
        withBoundValue kernel.ledger.owners.identities context bound
          (← value.selectedSource context) value action
    let withEndpoint (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
        (endpoint : PreparedSymbolicEndpoint)
        (action : OpenContext → Std.HashMap BindingId ValueBinding →
          PublishedSource.NativeSymbolicEndpoint → MetaM Unit) : MetaM Unit := do
      match endpoint with
      | .value value => do
        withNative context bound value fun context bound source =>
          action context bound (.value source)
      | .inline position => action context bound (.inline position)
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
    let finish := fun (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
        (selections : SourceSelectionScope Expr)
        (slotSources : Array Expr) (nativeNodes : Array PublishedSource.NativeSymbolicNode) => do
      let environment := fun (state : PointSourceState) =>
        RuntimeEnvironment.captureBound base.environment.worker state.context state.bound graph
          (some base.environment) state.selections
      let stateIn := fun (state : PointSourceState) context bound => do
        let current ← environment { state with context, bound }
        return ({ context, bound, selections := ← current.selections.inContext context } :
          PointSourceState)
      let checkDeclared := fun (state : PointSourceState)
          (expected : Expr) (value : ValueBinding) => do
        let environment ← environment state
        let mut checked := false
        for node in nodes do
          if let some prior := node.fieldPrefix then
            if ← prior.checkEndpoint environment state.context graph expected value then checked := true
        unless checked do environment.checkDeclaredInput state.context graph expected value
      let references := fun (state : PointSourceState)
          expression => do
        let positions ← computationalDependencies (state.context.bindings.map (·.expression)) expression
        let mut values := #[]
        for position in positions do
          let some binding := state.context.bindings[position]?
            | throwError "a symbolic endpoint lost an original context dependency"
          if let some value := state.bound[binding.id]? then values := values.push value
        return values
      let shared := fun (state : PointSourceState)
          (left right : Expr) => do
        checkRegisteredDomains left right
        unless ← isDefEq left right do
          state.context.withOriginalSources #[left, right] fun original => do
            checkRegisteredDomains original[0]! original[1]!
            unless ← isDefEq original[0]! original[1]! do
              throwError "the symbolic maps changed their shared native endpoint"
        let environment ← environment state
        let first ← environment.endpointValue? state.context graph left
        let second ← environment.endpointValue? state.context graph right
        match first, second with
        | some first, some second =>
          unless compatible first second do
            throwError "the symbolic maps share different original endpoint occurrences"
          checkDeclared state left second
          checkDeclared state right first
        | some first, none => checkDeclared state right first
        | none, some second => checkDeclared state left second
        | none, none =>
          let leftInputs ← references state left
          let rightInputs ← references state right
          unless leftInputs.size == rightInputs.size &&
              (leftInputs.zip rightInputs).all (fun (first, second) => compatible first second) do
            throwError "the symbolic maps changed an original endpoint dependency position"
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
      let retained : Json → MetaM (Option ValueBinding) := fun packet => do
        match ScopedReference.parse? packet with
        | .ok none => pure none
        | .ok (some (.scope index)) =>
          let some value := slots[index]?
            | throwError "the construction leg lost its original symbolic packet position"
          pure (some value)
        | _ => throwError "the construction leg contains another reference authority"
      let unavailable : {α : Type} → MetaM α := fun {_} =>
        throwError "symbolic map admission cannot select or execute another source request"
      let sourceContext : PublishedSourceContext
          PointSourceState := {
        scope := (·.context)
        selections := (·.selections)
        identities := fun _ => kernel.ledger.owners.identities
        select := fun selection declaredType _ state continuation =>
          controlAt MetaM fun run =>
            SourceSelectionScope.withBinding kernel.ledger.owners.identities
              state.selections state.context selection
              (fun context selections sourceVariable =>
                run (continuation sourceVariable { state with context, selections }))
              (declaredType := declaredType)
        retained := fun _ => readRetained
        actionSource := fun packet _ state continuation =>
          controlAt MetaM fun run => do
            let some _ ← readRetained packet
              | run (continuation none state)
            let some value ← retained packet
              | run (continuation none state)
            withNativeInterface kernel.ledger.owners.identities graph
                state.context state.bound state.selections value
                fun context bound selections nativeSource => do
              let next ← stateIn { state with selections } context bound
              run (continuation (some nativeSource) next)
        literal := ScalarLiteral.readAt
        bind := pure
        bindAt := fun source declaredType _ state continuation =>
          controlAt MetaM fun run => do
            if let .fvar localId := source then
              let some binding := state.context.bindings.find? (·.expression.fvarId! == localId)
                | throwError "the symbolic source is outside its complete native context"
              if let some value := state.bound[binding.id]? then
                return ← withBoundValue kernel.ledger.owners.identities state.context state.bound
                  source value
                  (fun context bound sourceVariable => do
                    let next ← stateIn state context bound
                    let selections ← next.selections.alias context
                      (← value.selectedSource context) sourceVariable
                    run (continuation sourceVariable { next with selections }))
                  (declaredType := some declaredType)
            if ← withoutModifyingState (isDefEq (← inferType source) declaredType) then
              return ← run (continuation source state)
            let allocated ← kernel.ledger.owners.identities.fresh .sourceBinding
            state.context.withLocalBinding ⟨allocated.worker, allocated.serial⟩ .parameter
              `symbolicSource declaredType
              (fun context binding => do
                let selections ← state.selections.alias context source binding.expression
                run (continuation binding.expression { state with context, selections }))
              (originalSource := some source)
        withLocal := fun name type _ state continuation =>
          controlAt MetaM fun run => do
            let allocated ← kernel.ledger.owners.identities.fresh .sourceBinding
            state.context.withLocalBinding ⟨allocated.worker, allocated.serial⟩ .parameter name type
              fun context binding => run (continuation binding.expression { state with context })
        rebind := fun _ selected => pure selected
        methodParameters := fun _ _ _ _ _ _ => liftM unavailable
        checkInput := fun state expected selected => do
          shared state expected selected
          if let some value ← (← environment state).endpointValue? state.context graph selected then
            checkDeclared state expected value
        admitMethod := fun _ _ _ _ => unavailable
        admitProperty := fun _ _ _ _ => unavailable
        admitPoint := fun _ _ _ => unavailable
        admitCategorical := fun _ _ _ _ => unavailable
        constructionCone := fun packet _ state continuation =>
          controlAt MetaM fun run =>
            kernel.retainedConstructionCone transaction graph state.context state.bound retained packet
              fun context bound result => do
                let next ← stateIn state context bound
                run (continuation result next)
        creationOwner := fun packet _ state continuation =>
          controlAt MetaM fun run =>
            kernel.retainedCreationOwner graph state.context state.bound retained packet
              fun context bound result => do
                let next ← stateIn state context bound
                run (continuation result next)
        constructionEndpoint := fun state original target candidate => do
          kernel.checkConstructionEndpoint transaction graph state.context (← environment state)
            original target candidate
        projection := fun _ _ => liftM (m := MetaM) unavailable }
      let initial ← stateIn { context, bound, selections } context bound
      Elab.Term.TermElabM.run' do
        Elab.Term.withSynthesize do
          PublishedSource.validateSymbolicBatch sourceContext initial nativeNodes
            (fun state first second => do shared state first second)
            (parameterCount := parameters.size) (parameterPosition? := parameterPosition?)
    let rec prepareNodes (remaining : List PreparedSymbolicNode) (descriptorIndex : Nat)
        (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
        (selections : SourceSelectionScope Expr)
        (slotSources : Array Expr) (nativeNodes : Array PublishedSource.NativeSymbolicNode) :
        MetaM Unit := do
      match remaining with
      | [] => finish context bound selections slotSources nativeNodes
      | node :: remaining =>
        let inputActions := descriptors.extract descriptorIndex
          (descriptorIndex + node.inputActions.size)
        let descriptorIndex := descriptorIndex + node.inputActions.size
        let descriptor := if node.action.isSome then descriptors[descriptorIndex]? else none
        let descriptorIndex := descriptorIndex + if node.action.isSome then 1 else 0
        let nextNode := fun context bound selections operands =>
          withEndpoint context bound node.framed.1 fun context bound source =>
            withEndpoint context bound node.framed.2 fun context bound target => do
              let next := fun context bound expected =>
                prepareNodes remaining descriptorIndex context bound selections slotSources
                  (nativeNodes.push {
                    expected := expected
                    tag := node.tag
                    operands := operands
                    descriptor := descriptor
                    framed := some (source, target)
                    inputActions := inputActions })
              match node.fieldPrefix with
              | none => next context bound (← asNativeMap (← node.source.source.inContext context))
              | some prior =>
                prior.withBoundType context graph bound fun context type bound => do
                  let allocated ← kernel.ledger.owners.identities.fresh .sourceBinding
                  context.withLocalBinding ⟨allocated.worker, allocated.serial⟩ .parameter
                      `nativeFieldInterface type fun context binding => do
                    next context bound (← asNativeMap binding.expression)
        let rec prepareOperands (remaining : List PreparedSymbolicOperand)
            (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
            (selections : SourceSelectionScope Expr)
            (operands : Array PublishedSource.NativeSymbolicOperand) : MetaM Unit := do
          match remaining with
          | [] => nextNode context bound selections operands
          | operand :: remaining =>
            let next := fun context bound selections operand =>
              prepareOperands remaining context bound selections (operands.push operand)
            match operand with
            | .value value =>
              if node.tag == "compose" || node.tag == "map" then
                withNativeInterface kernel.ledger.owners.identities graph context bound
                    selections value fun context bound selections expression => do
                  next context bound selections (.value (← asNativeMap expression))
              else
                withNative context bound value fun context bound expression =>
                  next context bound selections (.value expression)
            | .objectData value =>
              withEndpoint context bound value fun context bound endpoint => do
                next context bound selections (.objectData endpoint)
            | .mapData source target =>
              withEndpoint context bound source fun context bound source => do
                withEndpoint context bound target fun context bound target => do
                  next context bound selections (.mapData source target)
        prepareOperands node.operands.toList context bound selections #[]
    let rec prepareSlots (remaining : List ValueBinding) (context : OpenContext)
        (bound : Std.HashMap BindingId ValueBinding) (selections : SourceSelectionScope Expr)
        (sources : Array Expr) : MetaM Unit := do
      match remaining with
      | [] => prepareNodes nodes.toList 0 context bound selections sources #[]
      | value :: remaining =>
        withNative context bound value fun context bound source => do
          prepareSlots remaining context bound selections (sources.push source)
    let rec prepareContexts (remaining : List PreparedSymbolicNode) (context : OpenContext)
        (bound : Std.HashMap BindingId ValueBinding) : MetaM Unit := do
      match remaining with
      | [] => do
        let mut selections : SourceSelectionScope Expr := {}
        for node in nodes do
          selections ← SourceSelectionScope.merge selections
            (← node.environment.selections.inContext context)
          selections ← SourceSelectionScope.merge selections (← node.source.selections.inContext context)
        prepareSlots slots.toList context bound selections #[]
      | node :: remaining =>
        node.environment.withContext context bound fun context bound =>
          node.source.source.context.withInContext context fun context =>
            prepareContexts remaining context bound
    prepareContexts nodes.toList context bound




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
    invocation.domain invocation.target makeCallable path invocation.symbolic
    #[(invocation.arrow, invocation.source, invocation.target),
      (invocation.argument, invocation.domain, invocation.source)]
    (some (preparedSymbolicCheck kernel request transaction))
  return some codec



opaque PreparedPointInvocation.retained (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (original : PreparedRequest)
    (registration : Registration) (parameters : ValueContainer) (source target : ValueBinding)
    (packet : ValueContainer) (path : NativePointPath original.source)
    (captures : Array ValueBinding) : MetaM PreparedPointInvocation := do
  let .apply callable arguments _ := request.action
    | throwError "a returned map continuation requires its actual callable"
  unless arguments.size == 1 do
    throwError "a returned map requires its unchanged original point argument"
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
    withBindingContext graph context bound argument fun context bound => do
      let some selected ← argument.role.selected? context
        | throwStratum .noImplementation "the returned map requires an original source-prepared point"
      let some point := selected.pointOrigin
        | throwStratum .noImplementation "the returned map requires an original source-prepared point"
      let selections ← SourceSelectionScope.merge (← request.environment.selections.inContext context)
        (← argument.role.selections.inContext context)
      let domainSource := point.domain
      let domain ← request.environment.evaluateSource evaluateSource transaction request.program
        context bound domainSource selections
      let environment ← RuntimeEnvironment.captureBound request.environment.worker context bound
        (← transaction.view) (some request.environment) selections
      environment.checkDeclaredInput context (← transaction.view) domainSource domain
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
