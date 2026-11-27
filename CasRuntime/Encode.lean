module

public import CasRuntime.Scope
public import CasRuntime.PreparedRequest
public import CasRuntime.Closure
public import CasRuntime.CategoricalPointPacket

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend


structure EncodedInputs where
  values : Array Json
  slots : Array ValueBinding
  inputs : Array InputPosition




structure InputDescriptorView where
  private mk ::
  binding : ValueBinding
  packet : ValueContainer
  family : Option PreparedRequest
  parameters : Array ValueBinding
  dependencies : Array ValueBinding

def InputDescriptorView.slots (descriptorView : InputDescriptorView) : Array ContainerSlot :=
  descriptorView.packet.slots

private def exactInput (left right : ValueBinding) : Bool :=
  left.value == right.value && left.associationIds == right.associationIds





opaque InputDescriptorView.namedPoint? (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding) :
    MetaM (Option InputDescriptorView) := do
  let .ok _ := graph.requiredOwners #[binding]
    | throwError "the named arrow is outside its visible graph"
  let some node := graph.find binding.value
    | throwError "the named arrow has no visible original node"
  let .closure program captures := node.payload.data | return none
  if let some (.formalLeg _ (some packet) _) := codes[program]? then
    unless packet.fields.isNone && packet.callable.isNone && packet.originalPacket.isNone do
      throwError "the formal leg changed its original inert named packet"
    let parameters := packet.slots.map (·.binding)
    for parameter in parameters do
      unless captures.any (exactInput parameter) do
        throwError "the formal leg lost an original named descriptor operand"
    discard <| IO.ofExcept <| (graph.requiredOwners parameters).mapError IO.userError
    return some ⟨binding, packet, none, parameters, captures.push binding⟩
  let some (.family request path) := codes[program]? | return none
  unless path.isEmpty do return none
  let .primitive boundary _ := request.action | return none
  if let .point family := boundary then
    unless !family.invocation && captures.size == request.scope.size &&
        (captures.zip request.scope).all (fun (left, right) => exactInput left right) do
      throwError "the categorical arrow changed its original delayed family or complete captures"
    let complete ← request.source.source.withOpen fun _ source => do
      return (← whnfR (← inferType source)).isAppOfArity ``Quiver.Hom 4
    unless complete do return none
    discard <| request.admitInputs graph
    let values := request.origin.application.map (·.arguments) |>.getD #[]
    let prepared ← CategoricalPointPacket.prepare family values
    let .container packet := prepared.arrow.data
      | throwError "the categorical arrow lost its checked complete declaration packet"
    let parameters := prepared.parameters.slots.map (·.binding)
    return some ⟨binding, packet, some request, parameters,
      (request.scope ++ parameters ++ packet.slots.map (·.binding)).push binding⟩
  let selected : Option (Name × String) ← match boundary with
    | .registered family => do
      let .morphism morphismId := family.source.reference | pure none
      let some row := (← semanticState).morphisms.find? (·.id == morphismId)
        | throwError "the delayed named arrow lost its released declaration"
      unless family.source.declaration == row.declaration &&
          family.source.family.consumeMData.getAppFn.isConstOf row.declaration do
        throwError "the delayed named arrow changed its checked family"
      pure (some (row.declaration, row.id.raw))
    | .application family => do
      let .application entry := family.owner
        | throwError "the object application lost its original owner kind"
      let #[row] := (← semanticState).objects.filter (·.id == entry.id)
        | throwError "the delayed object application lost its exact registered owner"
      unless row.application == some family.declaration && row.category == entry.category &&
          row.declaration == entry.declaration &&
          family.family.getAppFn.isConstOf family.declaration do
        throwError "the delayed object application changed its checked family"
      pure (some (family.declaration, family.operation))
    | _ => pure none
  let some (declaration, operation) := selected | return none
  let complete ← request.source.source.withOpen fun _ source => do
    unless source.getAppFn.consumeMData.isConstOf declaration do
      throwError "the named arrow changed its original complete source application"
    return (← whnfR (← inferType source)).isAppOfArity ``Quiver.Hom 4
  unless complete do return none
  unless captures.size == request.scope.size &&
      (captures.zip request.scope).all (fun (left, right) => exactInput left right) do
    throwError "the named arrow changed its original complete captures"
  discard <| request.admitInputs graph
  let mut parameters := #[]
  if let some application := request.application then
    let some original := request.origin.application
      | throwError "the named arrow lost its complete native argument table"
    for parameter in application.arguments do
      if parameter.wireIndex.isSome && parameter.binderInfo.isExplicit then
        let some value := original.arguments[parameter.sourceIndex]?.bind id
          | throwError "the named arrow is missing an original declared parameter"
        parameters := parameters.push value
  let slots := parameters.mapIdx fun index binding =>
    ({ path := #[.field "args", .index index], binding, fieldIndex := none } : ContainerSlot)
  let template := Json.mkObj [("ctor", toJson operation),
    ("args", .arr (Array.replicate parameters.size Json.null))]
  let .ok payload := ValuePayload.descriptor template slots
    | throwError "the named arrow has an invalid declared descriptor layout"
  let .container packet := payload.data
    | throwError "the declared descriptor lost its checked packet structure"
  return some ⟨binding, packet, some request, parameters,
    request.scope.push binding⟩


opaque InputDescriptorView.namedMorphism? (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding) :
    MetaM (Option InputDescriptorView) := do
  let some view ← InputDescriptorView.namedPoint? graph codes binding | return none
  let some family := view.family | return none
  match family.reference with
  | some (.morphism _) => pure (some view)
  | _ =>
    match family.action with
    | .primitive (.point selected) _ =>
      match selected.owner with | .named (.morphism _) => pure (some view) | _ => pure none
    | _ => pure none


opaque InputDescriptorView.namedApplication? (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding) :
    MetaM (Option InputDescriptorView) := do
  let some view ← InputDescriptorView.namedPoint? graph codes binding | return none
  let some family := view.family | return none
  match family.action with
  | .primitive (.application _) _ => pure (some view)
  | .primitive (.point selected) _ =>
    match selected.owner with | .named (.application _) => pure (some view) | _ => pure none
  | _ => pure none



def InputDescriptorView.requireMorphism (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding)
    (expected : MorphismId) : MetaM InputDescriptorView := do
  let some descriptorView ← InputDescriptorView.namedMorphism? graph codes binding
    | throwStratum .malformed "the arrow is not its original complete released named family"
  let some family := descriptorView.family
    | throwError "the named-arrow descriptor lost its checked source family"
  let actual := match family.action with
    | .primitive (.point selected) _ =>
      match selected.owner with | .named (.morphism entry) => some entry.id | _ => none
    | _ => family.reference.bind fun reference =>
        match reference with | .morphism id => some id | _ => none
  unless actual == some expected do
    throwStratum .malformed "the supplied arrow belongs to a different released family"
  return descriptorView



def InputDescriptorView.requireApplication (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding)
    (expected : ObjectId) : MetaM InputDescriptorView := do
  let some view ← InputDescriptorView.namedApplication? graph codes binding
    | throwStratum .malformed "the arrow is not its original complete released object application"
  let some request := view.family | throwError "the application descriptor lost its checked family"
  let owner := match request.action with
    | .primitive (.application family) _ =>
      match family.owner with | .application entry => some entry.id | _ => none
    | .primitive (.point family) _ =>
      match family.owner with | .named (.application entry) => some entry.id | _ => none
    | _ => none
  unless owner == some expected do
    throwStratum .malformed "the supplied arrow belongs to a different released object application"
  return view


def InputDescriptorView.requireCategorical (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding)
    (expected : CategoricalPointFamily) : MetaM InputDescriptorView := do
  match expected.owner with
  | .named (.morphism entry) => return ← requireMorphism graph codes binding entry.id
  | .named (.application entry) => return ← requireApplication graph codes binding entry.id
  | _ => pure ()
  let some view ← InputDescriptorView.namedPoint? graph codes binding
    | throwStratum .malformed "the arrow is not its original complete categorical family"
  let some request := view.family | throwError "the categorical descriptor lost its source family"
  let .primitive (.point family) _ := request.action
    | throwStratum .malformed "the arrow has another original source boundary"
  unless !family.invocation && family.operation == expected.operation &&
      family.declaration == expected.declaration do
    throwStratum .malformed "the supplied arrow belongs to a different categorical owner"
  return view





opaque InputDescriptorView.nativeArrow (graph : ValueGraph) (binding : ValueBinding)
    (values : Array ValueBinding) : MetaM InputDescriptorView := do
  let projections := #[``CategoryTheory.Comma.left, ``CategoryTheory.Comma.right,
    ``CategoryTheory.Comma.hom]
  let native := binding.nativeRole
  let fields := native.fields.filter (·.wireIndex.isSome)
  unless native.kind == .record && fields.size == projections.size &&
      values.size == fields.size && fields.map (·.projection) == projections do
    throwError "the method receiver has no complete native Arrow field layout"
  let .ok _ := graph.requiredOwners (values.push binding)
    | throwError "the method arrow is outside its visible graph"
  native.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let some hom := fields[2]? | throwError "the native Arrow lost its hom field"
    let selected ← hom.source.inContext context
    let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[selected]
    unless ← isDefEq (← inferType expression) (← inferType arrow) do
      throwError "the selected method receiver is a different complete native record"
  let some node := graph.find binding.value
    | throwError "the native Arrow lost its visible original node"
  for (field, value) in fields.zip values do
    let some wireIndex := field.wireIndex
      | throwError "the native Arrow field lost its computational position"
    if node.payload.data.storedFields?.isSome then
      let original ← IO.ofExcept <| (graph.project binding wireIndex).mapError IO.userError
      unless original.value == value.value &&
          original.associationIds.toList.isPrefixOf value.associationIds.toList do
        throwError "the method arrow changed an actual stored field"
    else
      let .ok (some _) := graph.projectionBasis value binding #[field.projection]
        | throwError "the method arrow field has no exact original projection access"
  let slots := values.mapIdx fun index value =>
    ({ path := #[.field "args", .index index], binding := value, fieldIndex := none } : ContainerSlot)
  let template := Json.mkObj [("ctor", toJson "arrow"),
    ("args", .arr (Array.replicate values.size Json.null))]
  let .ok payload := ValuePayload.descriptor template slots
    | throwError "the method arrow has an invalid public descriptor layout"
  let .container packet := payload.data
    | throwError "the native Arrow view lost its checked descriptor structure"
  return ⟨binding, packet, none, values, values.push binding⟩

private partial def collectDescriptorViews (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding)
    (seen : Array ValueBinding) (views : Array InputDescriptorView) :
    MetaM (Array ValueBinding × Array InputDescriptorView) := do
  if seen.any (exactInput binding) then return (seen, views)
  let mut seen := seen.push binding
  let mut views := views
  let mut children := #[]
  if let some descriptorView := views.find? (fun descriptorView =>
      exactInput descriptorView.binding binding) then
    children := descriptorView.slots.map (·.binding)
  else if let some descriptorView ← InputDescriptorView.namedPoint? graph codes binding then
    views := views.push descriptorView
    children := descriptorView.slots.map (·.binding)
  else
    let some node := graph.find binding.value
      | throwError "a descriptor input is outside its visible graph"
    match node.payload.data with
    | .container value =>
      unless (binding.nativeRole.kind == .function || value.callable.isSome) && !value.callableData do
        for slot in value.slots do
          let child ← match slot.fieldIndex with
            | none => pure slot.binding
            | some index => IO.ofExcept <| (graph.project binding index).mapError IO.userError
          children := children.push child
    | .product fields =>
      for index in [:fields.size] do
        children := children.push (← IO.ofExcept <|
          (graph.project binding index).mapError IO.userError)
    | .portable _ | .closure .. | .ownedToken .. => pure ()
  for child in children do
    let (nextSeen, nextViews) ← collectDescriptorViews graph codes child seen views
    seen := nextSeen
    views := nextViews
  return (seen, views)



def InputDescriptorView.collect (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (roots : Array ValueBinding)
    (prepared : Array InputDescriptorView := #[]) :
    MetaM (Array InputDescriptorView) := do
  let mut seen := #[]
  let mut views := prepared
  for root in roots do
    let (nextSeen, nextViews) ← collectDescriptorViews graph codes root seen views
    seen := nextSeen
    views := nextViews
  return views

private structure EncodingState where
  slots : Array ValueBinding := #[]
  inputs : Array InputPosition := #[]

private def addInput (state : EncodingState) (path : Array InputPathStep)
    (binding : ValueBinding) : EncodingState :=


  if state.inputs.any (·.path == path) then state
  else { state with inputs := state.inputs.push { path, binding } }

private def scopeReference (state : EncodingState) (binding : ValueBinding) : Json × EncodingState :=
  ((ScopedReference.scope state.slots.size).encode,
    { state with slots := state.slots.push binding })




private partial def encodeAt (graph : ValueGraph) (receiver : ConnectionGeneration)
    (binding : ValueBinding) (path : Array InputPathStep) (state : EncodingState)
    (views : Array InputDescriptorView) :
    Except String (Json × EncodingState) := do
  let some node := graph.find binding.value | throw "the encoded input is outside the visible graph"
  let state := addInput state path binding
  if let some descriptorView := views.find? (fun descriptorView =>
      exactInput descriptorView.binding binding) then
    discard <| graph.requiredOwners descriptorView.dependencies
    let mut replacements := #[]
    let mut state := state
    for slot in descriptorView.slots do
      let (value, next) ← encodeAt graph receiver slot.binding (path ++ slot.path) state views
      replacements := replacements.push value
      state := next
    return (← descriptorView.packet.fill replacements, state)
  match node.payload.data with
  | .portable bytes =>
    let some text := String.fromUTF8? bytes | throw "the portable input is not UTF-8 packet data"
    let packet ← Json.parse text
    checkLiteral packet
    return (packet, state)
  | .ownedToken owner token _ =>
    if token.isEmpty then throw "the native input has an empty local token"
    if owner == receiver then return ((ComputationalValue.opaque token).encode, state)
    return scopeReference state binding
  | .closure .. => return scopeReference state binding
  | .container container =>
    if container.packetExports.any (·.owner != receiver) then
      return scopeReference state binding
    if (binding.nativeRole.kind == .function || container.callable.isSome) && !container.callableData then
      return scopeReference state binding
    let mut replacements : Array Json := #[]
    let mut state := state
    for slot in container.slots do
      let actual ← match slot.fieldIndex with
        | none => pure slot.binding
        | some index => graph.project binding index
      let (packet, next) ← encodeAt graph receiver actual (path ++ slot.path) state views
      replacements := replacements.push packet
      state := next
    return (← container.fillForOwner receiver replacements, state)
  | .product fields =>
    unless binding.nativeRole.kind == .record &&
        (binding.nativeRole.fields.filter (·.wireIndex.isSome)).size == fields.size do
      throw "the stored product does not match its complete source data-field interface"
    let mut packets : Array Json := #[]
    let mut state := state
    for index in [:fields.size] do
      let field ← graph.project binding index
      let fieldPath := if fields.size == 1 then path else path.push (.index index)
      let (packet, next) ← encodeAt graph receiver field fieldPath state views
      packets := packets.push packet
      state := next
    if let #[packet] := packets then return (packet, state)
    return (.arr packets, state)





private def encodeRoots (graph : ValueGraph) (receiver : ConnectionGeneration)
    (roots : Array InputPosition) (captures : Array ValueBinding)
    (views : Array InputDescriptorView := #[]) : Except String EncodedInputs := do
  unless receiver.worker == graph.worker do throw "the input receiver belongs to a different worker"
  discard <| graph.requiredOwners (captures ++ roots.map (·.binding))
  let mut paths : Array (List InputPathStep) := #[]
  for root in roots do
    let path := root.path.toList
    if paths.any (fun previous => previous.isPrefixOf path || path.isPrefixOf previous) then
      throw "complete encoded input roots overlap"
    paths := paths.push path
  let mut state : EncodingState := { slots := captures }
  let mut values := #[]
  for root in roots do
    let (packet, next) ← encodeAt graph receiver root.binding root.path state views
    values := values.push packet
    state := next
  return ⟨values, state.slots.extract captures.size state.slots.size, state.inputs⟩


opaque ValueGraph.encodeInputs (graph : ValueGraph) (receiver : ConnectionGeneration)
    (roots : Array InputPosition) (views : Array InputDescriptorView := #[]) :
    Except String EncodedInputs :=
  encodeRoots graph receiver roots #[] views




opaque ValueGraph.encodeExportInputs (graph : ValueGraph) (receiver : ConnectionGeneration)
    (callable : ValueBinding) (roots : Array InputPosition) : Except String EncodedInputs := do
  let code ← graph.callable callable
  let some node := graph.find code.value | throw "the native code is outside the encoding graph"
  let .ownedToken owner _ captures := node.payload.data
    | throw "the callable has no native export capture table"
  unless owner == receiver do throw "the native export receiver is not its actual owner"
  encodeRoots graph receiver roots captures

private def kindName : ComputationalKind → String
  | .proof => "proof"
  | .typeValue => "type"
  | .function => "function"
  | .record => "record"
  | .data => "data"


private def layoutJson (layout : SourceLayout) : Json :=
  Json.mkObj [("kind", toJson (kindName layout.kind)),
    ("fields", .arr (layout.fields.filterMap fun field => field.wireIndex.map fun _ =>
      Json.mkObj [("name", toJson field.projection.toString), ("kind", toJson (kindName field.kind))]))]



def dependentContext (role : String) (parameters : Array Json)
    (bindings : Array (Nat × Json)) (arguments : Array Json)
    (argumentLayouts : Array SourceLayout) (result : SourceLayout) : Json :=
  Json.mkObj [("kind", "dependent"), ("prepared_role", toJson role),
    ("parameters", .arr parameters), ("bindings", .arr (bindings.map fun (slot, value) =>
      Json.mkObj [("slot", toJson slot), ("value", value)])), ("arguments", .arr arguments),
    ("argument_layouts", .arr (argumentLayouts.map layoutJson)),
    ("result_layout", layoutJson result)]

def argumentLayouts (request : PreparedRequest) : Array SourceLayout :=
  match request.application with
  | none => #[]
  | some application => application.arguments.filterMap fun argument =>
      argument.wireIndex.map fun _ => argument.source

open Lean Meta



opaque PreparedRequest.encodeArguments (request : PreparedRequest) (graph : ValueGraph)
    (receiver : ConnectionGeneration) (path : Array InputPathStep) :
    Lean.MetaM (InputRoleMap × EncodedInputs) := do
  let admitted ← request.admitInputs graph
  let arguments ← IO.ofExcept <| (admitted.arguments graph).mapError IO.userError
  let roots := arguments.mapIdx fun index binding => ({ path := path.push (.index index), binding } : InputPosition)
  let encoding : Except String EncodedInputs := do
    match request.action with
    | .apply callable .. =>
      let code ← graph.callable callable
      let some node := graph.find code.value | throw "the callable is outside the encoding graph"
      match node.payload.data with
      | .ownedToken .. => graph.encodeExportInputs receiver callable roots
      | .closure .. => graph.encodeInputs receiver roots
      | _ => throw "the retained callable has no code or native token"
    | _ => graph.encodeInputs receiver roots
  let encoded ← IO.ofExcept <| encoding.mapError IO.userError
  return (admitted, encoded)

end CasRuntime
