module

public import CasRuntime.Scope
public import CasRuntime.PreparedRequest
public import CasRuntime.Closure

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Original packet data and fresh scope/input authorities for the actual receiving process. -/
structure EncodedInputs where
  values : Array Json
  slots : Array ValueBinding
  inputs : Array InputPosition

/-- A checked released descriptor for an original visible input. The ordinary value node and
its complete association chain remain the scope authority; this view creates no replacement
value or stored field. Only the declared source-specific producers below can create it. -/
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

/-- The exact root of a delayed registered named morphism has its released declaration packet.
The code must name that family at the empty native path, and its complete original input table
is admitted before any view is produced. Opaque arrows and projected code are left untouched. -/
opaque InputDescriptorView.namedMorphism? (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding) :
    MetaM (Option InputDescriptorView) := do
  let .ok _ := graph.requiredOwners #[binding]
    | throwError "the named arrow is outside its visible graph"
  let some node := graph.find binding.value
    | throwError "the named arrow has no visible original node"
  let .closure program captures := node.payload.data | return none
  let some (.family request path) := codes[program]? | return none
  unless path.isEmpty do return none
  let .primitive (.registered family) _ := request.action | return none
  let .morphism morphismId := family.source.reference | return none
  let some row := (← semanticState).morphisms.find? (·.id == morphismId)
    | throwError "the delayed named arrow lost its released declaration"
  unless family.source.declaration == row.declaration &&
      family.source.family.getAppFn.isConstOf row.declaration do
    throwError "the delayed named arrow changed its checked family"
  let complete ← request.source.source.withOpen fun _ source => do
    unless source.getAppFn.isConstOf row.declaration do
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
  let template := Json.mkObj [("ctor", toJson row.id.raw),
    ("args", .arr (Array.replicate parameters.size Json.null))]
  let .ok payload := ValuePayload.descriptor template slots
    | throwError "the named arrow has an invalid declared descriptor layout"
  let .container packet := payload.data
    | throwError "the declared descriptor lost its checked packet structure"
  return some ⟨binding, packet, some request, parameters,
    request.scope.push binding⟩

/-- Require the caller's released named family at an actual scoped arrow. This is an identity
check on its original prepared code; equal native endpoints cannot change the operation. -/
def InputDescriptorView.requireMorphism (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) (binding : ValueBinding)
    (expected : MorphismId) : MetaM InputDescriptorView := do
  let some descriptorView ← InputDescriptorView.namedMorphism? graph codes binding
    | throwStratum .malformed "the arrow is not its original complete released named family"
  let some family := descriptorView.family
    | throwError "the named-arrow descriptor lost its checked source family"
  unless family.reference == some (.morphism expected) do
    throwStratum .malformed "the supplied arrow belongs to a different released family"
  return descriptorView

/-- The public Arrow packet is a view of one actual native Arrow record. Its three supplied
fields must already be the exact stored or ordinarily demanded projections of that parent.
The complete native type is checked against Arrow.mk of its own hom field, so an unrelated
three-field Comma record cannot acquire this codec. No value or projection is staged here. -/
opaque InputDescriptorView.nativeArrow (graph : ValueGraph) (binding : ValueBinding)
    (values : Array ValueBinding) : MetaM InputDescriptorView := do
  let projections := #[``CategoryTheory.Comma.left, ``CategoryTheory.Comma.right,
    ``CategoryTheory.Comma.hom]
  let fields := binding.role.fields.filter (·.wireIndex.isSome)
  unless binding.role.kind == .record && fields.size == projections.size &&
      values.size == fields.size && fields.map (·.projection) == projections do
    throwError "the method receiver has no complete native Arrow field layout"
  let .ok _ := graph.requiredOwners (values.push binding)
    | throwError "the method arrow is outside its visible graph"
  binding.role.source.withOpen fun bindings expression => do
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
  else if let some descriptorView ← InputDescriptorView.namedMorphism? graph codes binding then
    views := views.push descriptorView
    children := descriptorView.slots.map (·.binding)
  else
    let some node := graph.find binding.value
      | throwError "a descriptor input is outside its visible graph"
    match node.payload.data with
    | .container value =>
      unless binding.role.kind == .function || value.callable.isSome do
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

/-- Prepare source-authorized descriptor views only within the actual requested stored inputs.
This neither forces a lazy field nor searches the graph for an equal source or payload. -/
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
  -- Public single-data-field collapse can put a field at its whole record's wire path.
  -- Keep the whole input authority; graph projection retains the field's independent role.
  if state.inputs.any (·.path == path) then state
  else { state with inputs := state.inputs.push { path, binding } }

private def scopeReference (state : EncodingState) (binding : ValueBinding) : Json × EncodingState :=
  ((ScopedReference.scope state.slots.size).encode,
    { state with slots := state.slots.push binding })

/-- Encode retained data rather than reconstructing it from source expressions.
Reference: CasContract.Port's computational wire grammar and ValueContainer.fill.
Whole callable wrappers stay references, preserving their independent stored interfaces. -/
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
    if binding.role.kind == .function || container.callable.isSome then
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
    return (← container.fill replacements, state)
  | .product fields =>
    unless binding.role.kind == .record &&
        (binding.role.fields.filter (·.wireIndex.isSome)).size == fields.size do
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

/-- Encode disjoint complete input roots for one actual consumer.
Reuse: graph visibility/owner traversal, the released JSON parser and packet encodings.
Each foreign occurrence gets its own scoped position, even when actual values alias.
Liveness belongs to the later atomic reservation/send check. -/
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

/-- Primitive scopes have no retained export capture prefix. -/
opaque ValueGraph.encodeInputs (graph : ValueGraph) (receiver : ConnectionGeneration)
    (roots : Array InputPosition) (views : Array InputDescriptorView := #[]) :
    Except String EncodedInputs :=
  encodeRoots graph receiver roots #[] views

/-- Reserve the actual native export's capture slots before encoding context arguments.
RequestScope.issue installs these same stored bindings, in order, without value deduplication.
Source: execution amendment #69, comment 6706802517; reuse ValueGraph.callable. -/
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

/-- The prepared interface of one role: its kind and its ordered computational fields. -/
private def layoutJson (layout : SourceLayout) : Json :=
  Json.mkObj [("kind", toJson (kindName layout.kind)),
    ("fields", .arr (layout.fields.filterMap fun field => field.wireIndex.map fun _ =>
      Json.mkObj [("name", toJson field.projection.toString), ("kind", toJson (kindName field.kind))]))]

/-- The dependent invocation context of execution contract v2 §4.1, for a published operation
and for a retained native export. Parameters and arguments keep their source order. -/
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

/-- Encode source-ordered arguments only after the entire declared input map is admitted.
Reuse: scoped role identities, native input checks and receiver-aware retained-data encoding. -/
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
