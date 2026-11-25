module

public import CasRuntime.PreparedRequest
public import CasRuntime.Reply
public import CasRuntime.Transaction
public import CasRuntime.Literal
public import CasRuntime.Association
public import CasRuntime.FixedInput
public import CasRuntime.FixedValue
public import CasRuntime.ConstructorPorts
public import CasRuntime.NativeMapEndpoints

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue.Backend

/-- The released complete record packet, including single-data-field collapse. -/
private def recordReplyPositions (count : Nat) (value : Json) :
    MetaM (Array (Array InputPathStep × Json)) := do
  if count == 1 then return #[(#[], value)]
  let .ok values := value.getArr?
    | throwError "the reply record requires its complete ordered data fields"
  unless values.size == count do
    throwError "the reply record has a different prepared data-field arity"
  return values.mapIdx fun index value => (#[.index index], value)

/-- Resolve fixed source inputs before taking an isolated draft. Inline positions follow the
same record/envelope grammar as materialization; references reuse stored-field preflight.
Reuse: resolveFixedResults, fixedInputFor and prepared native result projection paths. -/
private partial def preflightFixedResults (reply : ImmediateReply) (request : PreparedRequest)
    (transaction : CellTransaction) (resolve : Option (FixedInput → MetaM ValueBinding))
    (source : SourceLayout) (value : Json) (path : Array InputPathStep)
    (descendRecord : Bool := true) : MetaM (Array FixedResult) := do
  if let some reference := reply.references.find? (·.path == path) then
    return ← request.resolveFixedResults transaction source reference.binding resolve
  let graph ← liftM (m := IO) transaction.view
  if let some input ← request.fixedInputFor graph source then
    let value ← input.resolveValue (liftM (m := IO) transaction.view) resolve
    return #[{ path := ← request.source.projectionPathTo source, input, value }]
  let tag := (value.getObjValAs? String "ctor").toOption
  if tag == some "valueData" || tag == some "opaqueData" then
    let .ok envelope := ComputationalValue.decode value
      | throwError "the parsed reply lost its computational value envelope"
    match envelope with
    | .inline data =>
      return ← preflightFixedResults reply request transaction resolve source data
        (path ++ #[.field "args", .index 0]) descendRecord
    | .opaque _ => return #[]
  if source.kind != .record || !descendRecord then return #[]
  if tag == some "typedMap" then
    let map ← IO.ofExcept <| (TypedMap.decode value).mapError IO.userError
    return ← preflightFixedResults reply request transaction resolve source map.callable
      (path ++ #[.field "args", .index 2])
  let layout ← RecordLayout.ofSource source
  let fields := layout.fields.filter (·.field.wireIndex.isSome)
  let positions ← recordReplyPositions fields.size value
  let mut fixed := #[]
  for prepared in fields, position in positions do
    fixed := fixed ++ (← preflightFixedResults reply request transaction resolve prepared.layout
      position.2 (path ++ position.1))
  return fixed

/-- Original packet positions are joined only by an explicit callable relationship.
Equal packets never select an existing value or a different native endpoint. -/
private structure CallableEndpoint where
  parent : Nat
  binding : Option ValueBinding := none
  packet : Option (Json × Array InputPathStep) := none

private structure CallableFiniteCheck where
  value : Json
  path : Array InputPathStep
  source : Nat
  target : Nat
  structured : Bool

private structure CallableTree where
  endpoints : Array CallableEndpoint := #[]
  nodes : Array PreparedSymbolicNode := #[]
  finite : Array CallableFiniteCheck := #[]

private structure CallableFrame where
  native : SourceLayout
  environment : RuntimeEnvironment
  marks : Array ValueBinding := #[]
  operands : Array PreparedMapOperand := #[]
  fieldPrefix : Option NativeFieldPrefix := none
  /-- Structured maps require their actual source object's supplied inventory. -/
  structured : Bool := false

private def callableRoot (tree : CallableTree) (index : Nat) : Except String Nat := do
  let mut current := index
  for _ in [:tree.endpoints.size] do
    let some endpoint := tree.endpoints[current]?
      | throw "a callable endpoint is outside its original packet namespace"
    if endpoint.parent == current then return current
    current := endpoint.parent
  throw "the callable endpoint relationships contain a cycle"

private def newCallableEndpoint (tree : IO.Ref CallableTree)
    (binding : Option ValueBinding := none)
    (packet : Option (Json × Array InputPathStep) := none) : MetaM Nat := do
  let previous ← tree.get
  let index := previous.endpoints.size
  tree.set { previous with endpoints := previous.endpoints.push ⟨index, binding, packet⟩ }
  return index

private partial def unwrapCallable (value : Json) (path : Array InputPathStep) :
    MetaM (Json × Array InputPathStep) := do
  if (value.getObjValAs? String "ctor").toOption != some "valueData" then return (value, path)
  IO.ofExcept <| (checkServiceFields #["ctor", "args"] value).mapError IO.userError
  let .ok (.inline inner) := ComputationalValue.decode value
    | throwError "the callable lost its complete original inline envelope"
  unwrapCallable inner (path ++ #[.field "args", .index 0])

private def requireCallableEndpoint (reply : ImmediateReply) (graph : ValueGraph)
    (connection : Connection) (expected : ValueBinding)
    (value : Json) (path : Array InputPathStep) : MetaM Unit := do
  let (value, path) ← unwrapCallable value path
  if let some reference := reply.references.find? (·.path == path) then
    discard <| IO.ofExcept <| (graph.requiredOwners #[expected, reference.binding]).mapError IO.userError
    unless reference.binding.value == expected.value &&
        reference.binding.associationIds == expected.associationIds do
      throwError "the map changed its exact original endpoint occurrence"
    return
  unless ← IO.ofExcept <|
      (reply.retainsValue graph connection value path expected).mapError IO.userError do
    throwError "the map changed its independently retained complete endpoint data"

/-- Compare two explicitly corresponding endpoint positions. References preserve exact
node/view identity even when their portable data happen to be equal. A literal counterpart
is checked only after the original referenced endpoint has already been selected. -/
private partial def sameCallableEndpointPacket (reply : ImmediateReply) (graph : ValueGraph)
    (connection : Connection) (first : Json) (firstPath : Array InputPathStep)
    (second : Json) (secondPath : Array InputPathStep) : MetaM Unit := do
  let (first, firstPath) ← unwrapCallable first firstPath
  let (second, secondPath) ← unwrapCallable second secondPath
  if let some original := reply.references.find? (·.path == firstPath) then
    requireCallableEndpoint reply graph connection original.binding second secondPath
    return
  if let some original := reply.references.find? (·.path == secondPath) then
    requireCallableEndpoint reply graph connection original.binding first firstPath
    return
  if (first.getObjValAs? String "ctor").toOption == some "opaqueData" ||
      (second.getObjValAs? String "ctor").toOption == some "opaqueData" then
    let firstOriginal ← IO.ofExcept <| (reply.fragmentAt firstPath).mapError IO.userError
    let secondOriginal ← IO.ofExcept <| (reply.fragmentAt secondPath).mapError IO.userError
    unless firstOriginal == first && secondOriginal == second do
      throwError "the symbolic endpoint changed its original reply fragment"
    let firstPacket ← IO.ofExcept <|
      (reply.packetDescriptor graph connection firstPath).mapError IO.userError
    let secondPacket ← IO.ofExcept <|
      (reply.packetDescriptor graph connection secondPath).mapError IO.userError
    let #[firstExport] := firstPacket.exports
      | throwError "the symbolic maps lost an original opaque endpoint occurrence"
    let #[secondExport] := secondPacket.exports
      | throwError "the symbolic maps lost an original opaque endpoint occurrence"
    unless firstExport.path.isEmpty && secondExport.path.isEmpty &&
        firstExport.originScope == secondExport.originScope &&
        firstExport.originPath == secondExport.originPath &&
        firstExport.owner == secondExport.owner && firstExport.token == secondExport.token &&
        firstExport.captures.size == secondExport.captures.size &&
        ((firstExport.captures.zip secondExport.captures).all fun (first, second) =>
          first.value == second.value && first.associationIds == second.associationIds) do
      throwError "the symbolic maps joined distinct original opaque endpoint occurrences"
    return
  match first, second with
  | .arr first, .arr second =>
    unless first.size == second.size do
      throwError "the symbolic maps changed their complete endpoint array"
    for firstValue in first, secondValue in second, index in [:first.size] do
      sameCallableEndpointPacket reply graph connection firstValue (firstPath.push (.index index))
        secondValue (secondPath.push (.index index))
  | .obj first, .obj second =>
    unless first.toList.length == second.toList.length do
      throwError "the symbolic maps changed their complete endpoint object"
    for (name, first) in first.toList do
      let second ← IO.ofExcept <| ((Json.obj second).getObjVal? name).mapError IO.userError
      sameCallableEndpointPacket reply graph connection first (firstPath.push (.field name))
        second (secondPath.push (.field name))
  | _, _ =>
    unless first == second do throwError "the symbolic maps changed their explicit shared endpoint"

private def joinCallableEndpoints (reply : ImmediateReply) (graph : ValueGraph)
    (connection : Connection) (tree : IO.Ref CallableTree) (left right : Nat) : MetaM Unit := do
  let previous ← tree.get
  let left ← IO.ofExcept <| (callableRoot previous left).mapError IO.userError
  let right ← IO.ofExcept <| (callableRoot previous right).mapError IO.userError
  if left == right then return
  let some first := previous.endpoints[left]?
    | throwError "the first callable endpoint disappeared"
  let some second := previous.endpoints[right]?
    | throwError "the second callable endpoint disappeared"
  match first.binding, second.binding with
  | some first, some second =>
    unless first.value == second.value && first.associationIds == second.associationIds do
      throwError "the symbolic maps joined different retained endpoint occurrences"
  | some expected, none =>
    if let some (value, path) := second.packet then
      requireCallableEndpoint reply graph connection expected value path
  | none, some expected =>
    if let some (value, path) := first.packet then
      requireCallableEndpoint reply graph connection expected value path
  | none, none =>
    if let some (first, firstPath) := first.packet then
      if let some (second, secondPath) := second.packet then
        sameCallableEndpointPacket reply graph connection first firstPath second secondPath
  let retained := { first with
    binding := first.binding.orElse (fun _ => second.binding)
    packet := first.packet.orElse (fun _ => second.packet) }
  let endpoints := previous.endpoints.set! left retained |>.set! right { second with parent := left }
  tree.set { previous with endpoints }

private def packetCallableEndpoint (reply : ImmediateReply) (tree : IO.Ref CallableTree)
    (value : Json) (path : Array InputPathStep) : MetaM Nat := do
  let (value, path) ← unwrapCallable value path
  let binding := (reply.references.find? (·.path == path)).map (·.binding)
  newCallableEndpoint tree binding (some (value, path))

private def callableEndpointInventoryAt (reply : ImmediateReply) (graph : ValueGraph)
    (tree : IO.Ref CallableTree) (position : Nat) :
    MetaM (Option (Array CallableDatum)) := do
  let tree ← tree.get
  let position ← IO.ofExcept <| (callableRoot tree position).mapError IO.userError
  let some endpoint := tree.endpoints[position]?
    | throwError "the callable inventory lost its original endpoint position"
  let datum ← match endpoint.binding, endpoint.packet with
    | some binding, _ =>
      pure (some (← IO.ofExcept <| (graph.callableDatum binding).mapError IO.userError))
    | none, some (value, path) =>
      pure (some (← IO.ofExcept <| (reply.callableDatum graph value path).mapError IO.userError))
    | none, none => pure none
  match datum with
  | none => pure none
  | some datum => IO.ofExcept <| datum.endpointInventory.mapError IO.userError

private def readCallableEndpoint (tree : CallableTree)
    (endpoint : PreparedSymbolicEndpoint) : MetaM PreparedSymbolicEndpoint := do
  let .inline position := endpoint | return endpoint
  let position ← IO.ofExcept <| (callableRoot tree position).mapError IO.userError
  let some endpoint := tree.endpoints[position]?
    | throwError "the symbolic callable lost an original endpoint position"
  return endpoint.binding.map PreparedSymbolicEndpoint.value |>.getD (.inline position)

/-- A composition may expose the middle endpoint's inventory after its first graph was
parsed. Recheck every finite packet against the final explicit endpoint relationships. -/
private def checkFiniteCallableTree (reply : ImmediateReply) (tree : IO.Ref CallableTree)
    (graph : ValueGraph) : MetaM Unit := do
  for retained in (← tree.get).finite do
    let domain ← callableEndpointInventoryAt reply graph tree retained.source
    let target ← callableEndpointInventoryAt reply graph tree retained.target
    if retained.structured && domain.isNone then
      throwError "a structured finite map lost its actual source inventory"
    discard <| IO.ofExcept <| (CallablePacket.finiteWith retained.value domain target
      fun value relative => reply.callableDatum graph value (retained.path ++ relative)).mapError IO.userError

/-- One source check sees the complete tree, including nested action routes, and the final
isolated draft graph. No partial symbolic subtree is independently installed or trusted. -/
private def checkCallableTree (tree : IO.Ref CallableTree) (graph : ValueGraph)
    (check : Option PreparedSymbolicCheck) : MetaM Unit := do
  let tree ← tree.get
  if tree.nodes.isEmpty then return
  let some check := check
    | CasCatalogue.throwStratum .noImplementation
        "the symbolic callable requires its independently prepared native interface checker"
  let nodes ← tree.nodes.mapM fun node => do
    let operands ← node.operands.mapM fun operand => do
      match operand with
      | .value value => pure (.value value)
      | .objectData endpoint => return .objectData (← readCallableEndpoint tree endpoint)
      | .mapData source target =>
        return .mapData (← readCallableEndpoint tree source) (← readCallableEndpoint tree target)
    let framedSource ← readCallableEndpoint tree node.framed.1
    let framedTarget ← readCallableEndpoint tree node.framed.2
    return { node with operands := operands, framed := (framedSource, framedTarget) }
  check graph nodes

private def callableReferenceEndpoints (request : PreparedRequest) (frame : CallableFrame)
    (supply : IdentitySupply) (binding : ValueBinding) (draft : CellDraft) :
    MetaM (CellDraft × ValueBinding × ValueBinding) := do
  if let some original := frame.operands.find? (fun original =>
      original.binding.value == binding.value &&
        original.binding.associationIds == binding.associationIds) then
    return (draft, original.source, original.target)
  let some node := draft.view.find binding.value
    | throwError "a symbolic map operand is outside its actual draft graph"
  let environment ← frame.environment.withSourceMarks binding.sourceMarks (some draft.view)
  let environment ← environment.withSourceMarks node.origin.sourceMarks (some draft.view)
  let (draft, prepared) ← PreparedMapResult.fromNative request environment binding.role supply
    draft frame.marks
  return (draft, prepared.source, prepared.target)

/-- Parse only released callable framing. The tree retains original scoped operands and
typed endpoint positions; finite tables and symbolic maps are never applied here. -/
private partial def collectCallable (reply : ImmediateReply) (request : PreparedRequest)
    (connection : Connection) (supply : IdentitySupply) (frame : CallableFrame)
    (tree : IO.Ref CallableTree) (value : Json) (path : Array InputPathStep)
    (framed : Option (Nat × Nat)) (inputActions : Array ValueContainer)
    (draft : CellDraft) (current : Option (SourceLayout × Option NativeFieldPrefix) := none) :
    MetaM (CellDraft × CallablePacket × Nat × Nat × Option ValueBinding) := do
  if let some reference := reply.references.find? (·.path == path) then
    if reference.binding.role.kind == .function then
      if let some (current, nativePrefix) := current then
        let retained ← match nativePrefix with
          | some nativePrefix => do
            let candidate ← nativePrefix.checkResult frame.environment draft.view reference.binding
            pure candidate.root
          | none => do
            let candidate ← frame.environment.checkResult draft.view current reference.binding
            pure candidate.root
        let (source, target) ← match framed with
          | some endpoints => pure endpoints
          | none => do
            let source ← newCallableEndpoint tree
            let target ← newCallableEndpoint tree
            pure (source, target)
        let packet ← IO.ofExcept <| (CallablePacket.retained value).mapError IO.userError
        return (draft, packet, source, target, some retained)
    let (draft, source, target) ← callableReferenceEndpoints request frame supply reference.binding draft
    let source ← newCallableEndpoint tree (some source)
    let target ← newCallableEndpoint tree (some target)
    if let some (expectedSource, expectedTarget) := framed then
      joinCallableEndpoints reply draft.view connection tree source expectedSource
      joinCallableEndpoints reply draft.view connection tree target expectedTarget
    let packet ← IO.ofExcept <| (CallablePacket.retained value).mapError IO.userError
    return (draft, packet, source, target, some reference.binding)
  let tag := (value.getObjValAs? String "ctor").toOption
  if tag == some "valueData" then
    let .ok (.inline inner) := ComputationalValue.decode value
      | throwError "a callable lost its actual inline data"
    let (draft, packet, source, target, retained) ← collectCallable reply request connection supply
      frame tree inner (path ++ #[.field "args", .index 0]) framed inputActions draft current
    return (draft, ← IO.ofExcept <| (packet.inline value).mapError IO.userError,
      source, target, retained)
  if tag == some "typedMap" then
    IO.ofExcept <| (checkServiceFields #["ctor", "args"] value).mapError IO.userError
    let map ← IO.ofExcept <| (TypedMap.decode value).mapError IO.userError
    let source ← packetCallableEndpoint reply tree map.source (path ++ #[.field "args", .index 0])
    let target ← packetCallableEndpoint reply tree map.target (path ++ #[.field "args", .index 1])
    if let some (expectedSource, expectedTarget) := framed then
      joinCallableEndpoints reply draft.view connection tree source expectedSource
      joinCallableEndpoints reply draft.view connection tree target expectedTarget
    let (draft, packet, _, _, retained) ← collectCallable reply request connection supply
      { frame with structured := true } tree map.callable (path ++ #[.field "args", .index 2])
      (some (source, target)) inputActions draft current
    return (draft, ← IO.ofExcept <| (packet.withMap value).mapError IO.userError,
      source, target, retained)
  let (source, target) ← match framed with
    | some pair => pure pair
    | none => do
      let source ← newCallableEndpoint tree
      let target ← newCallableEndpoint tree
      pure (source, target)
  if tag == some "opaqueData" then
    discard <| IO.ofExcept <| (reply.packetDescriptor draft.view connection path).mapError IO.userError
    let packet ← IO.ofExcept <| (CallablePacket.retained value).mapError IO.userError
    return (draft, packet, source, target, none)
  if tag == some "finiteGraph" || (match value with | .arr _ => true | _ => false) then
    let domain ← callableEndpointInventoryAt reply draft.view tree source
    let targetInventory ← callableEndpointInventoryAt reply draft.view tree target
    if frame.structured && domain.isNone then
      throwError "a structured finite map requires its actual selected source inventory"
    let packet ← IO.ofExcept <| (CallablePacket.finiteWith value domain targetInventory
      fun value relative => reply.callableDatum draft.view value (path ++ relative)).mapError IO.userError
    tree.modify fun tree => { tree with
      finite := tree.finite.push ⟨value, path, source, target, frame.structured⟩ }
    return (draft, packet, source, target, none)
  let packet ← IO.ofExcept <| (CallablePacket.symbolic value).mapError IO.userError
  let tag ← IO.ofExcept <| (value.getObjValAs? String "ctor").mapError IO.userError
  let args ← IO.ofExcept <| (value.getObjValAs? (Array Json) "args").mapError IO.userError
  let mut draft := draft
  let mut operands : Array PreparedSymbolicOperand := #[]
  let mut action : Option ValueContainer := none
  if tag == "identity" || tag == "zero" then
    let #[sourceValue, targetValue] := args
      | throwError "the symbolic map lost its two complete endpoints"
    let actualSource ← packetCallableEndpoint reply tree sourceValue (path ++ #[.field "args", .index 0])
    let actualTarget ← packetCallableEndpoint reply tree targetValue (path ++ #[.field "args", .index 1])
    joinCallableEndpoints reply draft.view connection tree source actualSource
    joinCallableEndpoints reply draft.view connection tree target actualTarget
    if tag == "identity" then
      joinCallableEndpoints reply draft.view connection tree source target
      operands := #[.objectData (.inline source)]
    else operands := #[.objectData (.inline source), .objectData (.inline target)]
  else if tag == "compose" then
    let #[first, second] := args
      | throwError "composition lost one of its complete original maps"
    let middle ← newCallableEndpoint tree
    let (next, _, firstSource, firstTarget, firstValue) ← collectCallable reply request connection supply
      { frame with structured := true } tree first (path ++ #[.field "args", .index 0])
      (some (source, middle)) inputActions draft
    draft := next
    let (next, _, secondSource, secondTarget, secondValue) ← collectCallable reply request connection supply
      { frame with structured := true } tree second (path ++ #[.field "args", .index 1])
      (some (middle, target)) inputActions draft
    draft := next
    operands := #[
      firstValue.map PreparedSymbolicOperand.value |>.getD
        (.mapData (.inline firstSource) (.inline firstTarget)),
      secondValue.map PreparedSymbolicOperand.value |>.getD
        (.mapData (.inline secondSource) (.inline secondTarget))]
  else if tag == "map" then
    let #[descriptor, arrow] := args
      | throwError "a symbolic action lost its complete action and original arrow"
    let descriptorPath := path ++ #[.field "args", .index 0]
    unless (← IO.ofExcept <| (reply.fragmentAt descriptorPath).mapError IO.userError) == descriptor do
      throwError "the symbolic action changed its original descriptor position"
    let descriptor ← IO.ofExcept <|
      (reply.packetDescriptor draft.view connection descriptorPath).mapError IO.userError
    let (next, _, arrowSource, arrowTarget, arrowValue) ← collectCallable reply request connection supply
      { frame with structured := true } tree arrow (path ++ #[.field "args", .index 1])
      none (inputActions.push descriptor) draft
    draft := next
    operands := #[arrowValue.map PreparedSymbolicOperand.value |>.getD
      (.mapData (.inline arrowSource) (.inline arrowTarget))]
    action := some descriptor
  else
    action := some (← IO.ofExcept <|
      (reply.packetDescriptor draft.view connection path).mapError IO.userError)
  tree.modify fun tree => { tree with nodes := tree.nodes.push {
    source := frame.native, environment := frame.environment,
    tag := tag, operands := operands, action := action,
    framed := (.inline source, .inline target), inputActions := inputActions,
    fieldPrefix := frame.fieldPrefix } }
  return (draft, packet, source, target, none)

private def stageNativeResult (source : SourceLayout) (environment : RuntimeEnvironment)
    (origin : ValueOrigin) (draft : CellDraft) (payload : ValuePayload)
    (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM (CellDraft × ValueBinding) := do
  let (draft, binding) ← liftM (m := IO) <| draft.stage origin payload
  let binding ← match fieldPrefix with
    | some nativePrefix => do
      let candidate ← nativePrefix.checkResult environment draft.view binding
      pure candidate.root
    | none => do
      let candidate ← environment.checkResult draft.view source binding
      pure candidate.root
  return (draft, binding)

/-- Native slots replace only their own packet subtree. Endpoint and parameter references
outside those slots remain exact original references, including their owning exports. -/
private def completeNativeContainer (original : ValueContainer)
    (slots : Array ContainerSlot) (fields : Array ValueBinding) : MetaM ValuePayload := do
  let retained := original.slots.filter fun original =>
    !slots.any (fun slot => slot.path.toList.isPrefixOf original.path.toList)
  IO.ofExcept <| (ValuePayload.completeContainer original (retained ++ slots) fields).mapError IO.userError

private partial def atomicCallableExport? (value : Json) : MetaM (Option String) := do
  match (value.getObjValAs? String "ctor").toOption with
  | some "valueData" =>
    let .ok (.inline data) := ComputationalValue.decode value
      | throwError "the admitted callable lost its inline wrapper"
    atomicCallableExport? data
  | some "typedMap" =>
    let map ← IO.ofExcept <| (TypedMap.decode value).mapError IO.userError
    atomicCallableExport? map.callable
  | some "opaqueData" =>
    let .ok (.opaque token) := ComputationalValue.decode value
      | throwError "the admitted callable lost its complete export token"
    return some token
  | _ => pure none

/-- Stage admitted callable data at this exact native function/map position. Optional native
code receives the original complete map and the current draft graph; no graph is evaluated. -/
private def materializeCallable (reply : ImmediateReply) (request : PreparedRequest)
    (connection : Connection) (supply : IdentitySupply) (tree : IO.Ref CallableTree)
    (source : SourceLayout) (environment : RuntimeEnvironment) (origin : ValueOrigin)
    (frame : CallableFrame) (framed : Option (Nat × Nat))
    (value : Json) (path : Array InputPathStep) (draft : CellDraft)
    (makeCallable : Option PreparedCallableTransport := none)
    (whole : Option ValueContainer := none)
    (fieldPrefix : Option NativeFieldPrefix := none) : MetaM (CellDraft × ValueBinding) := do
  let original ← IO.ofExcept <|
    (reply.packetDescriptor draft.view connection path).mapError IO.userError
  let (draft, packet, _, _, retained) ← collectCallable reply request connection supply
    frame tree value path framed #[] draft
      (if source.kind == .function then some (source, fieldPrefix) else none)
  let mut draft := draft
  let mut callable : Option ValueBinding := none
  if let some makeCallable := makeCallable then
    unless source.kind == .function do
      throwError "the retained callable continuation moved outside its native function field"
    let payload ← makeCallable draft.view source (whole.getD original)
    let (next, binding) ← stageNativeResult source environment origin draft payload fieldPrefix
    draft := next
    callable := some binding
  else if source.kind == .function then
    if let some retained := retained then
      if retained.role.kind == .function then
        let retained ← match fieldPrefix with
          | some nativePrefix => do
            let candidate ← nativePrefix.checkResult environment draft.view retained
            pure candidate.root
          | none => do
            let candidate ← environment.checkResult draft.view source retained
            pure candidate.root
        callable := some retained
    if callable.isNone then
      if let some token ← atomicCallableExport? value then
        let some declaration := reply.exports.find? (·.token == token)
          | throwError "the callable lost its original supplying export"
        unless declaration.owner == connection.generation do
          throwError "the callable export belongs to another supplying connection"
        let (next, binding) ← stageNativeResult source environment origin draft
          (.ownedExport connection token declaration.captures) fieldPrefix
        draft := next
        callable := some binding
  let payload ← IO.ofExcept <| (ValuePayload.callablePacket packet original.slots callable
    original.exports (some (whole.getD original))).mapError IO.userError
  stageNativeResult source environment origin draft payload fieldPrefix

private structure NativeCallableCarrier where
  codec : PreparedMapResult
  original : ValueContainer
  endpoints : Nat × Nat

/-- Each independently supplied endpoint constrains this function even when the other
endpoint has no runtime supplier. The source helper distinguishes genuine absence from
an invalid retained supplier; a failed native check never enables self-inventory fallback. -/
private def materializeNativeFunction (reply : ImmediateReply) (request : PreparedRequest)
    (connection : Connection) (supply : IdentitySupply) (tree : IO.Ref CallableTree)
    (source : SourceLayout) (environment : RuntimeEnvironment) (origin : ValueOrigin)
    (value : Json) (path : Array InputPathStep) (draft : CellDraft)
    (marks : Array ValueBinding) (fieldPrefix : Option NativeFieldPrefix) :
    MetaM (CellDraft × ValueBinding) := do
  let (draft, domain, target) ← nativeFunctionEndpoints? request environment source supply draft marks
    (fieldPrefix := fieldPrefix)
  let sourceEndpoint ← newCallableEndpoint tree domain
  let targetEndpoint ← newCallableEndpoint tree target
  let frame : CallableFrame := {
    native := source, environment := environment, marks := marks,
    fieldPrefix := fieldPrefix, structured := domain.isSome }
  materializeCallable reply request connection supply tree source environment origin frame
    (some (sourceEndpoint, targetEndpoint)) value path draft none none fieldPrefix

private def sameNativeSource (left right : SourceLayout) : Bool :=
  left.address == right.address &&
    left.source.context.exactlyMatches right.source.context &&
    left.source.expression.equal right.source.expression && left.source.type.equal right.source.type &&
    left.source.universeParams == right.source.universeParams &&
    left.source.nativeDeclarations.exactlyMatches right.source.nativeDeclarations

private def sourceHasMapInterface (source : SourceLayout) : MetaM Bool :=
  if source.kind != .record && source.kind != .function then pure false else
    source.source.withOpen fun _ expression => do
      let type ← inferType expression
      if type.isAppOfArity ``Quiver.Hom 4 then return true
      return (← whnfR type).isAppOfArity ``Quiver.Hom 4

private def fieldMapCodec (request : PreparedRequest) (source : SourceLayout)
    (environment : RuntimeEnvironment) (supply : IdentitySupply) (draft : CellDraft)
    (marks : Array ValueBinding) (check : Option PreparedSymbolicCheck)
    (category : Option (CasCatalogue.CategoryExpr × ClosedTerm))
    (fieldPrefix : Option NativeFieldPrefix) :
    MetaM (CellDraft × PreparedMapResult) := do
  let (draft, codec) ← PreparedMapResult.fromNative request environment source supply draft marks check
    (fieldPrefix := fieldPrefix)
  let some (category, bundle) := category | return (draft, codec)
  let path ← NativePointPath.prepare source category bundle
  let codec ← PreparedMapResult.forSource environment source draft.view codec.source codec.target
    marks none (some path) none #[] check (fieldPrefix := fieldPrefix)
  return (draft, codec)

mutual

/-- The original native role and complete environment control every recursive field. The
optional carrier is restricted to its sealed exact path; all other Hom fields obtain their
own independently supplied endpoints, and plain functions cannot borrow the root inventory. -/
private partial def materializeNativeValue (reply : ImmediateReply) (request : PreparedRequest)
    (connection : Connection) (supply : IdentitySupply) (tree : IO.Ref CallableTree)
    (source : SourceLayout) (environment : RuntimeEnvironment) (origin : ValueOrigin)
    (value : Json) (path : Array InputPathStep) (draft : CellDraft)
    (fixed : Option (Array FixedResult)) (check : Option PreparedSymbolicCheck)
    (marks : Array ValueBinding := #[])
    (category : Option (CasCatalogue.CategoryExpr × ClosedTerm) := none)
    (carrier : Option NativeCallableCarrier := none)
    (originalRoot : Option (ValueContainer × Array InputPathStep) := none)
    (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM (CellDraft × ValueBinding) := do
  if let some fixed := fixed then
    let resultPath ← request.source.projectionPathTo source
    if let some selected := fixed.find? (·.path == resultPath) then
      unless ← IO.ofExcept <|
          (reply.retainsValue draft.view connection value path selected.value).mapError IO.userError do
        CasCatalogue.throwStratum .malformed "the reply changed a fixed source input"
      if let some nativePrefix := fieldPrefix then
        discard <| nativePrefix.checkResult environment draft.view selected.value
      return ← request.associateResult supply source draft selected.value fixed (complete := true)
  if let some carrier := carrier then
    let some selected := carrier.codec.callablePath
      | throwError "the native callable lost its sealed carrier path"
    if source.address == carrier.codec.native.address ++ selected then
      unless source.kind == .function do
        throwError "the selected native carrier ceased to be a function"
      let frame : CallableFrame := {
        native := carrier.codec.native, environment := carrier.codec.environment,
        marks := carrier.codec.marks, operands := carrier.codec.operands, structured := true,
        fieldPrefix := carrier.codec.fieldPrefix }
      return ← materializeCallable reply request connection supply tree source environment origin
        frame (some carrier.endpoints) value path draft carrier.codec.makeCallable
          (some carrier.original) fieldPrefix
  -- A selected carrier's data belong at that function field. Its native record ancestors
  -- still retain their complete packet, even when the callable itself is a token or reference.
  if carrier.isNone then
    if let some reference := reply.references.find? (·.path == path) then
      let retained ← match fieldPrefix with
        | some nativePrefix => do
          let candidate ← nativePrefix.checkResult environment draft.view reference.binding
          pure candidate.root
        | none => pure reference.binding
      if let some fixed := fixed then
        return ← request.associateResult supply source draft retained fixed (complete := true)
      if fieldPrefix.isSome then return (draft, retained)
      let candidate ← environment.checkResult draft.view source retained
      return (draft, candidate.root)
  let tag := (value.getObjValAs? String "ctor").toOption
  if source.kind == .function && tag != some "opaqueData" then
    return ← materializeNativeFunction reply request connection supply tree source environment origin
      value path draft marks fieldPrefix
  if tag == some "valueData" || (tag == some "opaqueData" && carrier.isNone) then
    let .ok envelope := ComputationalValue.decode value
      | throwError "the parsed native result lost its computational value envelope"
    match envelope with
    | .inline data =>
      return ← materializeNativeValue reply request connection supply tree source environment origin
        data (path ++ #[.field "args", .index 0]) draft fixed check marks category carrier originalRoot fieldPrefix
    | .opaque token =>
      let some declaration := reply.exports.find? (·.token == token)
        | throwError "the parsed native result lost its original export declaration"
      unless declaration.owner == connection.generation do
        throwError "the native result export belongs to another supplying connection"
      return ← stageNativeResult source environment origin draft
        (.ownedExport connection token declaration.captures) fieldPrefix
  let nativeHom ← if carrier.isNone then sourceHasMapInterface source else pure false
  if carrier.isNone && nativeHom then
    let (draft, codec) ← fieldMapCodec request source environment supply draft marks check
      category fieldPrefix
    return ← materializeNativeMap reply request connection supply tree source environment origin
      codec value path draft fixed check fieldPrefix
  discard <| ScalarLiteral.check source value
  match source.kind with
  | .proof => throwError "a source proof has no computational reply position"
  | .function =>
    materializeNativeFunction reply request connection supply tree source environment origin
      value path draft marks fieldPrefix
  | .record =>
    let (original, rootPath) ← match originalRoot with
      | some selected => pure selected
      | none => do
        let original ← IO.ofExcept <|
          (reply.packetDescriptor draft.view connection path).mapError IO.userError
        pure (original, path)
    unless rootPath.toList.isPrefixOf path.toList do
      throwError "a native record moved outside its original packet root"
    let relative := path.extract rootPath.size path.size
    let layout ← RecordLayout.ofSource source
    let fields := layout.fields.filter (·.field.wireIndex.isSome)
    let positions ← recordReplyPositions fields.size value
    let mut draft := draft
    let mut record ← RecordPrefix.prepare supply origin.program origin.occurrence layout
      draft.view environment.sourceMarks
    let mut slots : Array ContainerSlot := #[]
    let mut selected : Array ValueBinding := #[]
    for prepared in fields, position in positions do
      let current ← environment.withSourceMarks #[] (some draft.view)
      let immediate ← record.currentField
      let nativePrefix ← match fieldPrefix with
        | none => pure immediate
        | some outer => do
          let outer ← outer.descend prepared.field.projection
          outer.join immediate
      let childOrigin ← if fixed.isSome then do
          nativePrefix.attachOrigin (← request.originFor prepared.layout (some draft.view)) draft.view
        else nativePrefix.origin current origin.program origin.occurrence draft.view
      let nextCarrier := carrier.filter fun carrier =>
        (prepared.layout.address.toList.isPrefixOf
          (carrier.codec.native.address ++ carrier.codec.callablePath.getD #[]).toList)
      let (next, binding) ← materializeNativeValue reply request connection supply tree prepared.layout
        current childOrigin position.2 (path ++ position.1) draft fixed check marks none nextCarrier none
          (some nativePrefix)
      let (next, nextRecord, binding) ← liftM (m := IO) <| next.bindField record binding
      draft := next
      record := nextRecord
      slots := slots.push { path := relative ++ position.1, binding, fieldIndex := prepared.field.wireIndex }
      selected := selected.push binding
    let .ok _ := record.finish
      | throwError "the materialized native record has an incomplete formal field prefix"
    let payload ← completeNativeContainer original slots selected
    stageNativeResult source environment origin draft payload fieldPrefix
  | .data | .typeValue =>
    let original ← IO.ofExcept <|
      (reply.packetDescriptor draft.view connection path).mapError IO.userError
    let payload ← IO.ofExcept <|
      (ValuePayload.descriptor value original.slots original.exports).mapError IO.userError
    stageNativeResult source environment origin draft payload fieldPrefix

private partial def materializeNativeMap (reply : ImmediateReply) (request : PreparedRequest)
    (connection : Connection) (supply : IdentitySupply) (tree : IO.Ref CallableTree)
    (source : SourceLayout) (environment : RuntimeEnvironment) (origin : ValueOrigin)
    (codec : PreparedMapResult) (value : Json) (path : Array InputPathStep) (draft : CellDraft)
    (fixed : Option (Array FixedResult)) (check : Option PreparedSymbolicCheck)
    (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM (CellDraft × ValueBinding) := do
  unless sameNativeSource codec.native source do
    throwError "the map codec changed its original complete native result position"
  if let some fixed := fixed then
    let resultPath ← request.source.projectionPathTo source
    if let some selected := fixed.find? (·.path == resultPath) then
      unless ← IO.ofExcept <|
          (reply.retainsValue draft.view connection value path selected.value).mapError IO.userError do
        CasCatalogue.throwStratum .malformed "the map reply changed a fixed source input"
      if let some nativePrefix := fieldPrefix then
        discard <| nativePrefix.checkResult environment draft.view selected.value
      return ← request.associateResult supply source draft selected.value fixed (complete := true)
  let original ← IO.ofExcept <|
    (reply.packetDescriptor draft.view connection path).mapError IO.userError
  let sourceEndpoint ← newCallableEndpoint tree (some codec.source)
  let targetEndpoint ← newCallableEndpoint tree (some codec.target)
  let frame : CallableFrame := {
    native := codec.native, environment := codec.environment, marks := codec.marks,
    operands := codec.operands, structured := true, fieldPrefix := codec.fieldPrefix }
  let (body, bodyPath) ← unwrapCallable value path
  if reply.references.any (·.path == bodyPath) ||
      (body.getObjValAs? String "ctor").toOption == some "opaqueData" then
    return ← materializeNativeValue reply request connection supply tree source environment origin
      body bodyPath draft fixed check codec.marks none none none fieldPrefix
  let some carrierPath := codec.callablePath
    | return ← materializeCallable reply request connection supply tree source environment origin frame
        (some (sourceEndpoint, targetEndpoint)) value path draft none none fieldPrefix
  let carrier : NativeCallableCarrier := ⟨codec, original, (sourceEndpoint, targetEndpoint)⟩
  if carrierPath.isEmpty then
    return ← materializeNativeValue reply request connection supply tree source environment origin
      value path draft fixed check codec.marks none (some carrier) none fieldPrefix
  let (body, bodyPath) ← if (body.getObjValAs? String "ctor").toOption == some "typedMap" then do
      IO.ofExcept <| (checkServiceFields #["ctor", "args"] body).mapError IO.userError
      let map ← IO.ofExcept <| (TypedMap.decode body).mapError IO.userError
      requireCallableEndpoint reply draft.view connection codec.source map.source
        (bodyPath ++ #[.field "args", .index 0])
      requireCallableEndpoint reply draft.view connection codec.target map.target
        (bodyPath ++ #[.field "args", .index 1])
      pure (map.callable, bodyPath ++ #[.field "args", .index 2])
    else pure (body, bodyPath)
  materializeNativeValue reply request connection supply tree source environment origin
    body bodyPath draft fixed check codec.marks none (some carrier) (some (original, path)) fieldPrefix

end

/-- Consume only the exact non-Prop ports of the accepted constructor, in its full declared
order. Each complete actual port enters the next port's context; proof slots stay empty. -/
private def materializeConstruction (reply : ImmediateReply) (request : PreparedRequest)
    (connection : Connection) (supply : IdentitySupply) (tree : IO.Ref CallableTree)
    (construction : PreparedConstructionResult) (draft : CellDraft) :
    MetaM (CellDraft × ValueBinding) := do
  let original ← IO.ofExcept <|
    (reply.packetDescriptor draft.view connection #[]).mapError IO.userError
  let (value, path) ← unwrapCallable reply.value #[]
  let expected := if construction.colimit then "cocone" else "cone"
  let ports := construction.plan.ports.filter (·.argument.wireIndex.isSome)
  if (value.getObjValAs? String "ctor").toOption == some "opaqueData" then
    throwError "the construction reply omitted its complete native data ports"
  if let some reference := reply.references.find? (·.path == path) then
    let some node := draft.view.find reference.binding.value
      | throwError "the retained construction ports are outside the visible graph"
    let .container stored := node.payload.data
      | throwError "a construction reference requires its original complete stored data ports"
    let some fields := stored.fields
      | throwError "a construction reference has no complete stored native fields"
    unless fields.size == (reference.binding.role.fields.filter (·.wireIndex.isSome)).size do
      throwError "a construction reference lost its complete native field ports"
    let some packet := stored.originalPacket
      | throwError "a construction reference lost its original complete constructor-port packet"
    let (packet, _) ← unwrapCallable packet.template #[]
    IO.ofExcept <| (checkServiceFields #["ctor", "args"] packet).mapError IO.userError
    unless (packet.getObjValAs? String "ctor").toOption == some expected do
      throwError "a construction reference changed its original cone/cocone data ports"
    let arguments ← IO.ofExcept <| (packet.getObjValAs? (Array Json) "args").mapError IO.userError
    unless arguments.size == ports.size do
      throwError "a construction reference changed its complete declared native port arity"
    let origin ← request.originFor request.source (some draft.view)
    return ← materializeNativeValue reply request connection supply tree request.source
      request.environment origin value path draft (some #[]) construction.checkSymbolic construction.marks
  IO.ofExcept <| (checkServiceFields #["ctor", "args"] value).mapError IO.userError
  unless (value.getObjValAs? String "ctor").toOption == some expected do
    throwError "the construction reply changed its original cone/cocone interface"
  let arguments ← IO.ofExcept <| (value.getObjValAs? (Array Json) "args").mapError IO.userError
  unless arguments.size == ports.size do
    throwError "the construction reply changed its complete native data-port arity"
  let mut draft := draft
  let mut nativePrefix ← ConstructorPortPrefix.prepare request draft.view construction.plan construction.marks
  for value in arguments, index in [:arguments.size] do
    let some port := nativePrefix.current?
      | throwError "the construction reply supplied an extra native data port"
    unless port.argument.wireIndex == some index do
      throwError "the construction reply changed its native computational port order"
    let position := path ++ #[.field "args", .index index]
    let origin ← nativePrefix.origin request draft.view
    let environment ← nativePrefix.environment.withSourceMarks #[] (some draft.view)
    let (next, binding) ← materializeNativeValue reply request connection supply tree port.argument.source
      environment origin value position draft none construction.checkSymbolic construction.marks
      (some (construction.category, construction.bundle))
    draft := next
    nativePrefix ← nativePrefix.bind draft.view binding
  let values ← IO.ofExcept <| nativePrefix.finish.mapError IO.userError
  construction.assemble request.source original path values draft

/-- Materialize a parsed immediate reply into an isolated draft with native prepared roles.
The original scope/reservation gate precedes every codec, and whole native admission follows
complete finite/symbolic framing. No intermediate port or field enters the transaction. -/
opaque ImmediateReply.materialize (reply : ImmediateReply) (request : PreparedRequest)
    (transaction : CellTransaction) (scope : RequestScope) (connection : Connection)
    (resolveFixed : Option (FixedInput → MetaM ValueBinding) := none)
    (codec : Option (PreparedResultCodec request.roles.scope) := none) :
    MetaM (CellDraft × PreparedResponse request) := do
  unless reply.scopeId == scope.id && scope.reservation.transaction == transaction.id &&
      scope.reservation.occurrence == request.occurrence &&
      scope.reservation.connection == connection.generation do
    throwError "reply materialization changed its prepared invocation or scope"
  let graph ← liftM (m := IO) transaction.view
  discard <| liftM (m := IO) <|
    scope.resolveMany scope.reservation graph scope.wireId #[]
  let kind : Option PreparedResultKind := codec.map (fun prepared => prepared.kind)
  let fixed ← match kind with
    | some (.construction _) => pure #[]
    | some (.map prepared) =>
      preflightFixedResults reply request transaction resolveFixed request.source
        reply.value #[] prepared.callablePath.isSome
    | some (.native _) | none =>
      preflightFixedResults reply request transaction resolveFixed request.source reply.value #[]
  let draft ← liftM (m := IO) transaction.draft
  discard <| liftM (m := IO) <|
    scope.resolveMany scope.reservation draft.view scope.wireId #[]
  let tree ← IO.mkRef ({} : CallableTree)
  let supply := transaction.owners.identities
  let origin ← request.originFor request.source (some draft.view)
  let (draft, binding, check) ← match kind with
    | some (.map prepared) => do
      let (draft, binding) ← materializeNativeMap reply request connection supply tree
        request.source request.environment origin prepared reply.value #[] draft
        (some fixed) prepared.checkSymbolic
      pure (draft, binding, prepared.checkSymbolic)
    | some (.construction prepared) => do
      let (draft, binding) ← materializeConstruction reply request connection supply tree prepared draft
      pure (draft, binding, prepared.checkSymbolic)
    | some (.native check) => do
      let (draft, binding) ← materializeNativeValue reply request connection supply tree
        request.source request.environment origin reply.value #[] draft (some fixed) (some check)
      pure (draft, binding, some check)
    | none => do
      let (draft, binding) ← materializeNativeValue reply request connection supply tree
        request.source request.environment origin reply.value #[] draft (some fixed) none
      pure (draft, binding, none)
  checkFiniteCallableTree reply tree draft.view
  checkCallableTree tree draft.view check
  return (draft, ← request.admitResult draft.view binding)

/-- Admit and install a complete immediate reply with its exact transaction-local completion.
Publication remains the whole-cell commit transition. -/
opaque ImmediateReply.stageCompletion (reply : ImmediateReply) (request : PreparedRequest)
    (transaction : CellTransaction) (scope : RequestScope) (connection : Connection)
    (resolveFixed : Option (FixedInput → MetaM ValueBinding) := none)
    (codec : Option (PreparedResultCodec request.roles.scope) := none) :
    MetaM (Except TransactionFailure CompletionAssociation) := do
  let (draft, response) ← reply.materialize request transaction scope connection resolveFixed codec
  transaction.completeReply draft request response scope reply

end CasRuntime
