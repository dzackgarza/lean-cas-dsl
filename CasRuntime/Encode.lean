module

public import CasRuntime.Scope
public import CasCompiler.Program

public section

namespace CasRuntime

open Lean CasCompiler CasCatalogue.Backend

/-- Original packet data and fresh scope/input authorities for the actual receiving process. -/
structure EncodedInputs where
  values : Array Json
  slots : Array ValueBinding
  inputs : Array InputPosition

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
    (binding : ValueBinding) (path : Array InputPathStep) (state : EncodingState) :
    Except String (Json × EncodingState) := do
  let some node := graph.find binding.value | throw "the encoded input is outside the visible graph"
  let state := addInput state path binding
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
      let (packet, next) ← encodeAt graph receiver actual (path ++ slot.path) state
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
      let (packet, next) ← encodeAt graph receiver field fieldPath state
      packets := packets.push packet
      state := next
    if let #[packet] := packets then return (packet, state)
    return (.arr packets, state)

/-- Encode disjoint complete input roots for one actual consumer.
Reuse: graph visibility/owner traversal, the released JSON parser and packet encodings.
Each foreign occurrence gets its own scoped position, even when actual values alias.
Liveness belongs to the later atomic reservation/send check. -/
private def encodeRoots (graph : ValueGraph) (receiver : ConnectionGeneration)
    (roots : Array InputPosition) (captures : Array ValueBinding) : Except String EncodedInputs := do
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
    let (packet, next) ← encodeAt graph receiver root.binding root.path state
    values := values.push packet
    state := next
  return ⟨values, state.slots.extract captures.size state.slots.size, state.inputs⟩

/-- Primitive scopes have no retained export capture prefix. -/
opaque ValueGraph.encodeInputs (graph : ValueGraph) (receiver : ConnectionGeneration)
    (roots : Array InputPosition) : Except String EncodedInputs :=
  encodeRoots graph receiver roots #[]

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

end CasRuntime

namespace CasCompiler

open Lean Meta CasRuntime CasCatalogue.Backend

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

end CasCompiler
