module

public import CasRuntime.Scope

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

structure ReplyReference where
  path : Array InputPathStep
  binding : ValueBinding

structure ReplyExport where
  token : String
  owner : ConnectionGeneration
  captures : Array ValueBinding

/-- Parsed control authority; prepared-layout and lifecycle admission follow separately. -/
structure ImmediateReply where
  private mk ::
  requestId : Nat
  scopeId : RuntimeId .scope
  value : Json
  exports : Array ReplyExport
  references : Array ReplyReference

private structure ReplyScan where
  references : Array (Array InputPathStep × ScopedReference) := #[]
  tokens : Array (Array InputPathStep × String) := #[]

/-- Walk the existing JSON packet structure, recognizing only reserved reference/envelope tags.
Reference: CasContract.Port.validateResultRefs and ComputationalValue.decode at f0431beb. -/
private partial def scanReply (value : Json) (path : Array InputPathStep) : Except String ReplyScan := do
  if let some reference ← ScopedReference.parse? value then
    return { references := #[(path, reference)] }
  let tag := (value.getObjValAs? String "ctor").toOption
  if tag == some "deferredData" then
    throw "a deferred control is not an immediate result value"
  if tag == some "opaqueData" || tag == some "valueData" then
    checkServiceFields #["ctor", "args"] value
    match ← ComputationalValue.decode value with
    | .opaque token => return { tokens := #[(path, token)] }
    | .inline _ => pure ()
  let mut found : ReplyScan := {}
  match value with
  | .arr values =>
    for index in [:values.size] do
      let child ← scanReply values[index]! (path.push (.index index))
      found := ⟨found.references ++ child.references, found.tokens ++ child.tokens⟩
  | .obj fields =>
    for (name, entry) in fields.toList do
      let child ← scanReply entry (path.push (.field name))
      found := ⟨found.references ++ child.references, found.tokens ++ child.tokens⟩
  | _ => pure ()
  return found

/-- Read every export and its exact immutable capture table while its request scope is live.
Immediate, deferred and suspended controls share this original export-admission boundary. -/
opaque ReplyExport.parseControl (scope : RequestScope) (actual : DispatchReservation)
    (graph : ValueGraph) (wireId : String) (exportValue : Json) : IO (Array ReplyExport) := do
  let declarations ← IO.ofExcept <| exportValue.getArr?.mapError IO.userError
  let mut tokens : Std.HashSet String := {}
  let mut exports : Array ReplyExport := #[]
  for declaration in declarations do
    IO.ofExcept <| (checkServiceFields #["token", "captures"] declaration).mapError IO.userError
    let token ← IO.ofExcept <| (declaration.getObjValAs? String "token").mapError IO.userError
    if token.isEmpty || tokens.contains token then
      throw <| IO.userError "the reply export table has an empty or repeated token"
    tokens := tokens.insert token
    let captureValue ← IO.ofExcept <| (declaration.getObjVal? "captures").mapError IO.userError
    let captures ← IO.ofExcept <| captureValue.getArr?.mapError IO.userError
    let references ← captures.mapM fun capture => do
      let some reference ← IO.ofExcept <| (ScopedReference.parse? capture).mapError IO.userError
        | throw <| IO.userError "an export capture is not a scoped reference"
      return reference
    let retained ← scope.capture actual graph wireId references
    exports := exports.push { token, owner := actual.connection, captures := retained }
  return exports

/-- Check a whole child/template packet before scheduling a group. Result references remain
relative to its completed prefix; all other references must already denote original input
positions in this exact request. This performs no mathematical operand interpretation. -/
opaque RequestScope.validateReplyTemplate (scope : RequestScope) (actual : DispatchReservation)
    (graph : ValueGraph) (wireId : String) (exports : Array ReplyExport)
    (resultBound : Nat) (value : Json) : IO Unit := do
  let found ← IO.ofExcept <| (scanReply value #[]).mapError IO.userError
  for (_, token) in found.tokens do
    unless exports.any (·.token == token) do
      throw <| IO.userError "an opaque control operand has no declaration in this reply"
  let mut original := #[]
  for (_, reference) in found.references do
    match reference with
    | .result index =>
      unless index < resultBound do
        throw <| IO.userError "a result reference is self, forward or outside its program"
    | _ => original := original.push reference
  discard <| scope.resolveMany actual graph wireId original

/-- Validate the complete immediate control record before any graph materialization.
Owner identity comes from the actual invocation; capture/reference authority comes from its scope.
Source: execution contract v2 §4.2 and the retained-capture amendment. -/
opaque ImmediateReply.parseControl (scope : RequestScope) (actual : DispatchReservation)
    (graph : ValueGraph) (wireId : String) (expectedRequestId : Nat) (frame : Json) :
    IO ImmediateReply := do
  IO.ofExcept <|
    (checkServiceFields #["request_id", "status", "value", "exports"] frame).mapError IO.userError
  let requestValue ← IO.ofExcept <| (frame.getObjVal? "request_id").mapError IO.userError
  let requestId ← IO.ofExcept <| requestValue.getNat?.mapError IO.userError
  unless requestId == expectedRequestId do
    throw <| IO.userError "the reply request identity does not match its invocation"
  let status ← IO.ofExcept <| (frame.getObjValAs? String "status").mapError IO.userError
  unless status == "ok" do throw <| IO.userError "the control is not an immediate successful reply"
  let value ← IO.ofExcept <| (frame.getObjVal? "value").mapError IO.userError
  let exportValue ← IO.ofExcept <| (frame.getObjVal? "exports").mapError IO.userError
  let exports ← ReplyExport.parseControl scope actual graph wireId exportValue
  let found ← IO.ofExcept <| (scanReply value #[]).mapError IO.userError
  for (_, token) in found.tokens do
    unless exports.any (·.token == token) do
      throw <| IO.userError "an opaque result token has no declaration in this reply"
  let bindings ← scope.resolveMany actual graph wireId (found.references.map (·.2))
  let references := found.references.zipWith (fun position binding =>
    { path := position.1, binding : ReplyReference }) bindings
  return ⟨requestId, scope.id, value, exports, references⟩

/-- Read one structural position of this exact admitted reply. A scoped reference remains
an indivisible authority; its wire fields cannot be reinterpreted as nested result data. -/
def ImmediateReply.fragmentAt (reply : ImmediateReply) (path : Array InputPathStep) :
    Except String Json := do
  for reference in reply.references do
    if reference.path != path && reference.path.toList.isPrefixOf path.toList then
      throw "a reply fragment descends through an original scoped reference"
  let mut value := reply.value
  for step in path do
    match step with
    | .field name => value ← value.getObjVal? name
    | .index index =>
      let values ← value.getArr?
      let some selected := values[index]?
        | throw "the selected reply fragment is outside its original array"
      value := selected
  return value

/-- Retain a complete inert fragment with the parser's exact original reference leaves and
actual export authorities. Export positions are transport ownership only; they do not create
native values, select mathematical endpoints or add an application address. -/
opaque ImmediateReply.packetDescriptor (reply : ImmediateReply) (graph : ValueGraph)
    (connection : Connection) (path : Array InputPathStep) : Except String ValueContainer := do
  unless connection.generation.worker == graph.worker do
    throw "the retained reply packet belongs to a different worker"
  let value ← reply.fragmentAt path
  let slots := reply.references.filterMap fun reference =>
    if path.toList.isPrefixOf reference.path.toList then
      some (⟨reference.path.extract path.size reference.path.size,
        reference.binding, none⟩ : ContainerSlot)
    else none
  discard <| graph.requiredOwners (slots.map (·.binding))
  let found ← scanReply value #[]
  let mut exports := #[]
  for (position, token) in found.tokens do
    let some declaration := reply.exports.find? (·.token == token)
      | throw "the admitted packet lost its original export declaration"
    unless declaration.owner == connection.generation do
      throw "the retained packet export belongs to another supplying connection"
    discard <| graph.requiredOwners declaration.captures
    exports := exports.push (← PacketExport.fromConnection connection reply.scopeId
      (path ++ position) position token
      declaration.captures)
  let payload ← ValuePayload.descriptor value slots exports
  let .container packet := payload.data
    | throw "the retained reply packet lost its original descriptor"
  return packet

end CasRuntime
