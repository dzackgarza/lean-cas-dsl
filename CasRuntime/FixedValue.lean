module

public import CasRuntime.Reply

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

/-- Read only the exact JSON position retained by a typed container slot.
Reuse: Lean.Json getters and ValueContainer.fill's InputPathStep grammar. -/
private def fixedValuePosition (value : Json) (path : List InputPathStep) : Except String Json := do
  match path with
  | [] => return value
  | .field name :: rest => fixedValuePosition (← value.getObjVal? name) rest
  | .index index :: rest =>
    let values ← value.getArr?
    let some entry := values[index]? | throw "a fixed input slot is outside the reply array"
    fixedValuePosition entry rest

/-- Check a reply fragment against an already selected fixed source input.
References preserve its node and original association prefix; literal data are compared only
after that input is selected. Products and containers follow their retained field views.
Reuse: ImmediateReply's parsed authorities, ValueGraph.project, ValueContainer.fill and the
released computational envelope. This comparison never searches for an input by its data. -/
partial def ImmediateReply.retainsValue (reply : ImmediateReply) (graph : ValueGraph)
    (connection : Connection) (value : Json) (path : Array InputPathStep)
    (expected : ValueBinding) : Except String Bool := do
  unless connection.generation.worker == graph.worker do
    throw "the fixed input comparison belongs to a different worker"
  discard <| graph.requiredOwners #[expected]
  if let some reference := reply.references.find? (·.path == path) then
    discard <| graph.requiredOwners #[reference.binding]
    return reference.binding.value == expected.value &&
      expected.associationIds.toList.isPrefixOf reference.binding.associationIds.toList
  let some node := graph.find expected.value
    | throw "the fixed source input is outside the visible graph"
  let tag := (value.getObjValAs? String "ctor").toOption
  if tag == some "valueData" || tag == some "opaqueData" then
    match ← ComputationalValue.decode value with
    | .inline data =>
      return ← reply.retainsValue graph connection data
        (path ++ #[.field "args", .index 0]) expected
    | .opaque token =>
      let some declaration := reply.exports.find? (·.token == token)
        | throw "the parsed reply lost its native export declaration"
      unless declaration.owner == connection.generation do
        throw "the fixed input export belongs to a different supplying connection"
      let .ownedToken owner retainedToken captures := node.payload.data | return false
      discard <| graph.requiredOwners (captures ++ declaration.captures)
      unless owner == declaration.owner && retainedToken == token &&
          captures.size == declaration.captures.size do return false
      for retained in captures, actual in declaration.captures do
        unless retained.value == actual.value &&
            retained.associationIds == actual.associationIds do return false
      return true
  match node.payload.data with
  | .portable bytes =>
    let some text := String.fromUTF8? bytes
      | throw "the fixed portable input is not UTF-8 packet data"
    let packet ← Json.parse text
    checkLiteral packet
    return packet == value
  | .closure .. | .ownedToken .. => return false
  | .product fields =>
    unless expected.role.kind == .record &&
        (expected.role.fields.filter (·.wireIndex.isSome)).size == fields.size do
      throw "the fixed product does not match its complete source data-field interface"
    let values ← if fields.size == 1 then pure #[value] else value.getArr?
    unless values.size == fields.size do
      throw "the fixed reply record has a different complete data-field arity"
    for index in [:fields.size] do
      let field ← graph.project expected index
      let fieldPath := if fields.size == 1 then path else path.push (.index index)
      unless ← reply.retainsValue graph connection values[index]! fieldPath field do
        return false
    return true
  | .container container =>
    if expected.role.kind == .function || container.callable.isSome then return false
    let mut fragments := #[]
    for slot in container.slots do
      let field ← match slot.fieldIndex with
        | none => pure slot.binding
        | some index => graph.project expected index
      let fragment ← fixedValuePosition value slot.path.toList
      unless ← reply.retainsValue graph connection fragment (path ++ slot.path) field do
        return false
      fragments := fragments.push fragment
    return (← container.fill fragments) == value

end CasRuntime
