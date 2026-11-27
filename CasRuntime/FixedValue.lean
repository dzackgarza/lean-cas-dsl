module

public import CasRuntime.Reply

public section

namespace CasRuntime

open Lean CasCatalogue.Backend



private def fixedValuePosition (value : Json) (path : List InputPathStep) : Except String Json := do
  match path with
  | [] => return value
  | .field name :: rest => fixedValuePosition (← value.getObjVal? name) rest
  | .index index :: rest =>
    let values ← value.getArr?
    let some entry := values[index]? | throw "a fixed input slot is outside the reply array"
    fixedValuePosition entry rest






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
    unless expected.nativeRole.kind == .record &&
        (expected.nativeRole.fields.filter (·.wireIndex.isSome)).size == fields.size do
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
    if (expected.nativeRole.kind == .function || container.callable.isSome) &&
        !container.callableData then return false
    if container.packetExports.any (·.owner != connection.generation) then return false
    let mut fragments := #[]
    for slot in container.slots do
      let field ← match slot.fieldIndex with
        | none => pure slot.binding
        | some index => graph.project expected index
      let fragment ← fixedValuePosition value slot.path.toList
      unless ← reply.retainsValue graph connection fragment (path ++ slot.path) field do
        return false
      fragments := fragments.push fragment
    for owned in container.exports do
      let fragment ← fixedValuePosition value owned.path.toList
      let .opaque token ← ComputationalValue.decode fragment | return false
      unless token == owned.token do return false
      let some declaration := reply.exports.find? (·.token == token)
        | throw "the parsed reply lost its retained packet export declaration"
      unless declaration.owner == owned.owner &&
          declaration.captures.size == owned.captures.size do return false
      discard <| graph.requiredOwners (owned.captures ++ declaration.captures)
      for retained in owned.captures, actual in declaration.captures do
        unless retained.value == actual.value &&
            retained.associationIds == actual.associationIds do return false
    return (← container.fillForOwner connection.generation fragments) == value

end CasRuntime
