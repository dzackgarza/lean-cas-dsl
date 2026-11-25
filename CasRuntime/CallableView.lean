module

public import CasRuntime.CallablePacket
public import CasRuntime.Reply

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

private def collapseArray (values : Array CallableDatum) : CallableDatum :=
  let literals := values.filterMap fun value => match value with
    | .literal value => some value
    | _ => none
  if literals.size == values.size then .literal (.arr literals) else .array values

private def collapseObject (values : Array (String × CallableDatum)) : CallableDatum :=
  let literals := values.filterMap fun (name, value) => match value with
    | .literal value => some (name, value)
    | _ => none
  if literals.size == values.size then .literal (Json.mkObj literals.toList) else .object values

mutual
  /-- Resolve only exact already selected references while reading comparison data. -/
  private partial def bindingDatum (graph : ValueGraph) (binding : ValueBinding)
      (seen : Std.HashSet (RuntimeId .value)) : Except String CallableDatum := do
    if seen.contains binding.value then throw "the callable comparison data have a cycle"
    discard <| graph.requiredOwners #[binding]
    let some node := graph.find binding.value
      | throw "a callable comparison reference is outside its visible graph"
    let seen := seen.insert binding.value
    match node.payload.data with
    | .portable bytes =>
      let some text := String.fromUTF8? bytes
        | throw "a portable callable point is not UTF-8 packet data"
      let value ← Json.parse text
      checkLiteral value
      return .literal value
    | .closure .. | .ownedToken .. =>
      return .reference binding.value binding.associationIds
    | .product fields =>
      let mut values := #[]
      for index in [:fields.size] do
        values := values.push (← bindingDatum graph (← graph.project binding index) seen)
      return match values with
        | #[only] => only
        | _ => collapseArray values
    | .container value =>
      let mut slots := #[]
      for slot in value.slots do
        let selected ← match slot.fieldIndex with
          | none => pure slot.binding
          | some index => graph.project binding index
        slots := slots.push (slot.path, selected)
      packetDatum graph value.template #[]
        (fun path => (slots.find? (·.1 == path)).map (·.2))
        (fun path => (value.exports.find? (·.path == path)).map fun owned =>
          .exported owned.owner owned.token
            (owned.captures.map fun captured => (captured.value, captured.associationIds))) seen

  private partial def packetDatum (graph : ValueGraph) (value : Json)
      (path : Array InputPathStep) (referenceAt : Array InputPathStep → Option ValueBinding)
      (exportAt : Array InputPathStep → Option CallableDatum)
      (seen : Std.HashSet (RuntimeId .value)) : Except String CallableDatum := do
    if let some reference := referenceAt path then
      return ← bindingDatum graph reference seen
    if let some exported := exportAt path then return exported
    match value with
    | .arr values =>
      return collapseArray (← values.mapIdxM fun index value =>
        packetDatum graph value (path.push (.index index)) referenceAt exportAt seen)
    | .obj values =>
      return collapseObject (← values.toList.toArray.mapM fun (name, value) => do
        return (name, ← packetDatum graph value (path.push (.field name)) referenceAt exportAt seen))
    | _ => return .literal value
end

/-- Read actual endpoint/point data from its original binding; never choose a source by data. -/
opaque ValueGraph.callableDatum (graph : ValueGraph) (binding : ValueBinding) :
    Except String CallableDatum := bindingDatum graph binding {}

/-- Resolve only the parser's checked current-scope references for finite-data comparison.
The original wire packet and every reference slot remain separate and unchanged. -/
opaque ImmediateReply.callableDatum (reply : ImmediateReply) (graph : ValueGraph)
    (value : Json) (path : Array InputPathStep) : Except String CallableDatum := do
  unless (← reply.fragmentAt path) == value do
    throw "callable framing changed its exact original reply fragment"
  packetDatum graph value path
    (fun path => (reply.references.find? (·.path == path)).map (·.binding))
    (fun path => do
      let value ← (reply.fragmentAt path).toOption
      let .opaque token ← (ComputationalValue.decode value).toOption | none
      let declaration ← reply.exports.find? (·.token == token)
      return .exported declaration.owner token
        (declaration.captures.map fun captured => (captured.value, captured.associationIds))) {}

private def datumField (value : CallableDatum) (name : String) : Except String CallableDatum := do
  match value with
  | .literal value => return .literal (← value.getObjVal? name)
  | .object values =>
    let some (_, value) := values.find? (·.1 == name)
      | throw "a callable descriptor omitted a required field"
    return value
  | _ => throw "a callable descriptor requires complete object data"

private def datumArray (value : CallableDatum) : Except String (Array CallableDatum) := do
  match value with
  | .literal value => return (← value.getArr?).map CallableDatum.literal
  | .array values => return values
  | _ => throw "a callable inventory requires an array of actual points"

/-- Inventories come only from actual finiteData packets, including their original references. -/
partial def CallableDatum.endpointInventory (value : CallableDatum) :
    Except String (Option (Array CallableDatum)) := do
  let .ok (.literal (.str tag)) := datumField value "ctor" | return none
  if tag == "valueData" then
    let #[data] ← datumArray (← datumField value "args")
      | throw "valueData requires its complete actual object data"
    return ← data.endpointInventory
  if tag != "finiteData" then return none
  let #[_, inventory] ← datumArray (← datumField value "args")
    | throw "finiteData requires its complete object descriptor and actual inventory"
  let inventory ← datumArray inventory
  CasCatalogue.GraphData.validateInventory inventory
  return some inventory

end CasRuntime
