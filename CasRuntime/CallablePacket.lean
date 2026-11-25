module

public import CasContract.Port
public import CasCatalogue.GraphData
public import CasRuntime.Owner
public import CasRuntime.ScopeReference

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

/-- Data used only for finite framing. Portable references use their actual packets;
nonportable values retain original node/association identity. Transport slots stay unchanged. -/
inductive CallableDatum where
  | literal (value : Json)
  | reference (value : RuntimeId .value) (associations : Array (RuntimeId .association))
  | exported (owner : ConnectionGeneration) (token : String)
      (captures : Array (RuntimeId .value × Array (RuntimeId .association)))
  | array (values : Array CallableDatum)
  | object (values : Array (String × CallableDatum))
  deriving BEq

/-- Complete public callable data, with its released representation framing already checked.
This evidence supplies no executable code and asserts no correctness of the returned map. -/
structure CallablePacket where
  private mk ::
  value : Json

/-- Admit the released finite graph alternatives at complete actual computational endpoints.
An explicit finiteGraph inventory is data supplied by the producer; when the independently
retained domain also has an inventory, both must describe the same complete computational set.
Graph order is immaterial. This gate never supplies a missing computation or executes a graph. -/
opaque CallablePacket.finiteWith (value : Json)
    (domain target : Option (Array CallableDatum))
    (view : Json → Array InputPathStep → Except String CallableDatum) :
    Except String CallablePacket := do
  let mut graph := value
  let mut graphPath := #[]
  let mut actualDomain := domain
  if (value.getObjValAs? String "ctor").toOption == some "finiteGraph" then
    checkServiceFields #["ctor", "args"] value
    let #[inventory, body] ← (← value.getObjVal? "args").getArr?
      | throw "finiteGraph requires its actual domain inventory and complete graph"
    let inventory ← (← inventory.getArr?).mapIdxM fun index point =>
      view point #[.field "args", .index 0, .index index]
    CasCatalogue.GraphData.validateInventory inventory
    if let some domain := domain then
      CasCatalogue.GraphData.validateInventory domain
      unless domain.size == inventory.size && inventory.all domain.contains do
        throw "the finite graph changed its selected actual domain inventory"
    actualDomain := some inventory
    graph := body
    graphPath := #[.field "args", .index 1]
  let some domain := actualDomain
    | throw "a finite graph requires its complete actual domain inventory"
  let pairs ← (← CasCatalogue.GraphData.pairs graph).mapIdxM fun index (input, output) => do
    return (← view input (graphPath ++ #[.index index, .index 0]),
      ← view output (graphPath ++ #[.index index, .index 1]))
  CasCatalogue.GraphData.validateEndpoints domain target pairs
  return ⟨value⟩

/-- Literal-only specialization of the same gate. Scoped replies use finiteWith. -/
def CallablePacket.finite (value : Json) (domain target : Option (Array Json)) :
    Except String CallablePacket :=
  CallablePacket.finiteWith value (domain.map (·.map CallableDatum.literal))
    (target.map (·.map CallableDatum.literal)) fun value _ => pure (.literal value)

/-- Frame a released symbolic callable without interpreting its mathematical operands.
The prepared native source validator must separately check the actual scoped operands,
selected declarations and complete endpoints before this packet is stored at a callable role.
Named descriptors retain their public row and full ordered arguments; this gate does not
invent a closed catalogue of declarations or compare the answer with the requested term. -/
opaque CallablePacket.symbolic (value : Json) : Except String CallablePacket := do
  checkServiceFields #["ctor", "args"] value
  let tag ← value.getObjValAs? String "ctor"
  let args ← (← value.getObjVal? "args").getArr?
  if tag.isEmpty then throw "a symbolic callable requires its complete public descriptor"
  if #["scopeRef", "inputRef", "resultRef", "opaqueData", "deferredData", "valueData",
      "typedMap", "finiteGraph"].contains tag then
    throw "the callable representation must use its own released admission boundary"
  if #["identity", "zero", "compose", "map"].contains tag then
    unless args.size == 2 do
      throw "a symbolic map requires both complete ordered operands"
  else if tag == "cellComponent" then
    discard <| CellComponent.decode value
  else if tag == "constructedCellComponent" then
    discard <| ConstructedCellComponent.decode value
  else if tag == "cartesianMap" then
    discard <| CartesianMap.decode value
  else if tag == "presentation" then
    let #[name, parameters, inverse] := args
      | throw "a presentation map requires its id, parameters and direction"
    if (← name.getStr?).isEmpty then throw "a presentation map has no declared id"
    discard parameters.getArr?
    discard inverse.getBool?
  else if tag == "constructionLeg" then
    let #[name, _, _, _] := args
      | throw "a construction leg requires its id, original diagram, complete result and typed index"
    if (← name.getStr?).isEmpty then throw "a construction leg has no declared limit id"
  return ⟨value⟩

/-- Frame only the existing retained-reference or export alternatives. The live reply
parser must still authenticate their exact scope position, owner and capture table. -/
opaque CallablePacket.retained (value : Json) : Except String CallablePacket := do
  checkServiceFields #["ctor", "args"] value
  if (← ScopedReference.parse? value).isSome then return ⟨value⟩
  let .opaque _ ← ComputationalValue.decode value
    | throw "a retained callable requires its original scoped reference or native export"
  return ⟨value⟩

/-- Preserve an original inline envelope around its already framed complete callable.
This checks packet containment only; it introduces no scope or native value authority. -/
opaque CallablePacket.inline (packet : CallablePacket) (value : Json) :
    Except String CallablePacket := do
  checkServiceFields #["ctor", "args"] value
  let .inline data ← ComputationalValue.decode value
    | throw "the callable wrapper is not its original inline envelope"
  unless data == packet.value do
    throw "the inline wrapper changed its complete admitted callable"
  return ⟨value⟩
/-- Retain the complete original typedMap around already framed callable data. -/
opaque CallablePacket.withMap (packet : CallablePacket) (value : Json) :
    Except String CallablePacket := do
  checkServiceFields #["ctor", "args"] value
  let map ← TypedMap.decode value
  unless map.callable == packet.value do
    throw "the callable wrapper changed its complete admitted field"
  return ⟨value⟩

/-- Read only an inventory explicitly retained in public object data. Its descriptor remains
part of that same object packet; callers authenticate the actual endpoint before using this.
Other descriptors supply no inventory here, even when a formal carrier is known to be finite. -/
partial def callableEndpointInventory (value : Json) : Except String (Option (Array Json)) := do
  match (value.getObjValAs? String "ctor").toOption with
  | some "valueData" =>
    checkServiceFields #["ctor", "args"] value
    let #[data] ← (← value.getObjVal? "args").getArr?
      | throw "valueData requires its complete actual object data"
    callableEndpointInventory data
  | some "finiteData" =>
    checkServiceFields #["ctor", "args"] value
    let #[_, inventory] ← (← value.getObjVal? "args").getArr?
      | throw "finiteData requires its complete object descriptor and actual inventory"
    let inventory ← inventory.getArr?
    CasCatalogue.GraphData.validateInventory inventory
    return some inventory
  | _ => return none

end CasRuntime
