module

public import CasCompiler.Layout
public import CasRuntime.Owner
public import CasContract.Port

public section

namespace CasRuntime

open Lean CasCompiler CasCatalogue.Backend

/-- A consuming role can differ from a node's producing role without replacing the node. -/
structure ValueBinding where
  private mk ::
  value : RuntimeId .value
  role : SourceLayout

structure ContainerSlot where
  path : Array InputPathStep
  binding : ValueBinding

/-- Literal packet structure, typed substitution slots and retained field/callable bindings. -/
structure ValueContainer where
  private mk ::
  template : Json
  slots : Array ContainerSlot
  fields : Array ValueBinding
  callable : Option ValueBinding

/-- Replace only a previously located JSON position.
Reference: Lean.Json array/object operations and CasContract.Port's InputPathStep grammar. -/
private def replacePosition (json : Json) (path : List InputPathStep) (replacement : Json) :
    Except String Json := do
  match path, json with
  | [], _ => return replacement
  | .index index :: rest, .arr values =>
    let some value := values[index]? | throw "the container position is outside its array"
    return .arr (values.set! index (← replacePosition value rest replacement))
  | .field name :: rest, .obj fields =>
    let value ← json.getObjVal? name
    let value ← replacePosition value rest replacement
    return Json.mkObj (fields.toList.map fun (key, entry) =>
      (key, if key == name then value else entry))
  | _, _ => throw "the container position does not follow the retained JSON structure"

/-- A retained literal cannot carry ambient reference or native-token authority.
Reference: CasContract.Port.validateResultRefs and the runtime immediate-control JSON walk. -/
private partial def checkLiteral (json : Json) : Except String Unit := do
  if let .ok tag := json.getObjValAs? String "ctor" then
    if #["scopeRef", "inputRef", "resultRef", "opaqueData", "deferredData"].contains tag then
      throw "the container has an unbound reference, native token or deferred control"
  match json with
  | .arr entries => for entry in entries do checkLiteral entry
  | .obj entries => for (_, entry) in entries.toList do checkLiteral entry
  | _ => pure ()

private def makeContainer (template : Json) (slots : Array ContainerSlot)
    (fields : Array ValueBinding) (callable : Option ValueBinding) : Except String ValueContainer := do
  let mut paths : Array (List InputPathStep) := #[]
  let mut template := template
  for slot in slots do
    let path := slot.path.toList
    if paths.any (fun previous => previous.isPrefixOf path || path.isPrefixOf previous) then
      throw "container reference positions overlap"
    template ← replacePosition template path .null
    paths := paths.push path
  checkLiteral template
  if let some binding := callable then
    unless binding.role.kind == .function do
      throw "the container callable has no prepared function interface"
  return ⟨template, slots, fields, callable⟩

/-- Substitute freshly encoded references without rebuilding literal data from a source term. -/
opaque ValueContainer.fill (container : ValueContainer) (replacements : Array Json) :
    Except String Json := do
  unless replacements.size == container.slots.size do
    throw "container substitution does not match its exact reference arity"
  let mut packet := container.template
  for slot in container.slots, replacement in replacements do
    packet ← replacePosition packet slot.path.toList replacement
  return packet

inductive ValueData
  | portable (bytes : ByteArray)
  | product (fields : Array ValueBinding)
  | container (value : ValueContainer)
  | closure (program : RuntimeId .program) (captures : Array ValueBinding)
  | ownedToken (owner : ConnectionGeneration) (token : String) (captures : Array ValueBinding)

/-- Payload construction stamps native exports from the actual supplying connection. -/
structure ValuePayload where
  private mk ::
  data : ValueData

def ValuePayload.portable (bytes : ByteArray) : ValuePayload := ⟨.portable bytes⟩

def ValuePayload.product (fields : Array ValueBinding) : ValuePayload := ⟨.product fields⟩

opaque ValuePayload.container (template : Json) (slots : Array ContainerSlot)
    (fields : Array ValueBinding) (callable : Option ValueBinding) : Except String ValuePayload := do
  return ⟨.container (← makeContainer template slots fields callable)⟩

def ValuePayload.closure (program : RuntimeId .program)
    (captures : Array ValueBinding) : ValuePayload := ⟨.closure program captures⟩

opaque ValuePayload.ownedExport (connection : Connection) (token : String)
    (captures : Array ValueBinding) : ValuePayload :=
  ⟨.ownedToken connection.generation token captures⟩

structure ValueOrigin where
  occurrence : RuntimeId .occurrence
  program : RuntimeId .program
  role : SourceLayout

/-- A tentative immutable node; whole-reply admission and receipt publication are separate. -/
structure ValueNode where
  private mk ::
  id : RuntimeId .value
  origin : ValueOrigin
  payload : ValuePayload
  owners : Array ConnectionGeneration

private def ValueData.references : ValueData → Array ValueBinding
  | .portable _ => #[]
  | .product fields => fields
  | .container value => value.slots.map (·.binding) ++ value.fields ++
      match value.callable with | none => #[] | some binding => #[binding]
  | .closure _ captures | .ownedToken _ _ captures => captures

def ValueNode.references (node : ValueNode) : Array ValueBinding := node.payload.data.references

/-- Persistent storage uses Lean's immutable HashMap; the live ledger holds no copy.
Reference: Lean v4.33.0 Std/Data/HashMap/Basic.lean, `HashMap.insert` and `getElem?`. -/
structure ValueGraph where
  private mk ::
  worker : String
  private nodes : Std.HashMap (RuntimeId .value) ValueNode
  private revision : Option (RuntimeId .value)

def ValueGraph.empty (supply : IdentitySupply) : ValueGraph := ⟨supply.worker, {}, none⟩

/-- Each append has a fresh node identity, so an append-only graph has an exact revision.
Reference: the existing IdentitySupply monotone allocation and persistent HashMap insertion. -/
def ValueGraph.sameRevision (left right : ValueGraph) : Bool :=
  left.worker == right.worker && left.revision == right.revision

def ValueGraph.find (graph : ValueGraph) (id : RuntimeId .value) : Option ValueNode :=
  graph.nodes[id]?

private def ValueGraph.require (graph : ValueGraph) (binding : ValueBinding) :
    Except String ValueNode := do
  let some node := graph.find binding.value
    | throw "the value reference is outside the visible graph"
  return node

/-- Derive dependencies from visible nodes, rather than accepting owner claims from a reply. -/
opaque ValueGraph.requiredOwners (graph : ValueGraph) (bindings : Array ValueBinding) :
    Except String (Array ConnectionGeneration) := do
  let mut owners : Array ConnectionGeneration := #[]
  let mut seen : Std.HashSet ConnectionGeneration := {}
  for binding in bindings do
    let node ← graph.require binding
    for owner in node.owners do
      unless seen.contains owner do
        seen := seen.insert owner
        owners := owners.push owner
  return owners

/-- Retain the same node under an already prepared consuming role. -/
opaque ValueGraph.rebind (graph : ValueGraph) (binding : ValueBinding) (role : SourceLayout) :
    Except String ValueBinding := do
  discard <| graph.require binding
  if role.kind == .proof then throw "a source proof has no computational value binding"
  return ⟨binding.value, role⟩

/-- Projection returns the stored field binding, independently of unrelated field owners. -/
opaque ValueGraph.project (graph : ValueGraph) (binding : ValueBinding) (index : Nat) :
    Except String ValueBinding := do
  let node ← graph.require binding
  match node.payload.data with
  | .product fields =>
    let some field := fields[index]?
      | throw "the projection is outside the retained product"
    return field
  | .container value =>
    let some field := value.fields[index]?
      | throw "the projection is outside the retained container"
    return field
  | _ => throw "the retained payload has no stored product fields"

/-- Follow stored callable slots to actual code/token data, retaining the complete outer value.
The append-only graph supplies existing references; no source expression reconstructs a callable.
Reuse: ValueGraph.require and Lean v4.33.0 Std.HashSet for exact reference traversal. -/
private partial def storedCallable (graph : ValueGraph) (binding : ValueBinding)
    (visited : Std.HashSet (RuntimeId .value)) : Except String ValueBinding := do
  if visited.contains binding.value then throw "the retained callable references form a cycle"
  let node ← graph.require binding
  match node.payload.data with
  | .closure .. | .ownedToken .. => return binding
  | .container value =>
    let some callable := value.callable | throw "the container has no stored callable"
    storedCallable graph callable (visited.insert binding.value)
  | .portable _ | .product _ => throw "the retained payload has no callable code or token"

opaque ValueGraph.callable (graph : ValueGraph) (binding : ValueBinding) :
    Except String ValueBinding := storedCallable graph binding {}

/-- Stage one node without modifying the prior graph or creating a completion witness.
References must already be visible; ownership is derived from those exact nodes and the
actual supplying connection. Payload equality never participates in node allocation. -/
opaque ValueGraph.stage (graph : ValueGraph) (supply : IdentitySupply)
    (origin : ValueOrigin) (payload : ValuePayload) : IO (ValueGraph × ValueBinding) := do
  unless supply.worker == graph.worker && origin.program.worker == graph.worker &&
      origin.occurrence.worker == graph.worker do
    throw <| IO.userError "value staging belongs to a different worker"
  if origin.role.kind == .proof then
    throw <| IO.userError "a source proof has no computational payload"
  let mut owners ← IO.ofExcept <|
    (graph.requiredOwners payload.data.references).mapError IO.userError
  match payload.data with
  | .ownedToken owner _ _ =>
    unless owner.worker == graph.worker do
      throw <| IO.userError "the supplying connection belongs to a different worker"
    unless owners.contains owner do owners := owners.push owner
  | .closure program _ =>
    unless program.worker == graph.worker do
      throw <| IO.userError "the closure program belongs to a different worker"
  | .portable _ | .product _ | .container _ => pure ()
  let id ← supply.fresh .value
  let node : ValueNode := ⟨id, origin, payload, owners⟩
  return (⟨graph.worker, graph.nodes.insert id node, some id⟩, ⟨id, origin.role⟩)

/-- Availability reads current liveness without rewriting the immutable payload. -/
def ValueGraph.isAvailable (graph : ValueGraph) (owners : OwnerRegistry)
    (binding : ValueBinding) : BaseIO Bool := do
  let some node := graph.find binding.value | return false
  if owners.worker != graph.worker then return false
  owners.allAlive node.owners

/-- A computational candidate indexed by its prepared layout, retaining its actual root. -/
structure CandidateResponse (source : SourceLayout) where
  private mk ::
  root : ValueBinding

/-- Check the retained operational shape and bind the prepared source role.
Source: execution contract v2 §2 and data model §5. Scope, lifecycle and whole-reply admission
are separate boundaries. Native exports retain lazy field access through their actual root. -/
opaque CandidateResponse.ofValue (source : SourceLayout) (graph : ValueGraph)
    (value : ValueBinding) : Except String (CandidateResponse source) := do
  let node ← graph.require value
  match source.kind, node.payload.data with
  | .proof, _ => throw "a source proof has no computational response"
  | .function, .closure _ _ | .function, .ownedToken _ _ _ => pure ()
  | .function, .container _ => discard <| graph.callable value
  | .function, _ => throw "the candidate has no retained callable payload"
  | .record, .product fields =>
    let expected := source.fields.filter (·.wireIndex.isSome)
    unless fields.size == expected.size do
      throw "the candidate record does not match its prepared field arity"
  | .record, .container container =>
    let expected := source.fields.filter (·.wireIndex.isSome)
    unless container.fields.size == expected.size do
      throw "the candidate container does not match its prepared field arity"
  | .record, .closure _ _ | .record, .ownedToken _ _ _ => pure ()
  | .record, _ => throw "the candidate has no retained record interface"
  | .data, _ | .typeValue, _ => pure ()
  return ⟨← graph.rebind value source⟩

end CasRuntime
