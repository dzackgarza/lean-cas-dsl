module

public import CasCompiler.Layout
public import CasRuntime.Owner
public import CasContract.Port

public section

namespace CasRuntime

open Lean CasCompiler CasCatalogue.Backend

/-- One exact record occurrence's prepared source and runtime association identity. -/
structure RecordAssociation where
  private mk ::
  id : RuntimeId .association
  program : RuntimeId .program
  occurrence : RuntimeId .occurrence
  layout : RecordLayout

/-- A consuming role retains its underlying binding and actual dependent prefix.
The recursive data keep earlier associations when an existing node fills another role.
Source: the data model's ResultBinding and dependency-ordered DataInterface contract. -/
inductive ValueBinding where
  | private direct (value : RuntimeId .value) (role : SourceLayout)
  | private atRole (binding : ValueBinding) (role : SourceLayout)
  | private inField (id : RuntimeId .association) (binding : ValueBinding) (role : SourceLayout)
      (association : RecordAssociation) (field : FieldLayout)
      (preceding : Array (Option ValueBinding))

def ValueBinding.value : ValueBinding → RuntimeId .value
  | .direct value _ => value
  | .atRole binding _ | .inField _ binding .. => binding.value

def ValueBinding.role : ValueBinding → SourceLayout
  | .direct _ role | .atRole _ role | .inField _ _ role .. => role

structure FieldInstantiation where
  private mk ::
  id : RuntimeId .association
  association : RecordAssociation
  field : FieldLayout
  preceding : Array (Option ValueBinding)

/-- Source type families are instantiated by these exact references, never decoded Lean terms. -/
def ValueBinding.instantiations : ValueBinding → Array FieldInstantiation
  | .direct .. => #[]
  | .atRole binding _ => binding.instantiations
  | .inField id binding _ association field preceding =>
    binding.instantiations.push ⟨id, association, field, preceding⟩

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

/-- Visit immutable instantiation identities, retaining distinct roles on aliased nodes.
Reference: Lean v4.33.0 Lean/Util/ForEachExpr.lean, memoized traversal of shared DAGs.
Reuse: Std.HashSet with worker-issued identities in place of expression keys. -/
private partial def ValueGraph.checkBinding (graph : ValueGraph) (binding : ValueBinding)
    (visited : Std.HashSet (RuntimeId .association)) :
    Except String (Std.HashSet (RuntimeId .association)) := do
  match binding with
  | .direct value _ =>
    unless (graph.find value).isSome do throw "the value reference is outside the visible graph"
    return visited
  | .atRole underlying _ => graph.checkBinding underlying visited
  | .inField id underlying _ association field preceding =>
    if visited.contains id then return visited
    unless id.worker == graph.worker && association.id.worker == graph.worker &&
        field.sourceIndex == preceding.size do
      throw "the field association has a foreign worker or incomplete source prefix"
    let mut visited ← graph.checkBinding underlying (visited.insert id)
    for previous in preceding do
      if let some previous := previous then visited ← graph.checkBinding previous visited
    return visited

private def ValueGraph.require (graph : ValueGraph) (binding : ValueBinding) :
    Except String ValueNode := do
  discard <| graph.checkBinding binding {}
  let some node := graph.find binding.value
    | throw "the value reference is outside the visible graph"
  return node

private structure BindingOwners where
  instantiations : Std.HashSet (RuntimeId .association) := {}
  values : Std.HashSet (RuntimeId .value) := {}
  generations : Std.HashSet ConnectionGeneration := {}
  owners : Array ConnectionGeneration := #[]

private partial def ValueGraph.bindingOwners (graph : ValueGraph) (binding : ValueBinding)
    (state : BindingOwners) : Except String BindingOwners := do
  match binding with
  | .direct value _ =>
    if state.values.contains value then return state
    let some node := graph.find value
      | throw "the value reference is outside the visible graph"
    let mut state := { state with values := state.values.insert value }
    for owner in node.owners do
      unless state.generations.contains owner do
        state := { state with
          generations := state.generations.insert owner
          owners := state.owners.push owner }
    return state
  | .atRole underlying _ => graph.bindingOwners underlying state
  | .inField id underlying _ _ field preceding =>
    if state.instantiations.contains id then return state
    let mut state ← graph.bindingOwners underlying
      { state with instantiations := state.instantiations.insert id }
    for index in field.precedingDependencies do
      let some previous := preceding[index]?
        | throw "the dependent field is missing a preceding source position"
      if let some previous := previous then
        state ← graph.bindingOwners previous state
    return state

/-- Derive dependencies from visible nodes, rather than accepting owner claims from a reply. -/
opaque ValueGraph.requiredOwners (graph : ValueGraph) (bindings : Array ValueBinding) :
    Except String (Array ConnectionGeneration) := do
  let mut visible : Std.HashSet (RuntimeId .association) := {}
  for binding in bindings do
    visible ← graph.checkBinding binding visible
  let mut state : BindingOwners := {}
  for binding in bindings do state ← graph.bindingOwners binding state
  return state.owners

/-- Retain the same node under an already prepared consuming role. -/
opaque ValueGraph.rebind (graph : ValueGraph) (binding : ValueBinding) (role : SourceLayout) :
    Except String ValueBinding := do
  discard <| graph.require binding
  if role.kind == .proof then throw "a source proof has no computational value binding"
  return match binding with
    | .atRole underlying _ => .atRole underlying role
    | _ => .atRole binding role

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
  return (⟨graph.worker, graph.nodes.insert id node, some id⟩, .direct id origin.role)

/-- Availability reads current liveness without rewriting the immutable payload. -/
def ValueGraph.isAvailable (graph : ValueGraph) (owners : OwnerRegistry)
    (binding : ValueBinding) : BaseIO Bool := do
  if owners.worker != graph.worker then return false
  let .ok dependencies := graph.requiredOwners #[binding] | return false
  owners.allAlive dependencies

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

/-- Ordered actual constructor selections; proof positions retain their formal slots.
This is record storage, not a whole-reply admission or correctness witness. -/
structure RecordPrefix where
  private mk ::
  association : RecordAssociation
  private identities : IdentitySupply
  private selections : Array (Option ValueBinding)

private def RecordPrefix.skipProofs (record : RecordPrefix) : RecordPrefix := Id.run do
  let mut selections := record.selections
  while selections.size < record.association.layout.fields.size do
    let some field := record.association.layout.fields[selections.size]? | break
    if field.field.kind != .proof then break
    selections := selections.push none
  return { record with selections }

/-- Allocate a fresh association before recording any actual field selections.
Reuse: the worker IdentitySupply and complete source-prepared RecordLayout. -/
opaque RecordPrefix.begin (supply : IdentitySupply) (program : RuntimeId .program)
    (occurrence : RuntimeId .occurrence) (layout : RecordLayout) : IO RecordPrefix := do
  unless program.worker == supply.worker && occurrence.worker == supply.worker do
    throw <| IO.userError "record preparation belongs to a different worker"
  let association : RecordAssociation := ⟨← supply.fresh .association, program, occurrence, layout⟩
  return RecordPrefix.skipProofs ⟨association, supply, #[]⟩

/-- Bind this same node at the next field and retain every preceding actual selection.
Visibility checks include the whole prefix; owner requirements follow the declared dependencies.
Reuse: CandidateResponse's operational shape check and ValueGraph reference validation. -/
opaque RecordPrefix.bind (record : RecordPrefix) (graph : ValueGraph) (value : ValueBinding) :
    IO (RecordPrefix × ValueBinding) := do
  let record := record.skipProofs
  let some prepared := record.association.layout.fields[record.selections.size]?
    | throw <| IO.userError "the complete record has no further computational field"
  let candidate ← IO.ofExcept <|
    (CandidateResponse.ofValue prepared.layout graph value).mapError IO.userError
  let binding := ValueBinding.inField (← record.identities.fresh .association)
    candidate.root prepared.layout record.association prepared.field record.selections
  discard <| IO.ofExcept <| (graph.requiredOwners #[binding]).mapError IO.userError
  return (({ record with selections := record.selections.push (some binding) }).skipProofs, binding)

/-- Finish only a complete ordered record; no component is installed in a transaction here. -/
opaque RecordPrefix.finish (record : RecordPrefix) : Except String ValuePayload := do
  let record := record.skipProofs
  unless record.selections.size == record.association.layout.fields.size do
    throw "the dependent record is missing a required computational field"
  return .product (record.selections.filterMap id)

end CasRuntime
