module

public import CasCompiler.Program
public import CasRuntime.Owner

public section

namespace CasRuntime

open CasCompiler

/-- A consuming role can differ from a node's producing role without replacing the node. -/
structure ValueBinding where
  private mk ::
  value : RuntimeId .value
  role : SourceLayout

inductive ValueData
  | portable (bytes : ByteArray)
  | product (fields : Array ValueBinding)
  | closure (program : RuntimeId .program) (captures : Array ValueBinding)
  | ownedToken (owner : ConnectionGeneration) (token : String) (captures : Array ValueBinding)

/-- Payload construction stamps native exports from the actual supplying connection. -/
structure ValuePayload where
  private mk ::
  data : ValueData

def ValuePayload.portable (bytes : ByteArray) : ValuePayload := ⟨.portable bytes⟩

def ValuePayload.product (fields : Array ValueBinding) : ValuePayload := ⟨.product fields⟩

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
  | .closure _ captures | .ownedToken _ _ captures => captures

def ValueNode.references (node : ValueNode) : Array ValueBinding := node.payload.data.references

/-- Persistent storage uses Lean's immutable HashMap; the live ledger holds no copy.
Reference: Lean v4.33.0 Std/Data/HashMap/Basic.lean, `HashMap.insert` and `getElem?`. -/
structure ValueGraph where
  private mk ::
  worker : String
  private nodes : Std.HashMap (RuntimeId .value) ValueNode

def ValueGraph.empty (supply : IdentitySupply) : ValueGraph := ⟨supply.worker, {}⟩

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
  let .product fields := node.payload.data
    | throw "the retained payload has no stored product fields"
  let some field := fields[index]?
    | throw "the projection is outside the retained product"
  return field

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
  | .portable _ | .product _ => pure ()
  let id ← supply.fresh .value
  let node : ValueNode := ⟨id, origin, payload, owners⟩
  return (⟨graph.worker, graph.nodes.insert id node⟩, ⟨id, origin.role⟩)

/-- Availability reads current liveness without rewriting the immutable payload. -/
def ValueGraph.isAvailable (graph : ValueGraph) (owners : OwnerRegistry)
    (binding : ValueBinding) : BaseIO Bool := do
  let some node := graph.find binding.value | return false
  if owners.worker != graph.worker then return false
  owners.allAlive node.owners

end CasRuntime
