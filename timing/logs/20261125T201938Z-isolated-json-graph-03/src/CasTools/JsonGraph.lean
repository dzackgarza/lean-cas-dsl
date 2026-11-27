module

public import Lean

@[expose] public section

namespace CasTools.JsonGraph

open Lean

/-- Exact JSON constructors; child indices refer only to earlier nodes. Numeric payloads
retain their original mantissa and exponent, without a floating-point conversion. -/
private inductive Node where
  | null
  | bool (value : Bool)
  | num (mantissa : Int) (exponent : Nat)
  | str (value : String)
  | arr (children : Array Nat)
  | obj (fields : Array (String × Nat))
  deriving BEq, Hashable

private def Node.toJson : Node → Json
  | .null => .arr #[.str "null"]
  | .bool value => .arr #[.str "bool", Lean.toJson value]
  | .num mantissa exponent => .arr #[.str "num", Lean.toJson mantissa, Lean.toJson exponent]
  | .str value => .arr #[.str "str", .str value]
  | .arr children => .arr #[.str "arr", Lean.toJson children]
  | .obj fields => .arr #[.str "obj", Lean.toJson fields]

private structure Builder where
  indices : Std.HashMap Node Nat := {}
  nodes : Array Node := #[]

private partial def Builder.add (document : Json) : StateM Builder Nat := do
  let node ← match document with
    | .null => pure Node.null
    | .bool value => pure (.bool value)
    | .num value => pure (.num value.mantissa value.exponent)
    | .str value => pure (.str value)
    | .arr children => do
      let indices ← children.mapM Builder.add
      pure (.arr indices)
    | .obj fields => do
      let fields ← fields.toList.toArray.mapM fun (key, value) => do
        return (key, ← Builder.add value)
      pure (.obj fields)
  if let some index := (← get).indices[node]? then return index
  let index := (← get).nodes.size
  modify fun state => { state with
    indices := state.indices.insert node index
    nodes := state.nodes.push node }
  return index

/-- Share only exactly equal serialized constructors. No source identity, native type,
selection, or provenance is inferred by this transport codec. Every event owns its table. -/
opaque encode (document : Json) : Json :=
  let (root, builder) := (Builder.add document).run {}
  Json.mkObj [("root", toJson root), ("nodes", .arr (builder.nodes.map Node.toJson))]

/-- Restore the complete immutable JSON tree with shared child values. Forward/cyclic
references, duplicate object keys, malformed constructors and missing roots are rejected. -/
def decode (document : Json) : Except String Json := do
  let fields ← document.getObj?
  unless fields.toList.length == 2 do
    throw "a JSON graph requires exactly its root and node table"
  let nodes ← document.getObjValAs? (Array Json) "nodes"
  let root ← document.getObjValAs? Nat "root"
  let mut values : Array Json := #[]
  for node in nodes do
    let available := values
    let child (index : Nat) : Except String Json :=
      match available[index]? with
      | some value => .ok value
      | none => .error "a JSON graph has a forward, cyclic or missing child reference"
    let fields ← node.getArr?
    let value ← match fields with
      | #[.str "null"] => pure Json.null
      | #[.str "bool", .bool value] => pure (.bool value)
      | #[.str "num", mantissa, exponent] => do
        let mantissa ← fromJson? mantissa
        let exponent ← fromJson? exponent
        pure (.num ⟨mantissa, exponent⟩)
      | #[.str "str", .str value] => pure (.str value)
      | #[.str "arr", indices] => do
        let indices ← (fromJson? indices : Except String (Array Nat))
        let children ← indices.mapM child
        pure (.arr children)
      | #[.str "obj", entries] => do
        let entries ← (fromJson? entries : Except String (Array (String × Nat)))
        let mut keys : Std.HashSet String := {}
        let mut fields := #[]
        for (key, index) in entries do
          if keys.contains key then
            throw "a JSON graph has a duplicate object field"
          keys := keys.insert key
          fields := fields.push (key, ← child index)
        pure (Json.mkObj fields.toList)
      | _ => throw "a JSON graph has an invalid constructor"
    values := values.push value
  match values[root]? with
  | some value => pure value
  | none => throw "a JSON graph root is outside its node table"

end CasTools.JsonGraph
