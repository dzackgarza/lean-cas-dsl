module

public import Lean

@[expose] public section

namespace CasTools.NativeExpression

open Lean

-- Reference: Lean 4.33.0 Lean.Elab.Idbg.nameToJson/nameFromJson?. The standard
-- Name JSON instance uses dotted text and cannot preserve hygienic names.
def nameJson : Name → Json
  | .anonymous => Json.null
  | .str parent value => Json.mkObj [("str", Json.arr #[nameJson parent, toJson value])]
  | .num parent value => Json.mkObj [("num", Json.arr #[nameJson parent, toJson value])]

partial def nameFromJson (document : Json) : Except String Name := do
  if document.isNull then return .anonymous
  if let .ok value := document.getObjVal? "str" then
    let #[parent, value] ← fromJson? value | .error "native name str requires two fields"
    return .str (← nameFromJson parent) (← fromJson? value)
  if let .ok value := document.getObjVal? "num" then
    let #[parent, value] ← fromJson? value | .error "native name num requires two fields"
    return .num (← nameFromJson parent) (← fromJson? value)
  .error "invalid native name constructor"

local instance : ToJson Name := ⟨nameJson⟩
local instance : FromJson Name := ⟨nameFromJson⟩

deriving instance ToJson, FromJson for LevelMVarId
deriving instance ToJson, FromJson for Level
deriving instance ToJson, FromJson for BinderInfo
deriving instance ToJson, FromJson for Literal
deriving instance ToJson, FromJson for String.Pos.Raw
deriving instance ToJson, FromJson for Substring.Raw
deriving instance ToJson, FromJson for SourceInfo
deriving instance ToJson, FromJson for Syntax.Preresolved
deriving instance ToJson, FromJson for Syntax
deriving instance ToJson, FromJson for DataValue
deriving instance ToJson, FromJson for KVMap

/-- One exact native constructor. Child expressions are earlier node indices.
Reference: Lean.Elab.Idbg.exprToJson/exprFromJson?; retain metadata through the native
DataValue, Syntax and SourceInfo constructors instead of quotienting it. -/
inductive Node where
  | bvar (index : Nat)
  | fvar (name : Name)
  | mvar (name : Name)
  | sort (level : Level)
  | const (name : Name) (levels : List Level)
  | app (function argument : Nat)
  | lam (name : Name) (type body : Nat) (info : BinderInfo)
  | forallE (name : Name) (type body : Nat) (info : BinderInfo)
  | letE (name : Name) (type value body : Nat) (nondep : Bool)
  | lit (value : Literal)
  | mdata (data : MData) (body : Nat)
  | proj (name : Name) (index body : Nat)
  deriving ToJson, FromJson

structure Builder where
  indices : ExprStructMap Nat := {}
  nodes : Array Node := #[]

-- Native expression annotation equality treats some metadata fields extensionally.
-- Encode the full ordered metadata payload in the cache key, retaining the actual native
-- metadata in Node.mdata. Expr.replace uses the core pointer cache and preserves sharing.
-- Reference: Lean.Util.ReplaceExpr.replace; Lean.Expr.ExprStructEq; native derived JSON codecs.
partial def metadataKey (expression : Expr) : Expr :=
  expression.replace fun node => match node with
    | .mdata data body => some (.mdata
      (KVMap.empty.setString `nativeMetadata (toJson data).compress) (metadataKey body))
    | _ => none

partial def Builder.add (expression : Expr) : StateM Builder Nat := do
  let key := metadataKey expression
  if let some index := (← get).indices[ExprStructEq.mk key]? then return index
  let node : Node ← match expression with
    | .bvar index => pure (.bvar index)
    | .fvar id => pure (.fvar id.name)
    | .mvar id => pure (.mvar id.name)
    | .sort level => pure (.sort level)
    | .const name levels => pure (.const name levels)
    | .app function argument => pure (.app (← Builder.add function) (← Builder.add argument))
    | .lam name type body info =>
      pure (.lam name (← Builder.add type) (← Builder.add body) info)
    | .forallE name type body info =>
      pure (.forallE name (← Builder.add type) (← Builder.add body) info)
    | .letE name type value body nondep =>
      pure (.letE name (← Builder.add type) (← Builder.add value) (← Builder.add body) nondep)
    | .lit value => pure (.lit value)
    | .mdata data body => pure (.mdata data (← Builder.add body))
    | .proj name index body => pure (.proj name index (← Builder.add body))
  let index := (← get).nodes.size
  modify fun state => { state with
    indices := state.indices.insert ⟨key⟩ index
    nodes := state.nodes.push node }
  return index

def Builder.finish (builder : Builder) (roots : Array Nat) : Json :=
  Json.mkObj [("roots", toJson roots), ("nodes", toJson builder.nodes)]

/-- Encode a collection of native terms without expanding their shared subterms. -/
def encode (expressions : Array Expr) : Json :=
  let (roots, builder) := (expressions.mapM Builder.add).run {}
  builder.finish roots

/-- Decode only topological references. Native constructors restore every stored field. -/
def decodeNodes (document : Json) : Except String (Array Expr) := do
  let nodes ← document.getObjValAs? (Array Node) "nodes"
  let mut values : Array Expr := #[]
  for node in nodes do
    let available := values
    let child (index : Nat) : Except String Expr :=
      match available[index]? with
      | some value => .ok value
      | none => .error "native graph has a forward or cyclic reference"
    let value : Expr ← match node with
      | .bvar index => pure (.bvar index)
      | .fvar name => pure (.fvar ⟨name⟩)
      | .mvar name => pure (.mvar ⟨name⟩)
      | .sort level => pure (.sort level)
      | .const name levels => pure (.const name levels)
      | .app function argument => pure (.app (← child function) (← child argument))
      | .lam name type body info => pure (.lam name (← child type) (← child body) info)
      | .forallE name type body info => pure (.forallE name (← child type) (← child body) info)
      | .letE name type value body nondep =>
        pure (.letE name (← child type) (← child value) (← child body) nondep)
      | .lit value => pure (.lit value)
      | .mdata data body => pure (.mdata data (← child body))
      | .proj name index body => pure (.proj name index (← child body))
    values := values.push value
  return values

def decode (document : Json) : Except String (Array Expr) := do
  let roots ← document.getObjValAs? (Array Nat) "roots"
  let values ← decodeNodes document
  roots.mapM fun index => match values[index]? with
    | some value => .ok value
    | none => .error "native graph root is outside its node table"

end CasTools.NativeExpression
