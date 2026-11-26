module

public import Lean
import Init.Dynamic

@[expose] public section

namespace CasTools.NativeExpression

open Lean

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
  deriving ToJson, FromJson, Inhabited

private structure SnapshotDocumentsImpl where
  indices : ExprStructMap Nat := {}
  nodes : Array Node := #[]
  documents : Std.HashMap (Name × UInt64) (Array (Dynamic × Json)) := {}

opaque SnapshotDocumentsType : NonemptyType.{0} :=
  ⟨SnapshotDocumentsImpl, ⟨{}⟩⟩

def SnapshotDocuments : Type := SnapshotDocumentsType.type

private instance : Nonempty SnapshotDocuments := SnapshotDocumentsType.property

private unsafe def emptySnapshotDocumentsImpl : SnapshotDocuments :=
  unsafeCast ({} : SnapshotDocumentsImpl)

@[implemented_by emptySnapshotDocumentsImpl]
opaque emptySnapshotDocuments : SnapshotDocuments

structure Builder where
  indices : ExprStructMap Nat := {}
  nodes : Array Node := #[]
  snapshotDocuments : SnapshotDocuments := emptySnapshotDocuments

private unsafe def Builder.validSnapshotDocuments (state : Builder) : SnapshotDocumentsImpl :=
  let documents : SnapshotDocumentsImpl := unsafeCast state.snapshotDocuments
  if ptrEq documents.indices state.indices && ptrEq documents.nodes state.nodes then
    documents
  else
    { indices := state.indices, nodes := state.nodes }

private unsafe def Builder.memoSnapshot {α : Type} [TypeName α]
    (kind : Name) (owner : α) (encode : StateM Builder Json) : StateM Builder Json := do
  let slot := (kind, (ptrAddrUnsafe owner).toUInt64)
  let state ← get
  let documents := state.validSnapshotDocuments
  set { state with snapshotDocuments := unsafeCast documents }
  for (original, document) in documents.documents[slot]?.getD #[] do
    if let some original := Dynamic.get? α original then
      if ptrEq original owner then return document
  let document ← encode
  let state ← get
  let documents := state.validSnapshotDocuments
  let entries := documents.documents[slot]?.getD #[]
  let documents := { documents with
    documents := documents.documents.insert slot (entries.push (Dynamic.mk owner, document)) }
  set { state with snapshotDocuments := unsafeCast documents }
  return document

partial def metadataKey (expression : Expr) : Expr :=
  expression.replace fun node => match node with
    | .mdata data body => some (.mdata
      (KVMap.empty.setString `nativeMetadata (toJson data).compress) (metadataKey body))
    | _ => none

private def Builder.appendReference (key : Expr) (node : Node) : StateM Builder Nat := do
  let state ← get
  let index := state.nodes.size
  set { state with
    indices := state.indices.insert ⟨key⟩ index
    nodes := state.nodes.push node }
  return index

private unsafe def Builder.appendCached (key : Expr) (node : Node) : StateM Builder Nat :=
  fun state =>
    let documents := (state.validSnapshotDocuments).documents
    let ⟨indices, nodes, _⟩ := state
    let index := nodes.size
    let indices := indices.insert ⟨key⟩ index
    let nodes := nodes.push node
    let snapshotDocuments : SnapshotDocumentsImpl := { indices, nodes, documents }
    (index, { indices, nodes, snapshotDocuments := unsafeCast snapshotDocuments })

private partial def Builder.addWith (append : Expr → Node → StateM Builder Nat)
    (expression : Expr) : StateM Builder Nat :=
  go expression (metadataKey expression)
where
  go (expression key : Expr) : StateM Builder Nat := do
    if let some index := (← get).indices[ExprStructEq.mk key]? then return index
    let node : Node ← match expression, key with
      | .bvar index, .bvar _ => pure (.bvar index)
      | .fvar id, .fvar _ => pure (.fvar id.name)
      | .mvar id, .mvar _ => pure (.mvar id.name)
      | .sort level, .sort _ => pure (.sort level)
      | .const name levels, .const .. => pure (.const name levels)
      | .app function argument, .app functionKey argumentKey =>
        pure (.app (← go function functionKey) (← go argument argumentKey))
      | .lam name type body info, .lam _ typeKey bodyKey _ =>
        pure (.lam name (← go type typeKey) (← go body bodyKey) info)
      | .forallE name type body info, .forallE _ typeKey bodyKey _ =>
        pure (.forallE name (← go type typeKey) (← go body bodyKey) info)
      | .letE name type value body nondep, .letE _ typeKey valueKey bodyKey _ =>
        pure (.letE name (← go type typeKey) (← go value valueKey)
          (← go body bodyKey) nondep)
      | .lit value, .lit _ => pure (.lit value)
      | .mdata data body, .mdata _ bodyKey =>
        pure (.mdata data (← go body bodyKey))
      | .proj name index body, .proj _ _ bodyKey =>
        pure (.proj name index (← go body bodyKey))
      | _, _ =>

        unreachable!
    append key node

private unsafe def Builder.addCached (expression : Expr) : StateM Builder Nat :=
  Builder.addWith Builder.appendCached expression

@[implemented_by Builder.addCached]
opaque Builder.add (expression : Expr) : StateM Builder Nat :=
  Builder.addWith Builder.appendReference expression

def Builder.finish (builder : Builder) (roots : Array Nat) : Json :=
  Json.mkObj [("roots", toJson roots), ("nodes", toJson builder.nodes)]

def encode (expressions : Array Expr) : Json :=
  let (roots, builder) := (expressions.mapM Builder.add).run {}
  builder.finish roots

def constantInfoJson [Monad m] (encode : Expr → m Nat) (info : ConstantInfo) : m Json := do
  let common := [("name", nameJson info.name),
    ("universeParams", Json.arr (info.levelParams.toArray.map nameJson)),
    ("type", toJson (← encode info.type))]
  let names : List Name → Json := fun values => Json.arr (values.toArray.map nameJson)
  let fields ← match info with
    | .axiomInfo value =>
      pure [("kind", toJson "axiom"), ("unsafe", toJson value.isUnsafe)]
    | .defnInfo value => do
      let hints := match value.hints with
        | .opaque => Json.arr #[toJson "opaque"]
        | .abbrev => Json.arr #[toJson "abbrev"]
        | .regular height => Json.arr #[toJson "regular", toJson height.toNat]
      let safety := match value.safety with
        | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"
      pure [("kind", toJson "definition"), ("value", toJson (← encode value.value)),
        ("hints", hints), ("safety", toJson safety), ("all", names value.all)]
    | .thmInfo value =>
      pure [("kind", toJson "theorem"), ("value", toJson (← encode value.value)),
        ("all", names value.all)]
    | .opaqueInfo value =>
      pure [("kind", toJson "opaque"), ("value", toJson (← encode value.value)),
        ("unsafe", toJson value.isUnsafe), ("all", names value.all)]
    | .inductInfo value =>
      pure [("kind", toJson "inductive"), ("parameters", toJson value.numParams),
        ("indices", toJson value.numIndices), ("all", names value.all),
        ("constructors", names value.ctors), ("nested", toJson value.numNested),
        ("recursive", toJson value.isRec), ("unsafe", toJson value.isUnsafe),
        ("reflexive", toJson value.isReflexive)]
    | .ctorInfo value =>
      pure [("kind", toJson "constructor"), ("inductive", nameJson value.induct),
        ("index", toJson value.cidx), ("parameters", toJson value.numParams),
        ("fields", toJson value.numFields), ("unsafe", toJson value.isUnsafe)]
    | .recInfo value => do
      let rules ← value.rules.toArray.mapM fun rule => do
        pure <| Json.mkObj [("constructor", nameJson rule.ctor),
          ("fields", toJson rule.nfields), ("rhs", toJson (← encode rule.rhs))]
      pure [("kind", toJson "recursor"), ("all", names value.all),
        ("parameters", toJson value.numParams), ("indices", toJson value.numIndices),
        ("motives", toJson value.numMotives), ("minors", toJson value.numMinors),
        ("rules", Json.arr rules), ("k", toJson value.k), ("unsafe", toJson value.isUnsafe)]
    | .quotInfo value =>
      let kind := match value.kind with
        | .type => "type" | .ctor => "constructor" | .lift => "lift" | .ind => "induction"
      pure [("kind", toJson "quotient"), ("quotientKind", toJson kind)]
  return Json.mkObj (common ++ fields)

def encodeWithDeclarations (expressions : Array Expr) (declarations : Array ConstantInfo) :
    Json := Id.run do
  if declarations.isEmpty then return encode expressions
  let build : StateM Builder (Array Nat × Array Json) := do
    let roots ← expressions.mapM Builder.add
    let declarations ← declarations.mapM (constantInfoJson Builder.add)
    return (roots, declarations)
  let ((roots, declarations), builder) := build.run {}
  return Json.mkObj [("roots", toJson roots), ("nodes", toJson builder.nodes),
    ("declarations", Json.arr declarations)]

def valueDeclarationFromJson (document : Json) (expressions : Array Expr) :
    Except String Declaration := do
  let name ← document.getObjValAs? Name "name"
  let levelParams ← document.getObjValAs? (List Name) "universeParams"
  let expression (field : String) : Except String Expr := do
    let index ← document.getObjValAs? Nat field
    let some value := expressions[index]?
      | .error "a native declaration refers outside its shared expression graph"
    return value
  let type ← expression "type"
  let value ← expression "value"
  let all ← document.getObjValAs? (List Name) "all"
  let constant : ConstantVal := { name, levelParams, type }
  match ← document.getObjValAs? String "kind" with
  | "definition" =>
    let safety ← match ← document.getObjValAs? String "safety" with
      | "safe" => pure DefinitionSafety.safe
      | "unsafe" => pure DefinitionSafety.unsafe
      | "partial" => pure DefinitionSafety.partial
      | _ => .error "a native definition has an invalid safety constructor"
    let hints ← match ← document.getObjVal? "hints" with
      | .arr #[.str "opaque"] => pure ReducibilityHints.opaque
      | .arr #[.str "abbrev"] => pure ReducibilityHints.abbrev
      | .arr #[.str "regular", height] => do
        let height ← (fromJson? height : Except String Nat)
        if height > 4294967295 then
          throw "a native reducibility height is outside UInt32"
        pure (ReducibilityHints.regular height.toUInt32)
      | _ => .error "a native definition has invalid reducibility hints"
    return .defnDecl { toConstantVal := constant, value, hints, safety, all }
  | "theorem" => return .thmDecl { toConstantVal := constant, value, all }
  | "opaque" =>
    let isUnsafe ← document.getObjValAs? Bool "unsafe"
    return .opaqueDecl { toConstantVal := constant, value, isUnsafe, all }
  | _ => .error "the stored native declaration is not a value declaration"

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
