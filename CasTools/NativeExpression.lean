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
  deriving ToJson, FromJson, Inhabited

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

/-- Normalize each complete supplied root once, retaining exact native metadata
and the same child-before-parent interning order. Descending through the
corresponding children of the original and normalized key avoids renormalizing
the entire shared subtree for every child visited. -/
partial def Builder.add (expression : Expr) : StateM Builder Nat :=
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
        -- This branch cannot arise from metadataKey, which changes only
        -- metadata payloads. An internal invariant violation is not a node.
        unreachable!
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

/-- Encode the complete native declaration payload using the caller's existing expression
table. The same serializer serves exact snapshots and the typed canonical table; it never
substitutes an axiom for a definition or evaluates the declaration's value. -/
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

/-- Retain local native definitions beside the same shared expression graph. An empty
declaration closure uses the original document exactly. Decode still returns the original
ordered roots; declaration type/value indices refer to this same graph's node table. -/
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

/-- Reconstruct a stored native value declaration from the shared exact expression graph.
This is a codec, not an admission: callers must use the native kernel's declaration checker.
Ambient axioms and inductive families have no value-declaration replay through this API. -/
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
