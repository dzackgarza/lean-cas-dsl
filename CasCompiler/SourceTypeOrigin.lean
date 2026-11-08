module

public import CasCompiler.Surface

public section

namespace CasCompiler

open Lean Meta CasCatalogue

-- Native source syntax is data. Derive its codec from the independently owned types.
deriving instance ToJson, FromJson for CategoryId, ClassifierId, CategoryFamilyId
deriving instance ToJson, FromJson for ParameterId, ParameterOperationId, FunctorId, ConstructorId
deriving instance ToJson, FromJson for ParameterExpr
deriving instance ToJson, FromJson for EdgeRef

-- Reference: Lean.Elab.Deriving.FromToJson at Lean 4.33.0, tagged constructor encoding.
-- Its generator uses auxFunNames[0] for every mutual member; traverse the actual source
-- category/argument pair explicitly while keeping the same native data constructors.
mutual
private partial def categoryJson : CategoryExpr → Json
  | .atom id => Json.mkObj [("atom", toJson id)]
  | .construct id args => Json.mkObj [("construct", toJson (id, args.map argumentJson))]
  | .familyApp id args => Json.mkObj [("familyApp", toJson (id, args))]
  | .familyTotal id => Json.mkObj [("familyTotal", toJson id)]
  | .classifierTotal id => Json.mkObj [("classifierTotal", toJson id)]
  | .refine base id => Json.mkObj [("refine", toJson (categoryJson base, id))]
  | .opaque id => Json.mkObj [("opaque", toJson id)]

private partial def argumentJson : ConstructorArg → Json
  | .category category => Json.mkObj [("category", categoryJson category)]
  | .object id => Json.mkObj [("object", toJson id)]
  | .functor id => Json.mkObj [("functor", toJson id)]
end

mutual
private partial def categoryFromJson (document : Json) : Except String CategoryExpr := do
  if let .ok value := document.getObjVal? "atom" then return .atom (← fromJson? value)
  if let .ok value := document.getObjVal? "construct" then
    let (id, args) ← (fromJson? value : Except String (ConstructorId × Array Json))
    return .construct id (← args.mapM argumentFromJson)
  if let .ok value := document.getObjVal? "familyApp" then
    let (id, args) ← (fromJson? value : Except String (CategoryFamilyId × Array ParameterExpr))
    return .familyApp id args
  if let .ok value := document.getObjVal? "familyTotal" then
    return .familyTotal (← fromJson? value)
  if let .ok value := document.getObjVal? "classifierTotal" then
    return .classifierTotal (← fromJson? value)
  if let .ok value := document.getObjVal? "refine" then
    let (base, id) ← (fromJson? value : Except String (Json × ClassifierId))
    return .refine (← categoryFromJson base) id
  if let .ok value := document.getObjVal? "opaque" then return .opaque (← fromJson? value)
  .error "invalid source category constructor"

private partial def argumentFromJson (document : Json) : Except String ConstructorArg := do
  if let .ok value := document.getObjVal? "category" then
    return .category (← categoryFromJson value)
  if let .ok value := document.getObjVal? "object" then return .object (← fromJson? value)
  if let .ok value := document.getObjVal? "functor" then return .functor (← fromJson? value)
  .error "invalid source constructor argument"
end

instance : ToJson CategoryExpr := ⟨categoryJson⟩
instance : FromJson CategoryExpr := ⟨categoryFromJson⟩

private structure CarrierDescriptor where
  refs : Array EdgeRef
  target : CategoryExpr
  identifications : Nat
  actions : Nat
  comparisons : Nat
  deriving ToJson, FromJson

private structure OwnerDescriptor where
  category : CategoryExpr
  carrier : Option CarrierDescriptor
  deriving ToJson, FromJson

/-- The exact selected object and carrier expression carried by a source type. -/
structure NativeSourceTypeOrigin where
  category : NativeSourceCategory
  object : Expr
  type : Expr

/-- Preserve type provenance as typed native arguments, using Function.const's identity law.
Native abstraction/substitution transports every captured term. Metadata holds only source
syntax and declaration names; it contains no encoded expression or local-variable identity.
Reuse: Function.const, native MData/KVMap and Lean's derived JSON codecs. -/
def annotateSourceType (category : NativeSourceCategory) (object type : Expr) : MetaM Expr := do
  unless category.role == .object do throwError "source type provenance requires an object"
  let descriptor : OwnerDescriptor := ⟨category.expression, category.carrier.map fun carrier =>
    ⟨carrier.refs, carrier.target, carrier.identifications.size,
      carrier.actions.size, carrier.comparisons.size⟩⟩
  let mut data := KVMap.empty.setString `CasCompiler.source.typeOrigin (toJson descriptor).compress
  let mut fields := #[category.bundle, object]
  if let some carrier := category.carrier then
    for name in carrier.identifications, index in [:carrier.identifications.size] do
      data := data.setName (.num `CasCompiler.source.typeOrigin.identification index) name
    fields := fields ++ carrier.actions ++ carrier.comparisons
  let mut value := type
  for field in fields.reverse do
    value ← mkAppM ``Function.const #[← inferType field, value, field]
  return .mdata data value

/-- Read only the typed provenance emitted by annotateSourceType.
Reuse: Function.const's native argument layout, complete category bundles and source codecs.
Aliases follow their retained native definitions; source syntax is never replayed. -/
partial def sourceTypeOrigin? (type : Expr) : MetaM (Option NativeSourceTypeOrigin) := do
  match ← instantiateMVars type with
  | .mdata data body =>
    let encoded := data.getString `CasCompiler.source.typeOrigin
    if encoded.isEmpty then return ← sourceTypeOrigin? body
    let .ok document := Json.parse encoded
      | throwError "the native source type has malformed provenance data"
    let .ok (descriptor : OwnerDescriptor) := fromJson? document
      | throwError "the native source type has a different provenance layout"
    let count := 2 + (descriptor.carrier.map (fun carrier =>
      carrier.actions + carrier.comparisons) |>.getD 0)
    let mut fields := #[]
    let mut body := body
    for _ in [:count] do
      unless body.isAppOfArity ``Function.const 4 do
        throwError "the native source type lost a typed provenance field"
      fields := fields.push body.getAppArgs[3]!
      body := body.getAppArgs[2]!
    let carrier ← descriptor.carrier.mapM fun carrier => do
      let names ← (Array.range carrier.identifications).mapM fun index => do
        let name := data.getName (.num `CasCompiler.source.typeOrigin.identification index)
        if name.isAnonymous then throwError "the source type lost a comparison declaration"
        return name
      return (⟨carrier.refs, carrier.target, names,
        fields.extract 2 (2 + carrier.actions),
        fields.extract (2 + carrier.actions) count⟩ : NativeSourceCarrierSelection)
    let category : NativeSourceCategory :=
      ⟨.object, descriptor.category, fields[0]!, carrier⟩
    unless ← isDefEq (← inferType fields[1]!)
        (← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]) do
      throwError "the native source type has a different complete owner category"
    return some ⟨category, fields[1]!, body⟩
  | .letE _ _ value body _ => sourceTypeOrigin? (body.instantiate1 value)
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => sourceTypeOrigin? value
    | none => pure none
  | _ => pure none

end CasCompiler
