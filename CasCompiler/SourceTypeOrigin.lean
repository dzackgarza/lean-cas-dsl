module

public import CasCompiler.Elaborate
import Lean.Meta.Transform

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The actual object and checked whole carrier family that supply an element type. -/
structure NativeSourceElementOwner where
  category : NativeSourceCategory
  value : Expr
  evidence : Expr

@[expose] section

-- Native source syntax is data. Derive its codec from the independently owned types.
deriving instance ToJson, FromJson for CategoryId, ClassifierId, CategoryFamilyId
deriving instance ToJson, FromJson for ParameterId, ParameterOperationId, FunctorId, ConstructorId
deriving instance ToJson, FromJson for ParameterExpr
deriving instance ToJson, FromJson for EdgeRef

-- Reference: Lean.Elab.Deriving.FromToJson at Lean 4.33.0, tagged constructor encoding.
-- Its generator uses auxFunNames[0] for every mutual member; traverse the actual source
-- category/argument pair explicitly while keeping the same native data constructors.
mutual
partial def categoryJson : CategoryExpr → Json
  | .atom id => Json.mkObj [("atom", toJson id)]
  | .construct id args => Json.mkObj [("construct", toJson (id, args.map argumentJson))]
  | .familyApp id args => Json.mkObj [("familyApp", toJson (id, args))]
  | .familyTotal id => Json.mkObj [("familyTotal", toJson id)]
  | .classifierTotal id => Json.mkObj [("classifierTotal", toJson id)]
  | .refine base id => Json.mkObj [("refine", toJson (categoryJson base, id))]
  | .opaque id => Json.mkObj [("opaque", toJson id)]

partial def argumentJson : ConstructorArg → Json
  | .category category => Json.mkObj [("category", categoryJson category)]
  | .object id => Json.mkObj [("object", toJson id)]
  | .functor id => Json.mkObj [("functor", toJson id)]
end

mutual
partial def categoryFromJson (document : Json) : Except String CategoryExpr := do
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

partial def argumentFromJson (document : Json) : Except String ConstructorArg := do
  if let .ok value := document.getObjVal? "category" then
    return .category (← categoryFromJson value)
  if let .ok value := document.getObjVal? "object" then return .object (← fromJson? value)
  if let .ok value := document.getObjVal? "functor" then return .functor (← fromJson? value)
  .error "invalid source constructor argument"
end

instance : ToJson CategoryExpr := ⟨categoryJson⟩
instance : FromJson CategoryExpr := ⟨categoryFromJson⟩

structure CarrierDescriptor where
  refs : Array EdgeRef
  target : CategoryExpr
  identifications : Nat
  actions : Nat
  comparisons : Nat
  deriving ToJson, FromJson

structure OwnerDescriptor where
  category : CategoryExpr
  carrier : Option CarrierDescriptor
  deriving ToJson, FromJson

/-- The exact selected object and carrier expression carried by a source type. -/
structure NativeSourceTypeOrigin where
  category : NativeSourceCategory
  object : Expr
  type : Expr

-- The same typed owner fields travel with carrier types and with actual object parameters.
-- The marker distinguishes their consumers; neither representation infers an owner from an image.
private def annotateSourceOwner (key : Name) (category : NativeSourceCategory)
    (object value : Expr) : MetaM Expr := do
  unless category.role == .object do throwError "source provenance requires an object"
  let descriptor : OwnerDescriptor := ⟨category.expression, category.carrier.map fun carrier =>
    ⟨carrier.refs, carrier.target, carrier.identifications.size,
      carrier.actions.size, carrier.comparisons.size⟩⟩
  let mut data := KVMap.empty.setString key (toJson descriptor).compress
  let mut fields := #[category.bundle, object]
  if let some carrier := category.carrier then
    for name in carrier.identifications, index in [:carrier.identifications.size] do
      data := data.setName (.num `CasCompiler.source.typeOrigin.identification index) name
    fields := fields ++ carrier.actions ++ carrier.comparisons
  let mut value := value
  for field in fields.reverse do
    value ← mkAppM ``Function.const #[← inferType field, value, field]
  return .mdata data value

/-- Preserve carrier type provenance as typed native arguments. Native abstraction and
substitution transport every captured term; metadata contains only source syntax and names.
Reuse: Function.const, native MData/KVMap and the complete owner codec above. -/
opaque annotateSourceType (category : NativeSourceCategory) (object type : Expr) : MetaM Expr :=
  annotateSourceOwner `CasCompiler.source.typeOrigin category object type

/-- Retain the complete selected category beside its unchanged native object parameter.
The original object is both the identity wrapper's result and its typed owner field. -/
opaque annotateSourceObject (category : NativeSourceCategory) (object : Expr) : MetaM Expr :=
  annotateSourceOwner `CasCompiler.source.objectOrigin category object object

private partial def sourceOwnerOrigin? (key : Name) (value : Expr) :
    MetaM (Option (NativeSourceCategory × Expr × Expr)) := do
  match ← instantiateMVars value with
  | .mdata data body =>
    let encoded := data.getString key
    if encoded.isEmpty then return ← sourceOwnerOrigin? key body
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
      ⟨.object, descriptor.category, fields[0]!, carrier, none⟩
    unless ← isDefEq (← inferType fields[1]!)
        (← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]) do
      throwError "the native source type has a different complete owner category"
    return some (category, fields[1]!, body)
  | .letE _ _ value body _ => sourceOwnerOrigin? key (body.instantiate1 value)
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => sourceOwnerOrigin? key value
    | none => pure none
  | _ => pure none

/-- Read only the typed carrier provenance emitted by annotateSourceType.
Aliases follow their retained native definitions; source syntax is never replayed. -/
opaque sourceTypeOrigin? (type : Expr) : MetaM (Option NativeSourceTypeOrigin) := do
  return (← sourceOwnerOrigin? `CasCompiler.source.typeOrigin type).map fun
    (category, object, type) => ⟨category, object, type⟩

/-- Read only a parameter's explicit source mark. Equal-valued objects cannot replace the
original occurrence carried by that mark; the consumer still checks its whole carrier family. -/
opaque sourceObjectOrigin? (value : Expr) : MetaM (Option (NativeSourceCategory × Expr)) := do
  let some (category, object, body) ← sourceOwnerOrigin? `CasCompiler.source.objectOrigin value
    | return none
  unless object == body do
    throwError "the source object provenance changed its original parameter"
  return some (category, object)

-- Typeclass inference sees the unchanged native objects inside typed owner envelopes.
-- The source expression is not rewritten: fvars and every other metadata key stay intact.
private def sourceInstanceType (type : Expr) : MetaM Expr :=
  Meta.transform type (pre := fun expression => do
    if let .mdata data _ := expression then
      if data.contains `CasCompiler.source.objectOrigin then
        let some (_, original) ← sourceObjectOrigin? expression
          | throwError "the native instance input lost its explicit source object"
        return .visit original
    return .continue)

/-- Use native instance search at the original objects carried by explicit source owners.
Only the temporary instance goal is viewed without those checked identity envelopes;
the returned dictionary is checked at the complete retained goal. Stuck native goals
remain stuck, and failed native search is not an alternative source interpretation.
Reuse: sourceObjectOrigin?, Meta.transform and Lean.Meta.trySynthInstance. -/
opaque trySourceInstance (type : Expr) : MetaM (LOption Expr) := do
  let rawType := type
  let type ← instantiateMVars type
  let native ← sourceInstanceType type
  let hasOwner := fun (expression : Expr) => (expression.find? fun term => match term with
    | .mdata data _ => data.contains `CasCompiler.source.objectOrigin
    | _ => false).isSome
  dbg_trace "[source.instance] head={repr type.getAppFn.constName?} rawOwner={hasOwner rawType} owner={hasOwner type} nativeOwner={hasOwner native} rawMVars={rawType.hasMVar} raw={(reprStr rawType).take 1500} goal={(reprStr type).take 1500} native={(reprStr native).take 1500}"
  let result ← trySynthInstance native
  let tag := match result with | .some _ => "some" | .none => "none" | .undef => "undef"
  dbg_trace "[source.instance.result] head={repr type.getAppFn.constName?} result={tag}"
  if let .some instanceValue := result then
    unless ← isDefEq (← inferType instanceValue) type do
      throwError "the native instance has a different complete source goal"
  return result

end

end CasCompiler
