module

public import CasCompiler.Elaborate
import Lean.Meta.Transform

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

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
  let type ← instantiateMVars type
  let result ← trySynthInstance (← sourceInstanceType type)
  if let .some instanceValue := result then
    unless ← isDefEq (← inferType instanceValue) type do
      throwError "the native instance has a different complete source goal"
  return result

/-- Elaborate a native application with the original explicit and implicit positions.
The reader sees each dependent type after its preceding actual arguments have been assigned.
Only this application's registered class slots use the checked source-object inference view.
Successful slots are retired exactly as Lean's synthetic-goal resolver does; stuck slots remain
pending. The returned source spine keeps every original annotated explicit argument.
Reuse: Lean.Elab.Term.elabAppArgs and SyntheticMVars.markAsResolved's state transition. -/
opaque elabSourceApplication (function : Expr) (references : Array Syntax)
    (expected : Option Expr) (readArgument : Nat → Expr → TermElabM Expr) :
    TermElabM (Expr × Array Expr) := do
  let holes ← references.mapM fun _ => mkFreshExprMVar none
  let prepared ← elabAppArgs function #[] (holes.map Arg.expr) expected false false
  for hole in holes do
    unless (prepared.find? (· == hole)).isSome do
      throwError "the native application lost an original explicit argument"
  let instanceSlots ← (← getMVars prepared).filterM fun slot => do
    let some declaration ← getSyntheticMVarDecl? slot | return false
    return declaration.kind matches .typeClass _
  let mut actual := #[]
  for reference in references, hole in holes do
    let value ← withRef reference do
      let type ← instantiateMVars (← inferType hole)
      let value ← readArgument actual.size type
      unless ← isDefEq hole value do
        throwError "the source argument does not match its dependent native type"
      return value
    actual := actual.push value
  for slot in instanceSlots do
    let solved ← slot.withContext do
      let type ← instantiateMVars (← slot.getType)
      match ← trySourceInstance type with
      | .some instanceValue =>
        if ← slot.isAssigned then
          let previous ← instantiateMVars (mkMVar slot)
          unless ← isDefEq previous instanceValue do
            if (← containsPendingMVar previous <||> containsPendingMVar instanceValue) then
              return false
            throwError "the native application changed its original instance slot"
        else
          unless ← isDefEq (mkMVar slot) instanceValue do
            throwError "the native application could not retain its original instance slot"
        return true
      | .undef => return false
      | .none => do
        discard <| throwFailedToSynthesize type
        return false
    if solved then
      -- Assigning the dictionary alone leaves Lean's registered goal queued for another
      -- search at its wrapped type. Retire only this successfully checked original slot;
      -- the native pending-goal loop removes its queued ID through the ordinary path.
      modify fun state => { state with syntheticMVars := state.syntheticMVars.erase slot }
  let result := prepared.replace fun expression =>
    (holes.findIdx? (· == expression)).bind fun index => actual[index]?
  check result
  return (result, actual)

end

end CasCompiler
