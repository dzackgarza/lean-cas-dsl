module

public import CasCompiler.Elaborate
public import CasContract.Failure
import Lean.Meta.Transform
import Lean.Meta.Reduce

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
  -- A selected construction is part of this same original owner. Its whole presentation,
  -- diagram and interface are typed fields; abstraction transports every actual parameter.
  -- Ordinary owners add no metadata or fields and keep the existing envelope unchanged.
  if let some limit := category.limit then
    data := data.setString `CasCompiler.source.typeOrigin.limit.row limit.row
    data := data.setName `CasCompiler.source.typeOrigin.limit.declaration limit.declaration
    data := data.setBool `CasCompiler.source.typeOrigin.limit.colimit limit.colimit
    data := data.setString `CasCompiler.source.typeOrigin.limit.category
      (toJson limit.category).compress
    data := data.setBool `CasCompiler.source.typeOrigin.limit.standardization
      limit.interface.standardization.isSome
    data := data.setBool `CasCompiler.source.typeOrigin.limit.dataConstructor
      limit.interface.dataConstructor.isSome
    fields := fields ++ #[limit.cone, limit.bundle, limit.presentation, limit.diagram,
      limit.interface.presentation, limit.interface.diagram] ++
      limit.interface.standardization.toArray ++ limit.interface.dataConstructor.toArray
  -- The delimiter distinguishes the original native value from an accidentally omitted
  -- optional interface field. No delimiter is added to the legacy owner-only format.
  let mut value := if category.limit.isSome then
    .mdata (KVMap.empty.setBool `CasCompiler.source.typeOrigin.limit.payload true) value
    else value
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
    let carrierEnd := 2 + (descriptor.carrier.map (fun carrier =>
      carrier.actions + carrier.comparisons) |>.getD 0)
    let limitKeys := #[`CasCompiler.source.typeOrigin.limit.row,
      `CasCompiler.source.typeOrigin.limit.declaration,
      `CasCompiler.source.typeOrigin.limit.colimit,
      `CasCompiler.source.typeOrigin.limit.category,
      `CasCompiler.source.typeOrigin.limit.standardization,
      `CasCompiler.source.typeOrigin.limit.dataConstructor]
    let hasLimit := limitKeys.any data.contains
    unless !hasLimit || limitKeys.all data.contains do
      throwError "the native source owner lost part of its selected construction"
    let standardization ← if hasLimit then do
      let some present :=
          (data.get? `CasCompiler.source.typeOrigin.limit.standardization : Option Bool)
        | throwError "the native source construction has a different standardization field"
      pure present
    else pure false
    let dataConstructor ← if hasLimit then do
      let some present :=
          (data.get? `CasCompiler.source.typeOrigin.limit.dataConstructor : Option Bool)
        | throwError "the native source construction has a different data-constructor field"
      pure present
    else pure false
    let interfaceEnd := carrierEnd + 6
    let count := if hasLimit then
      interfaceEnd + (if standardization then 1 else 0) + (if dataConstructor then 1 else 0)
      else carrierEnd
    let mut fields := #[]
    let mut body := body
    for _ in [:count] do
      unless body.isAppOfArity ``Function.const 4 do
        throwError "the native source type lost a typed provenance field"
      fields := fields.push body.getAppArgs[3]!
      body := body.getAppArgs[2]!
    if hasLimit then
      let .mdata delimiter original := body
        | throwError "the native source construction has a different typed field count"
      unless delimiter.size == 1 &&
          (delimiter.get? `CasCompiler.source.typeOrigin.limit.payload : Option Bool) == some true do
        throwError "the native source construction lost its original payload boundary"
      body := original
    let carrier ← descriptor.carrier.mapM fun carrier => do
      let names ← (Array.range carrier.identifications).mapM fun index => do
        let name := data.getName (.num `CasCompiler.source.typeOrigin.identification index)
        if name.isAnonymous then throwError "the source type lost a comparison declaration"
        return name
      return (⟨carrier.refs, carrier.target, names,
        fields.extract 2 (2 + carrier.actions),
        fields.extract (2 + carrier.actions) carrierEnd⟩ : NativeSourceCarrierSelection)
    let limit ← if hasLimit then do
      let some row := (data.get? `CasCompiler.source.typeOrigin.limit.row : Option String)
        | throwError "the native source construction has a different row field"
      let some declaration := (data.get? `CasCompiler.source.typeOrigin.limit.declaration : Option Name)
        | throwError "the native source construction has a different declaration field"
      let some colimit := (data.get? `CasCompiler.source.typeOrigin.limit.colimit : Option Bool)
        | throwError "the native source construction has a different cone role"
      let some encoded := (data.get? `CasCompiler.source.typeOrigin.limit.category : Option String)
        | throwError "the native source construction has a different category field"
      let .ok document := Json.parse encoded
        | throwError "the native source construction has malformed category data"
      let .ok (category : CategoryExpr) := fromJson? document
        | throwError "the native source construction has a different category layout"
      let interface : NativeLimitInterface := {
        presentation := fields[carrierEnd + 4]!
        diagram := fields[carrierEnd + 5]!
        standardization := if standardization then some fields[interfaceEnd]! else none
        dataConstructor := if dataConstructor then
          some fields[interfaceEnd + (if standardization then 1 else 0)]! else none }
      pure (some (⟨row, declaration, fields[carrierEnd]!, colimit, category,
        fields[carrierEnd + 1]!, fields[carrierEnd + 2]!, fields[carrierEnd + 3]!,
        interface⟩ : NativeSourceLimitSelection))
    else pure none
    let category : NativeSourceCategory :=
      ⟨.object, descriptor.category, fields[0]!, carrier, limit⟩
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

/-- Read only a parameter's explicit source mark. Equal-valued objects cannot replace the
original occurrence carried by that mark; the consumer still checks its whole carrier family. -/
opaque sourceObjectOrigin? (value : Expr) : MetaM (Option (NativeSourceCategory × Expr)) := do
  let some (category, object, body) ← sourceOwnerOrigin? `CasCompiler.source.objectOrigin value
    | return none
  unless object == body do
    throwError "the source object provenance changed its original parameter"
  return some (category, object)

-- An object supplied as a native type parameter may carry its own explicit owner
-- envelope around a previously selected carrier type. Consume only that checked
-- envelope's original object, then read the inner carrier provenance unchanged.
private partial def sourceTypeOriginCore? (type : Expr) :
    MetaM (Option NativeSourceTypeOrigin) := do
  if let some (category, object, body) ← sourceOwnerOrigin? `CasCompiler.source.typeOrigin type then
    return some ⟨category, object, body⟩
  let some (_, object) ← sourceObjectOrigin? type | return none
  sourceTypeOriginCore? object

/-- Read the typed carrier provenance emitted by annotateSourceType, including through
validated object-argument envelopes. Aliases follow their retained native definitions;
no owner is inferred from a reduced carrier or a convertible object. -/
opaque sourceTypeOrigin? (type : Expr) : MetaM (Option NativeSourceTypeOrigin) :=
  sourceTypeOriginCore? type

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
Only the temporary class arguments are viewed without those checked identity envelopes
and normalized as native types. Lean's instance search otherwise keeps ordinary carrier
definitions folded. The original source and goal remain intact, and the returned dictionary
is checked at that complete goal. No native instance body is executed as result data.
Reuse: sourceObjectOrigin?, Meta.reduce and Lean.Meta.trySynthInstance. -/
opaque trySourceInstance (type : Expr) : MetaM (LOption Expr) := do
  let type ← instantiateMVars type
  let goal ← sourceInstanceType type
  let result ← trySynthInstance goal
  let result ← match result with
    | .none => do
      -- Keep successful original dictionaries and stuck metavariable goals intact.
      -- Only a failed search at a fixed native carrier needs the definitional view.
      let arguments ← goal.getAppArgs.mapM fun argument =>
        withTransparency .all <| Meta.reduce argument (explicitOnly := false)
          (skipTypes := false) (skipProofs := true)
      trySynthInstance (mkAppN goal.getAppFn arguments)
    | result => pure result
  if let .some instanceValue := result then
    unless ← withTransparency .all <| isDefEq (← inferType instanceValue) type do
      throwError "the native instance has a different complete source goal"
  return result

/-- Isolate the synthetic goals created by an applicability read and solve them only when
that read returned actual data. Reuse Lean 4.33's `withSynthesizeImp` queue isolation and
`finally` restoration. A returned native mismatch has no data to synthesize; exceptions
from the reader or from synthesis propagate unchanged. -/
def withSynthesizeApplicable {α : Type} (read : TermElabM (Except MessageData α)) :
    TermElabM (Except MessageData α) := do
  let pendingMVarsSaved := (← get).pendingMVars
  modify fun state => { state with pendingMVars := [] }
  try
    let result : Except MessageData α ← read
    match result with
    | .error message => return .error message
    | .ok value =>
      synthesizeSyntheticMVars (postpone := .no)
      return .ok value
  finally
    modify fun state => { state with pendingMVars := state.pendingMVars ++ pendingMVarsSaved }

/-- Elaborate a native application with the original explicit and implicit positions.
The reader sees each dependent type after its preceding actual arguments have been assigned.
Only this application's registered class slots use the checked source-object inference view.
Successful slots are retired exactly as Lean's synthetic-goal resolver does; stuck slots remain
pending. The returned source spine keeps every original annotated explicit argument.
Reuse: Lean.Elab.Term.elabAppArgs and SyntheticMVars.markAsResolved's state transition. -/
private opaque nativeSourceApplicationApplicable (function : Expr) (references : Array Syntax)
    (expected : Option Expr)
    (readArgument : Nat → Expr → TermElabM (Except MessageData Expr))
    (allArguments : Bool := false) :
    TermElabM (Except MessageData (Expr × Array Expr)) := do
  let holes ← references.mapM fun _ => mkFreshExprMVar none
  let prepared ← elabAppArgs function #[] (holes.map Arg.expr) expected allArguments false
  for hole in holes do
    unless (prepared.find? (· == hole)).isSome do
      throwError "the native application lost an original explicit argument"
  let instanceSlots ← (← getMVars prepared).filterM fun slot => do
    let some declaration ← getSyntheticMVarDecl? slot | return false
    return declaration.kind matches .typeClass _
  let mut actual := #[]
  for reference in references, hole in holes do
    let value : Except MessageData Expr ← withRef reference do
      let type ← instantiateMVars (← inferType hole)
      let value ← readArgument actual.size type
      let value ← match value with
        | .ok value => pure value
        | .error message => return .error message
      unless ← isDefEq (← inferType value) type do
        return .error m!"the source argument does not match its dependent native type"
      unless ← isDefEq hole value do
        return .error m!"the source argument does not match its dependent native type"
      return .ok value
    match value with
    | .ok value => actual := actual.push value
    | .error message => return .error message
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
  return .ok (result, actual)

/-- Ordinary syntax uses the shared native application producer with Lean's implicit
argument convention. Complete published interfaces use the same producer with every
computational native position exposed, preserving the same original argument holes. -/
opaque elabSourceApplicationApplicable (function : Expr) (references : Array Syntax)
    (expected : Option Expr)
    (readArgument : Nat → Expr → TermElabM (Except MessageData Expr)) :
    TermElabM (Except MessageData (Expr × Array Expr)) :=
  nativeSourceApplicationApplicable function references expected readArgument false

/-- Ordinary native application requires every explicit applicability check to succeed.
Only the application's own argument-reader result or native type comparison can
return a mismatch. Exceptions from readers, inference and chosen instance slots propagate. -/
opaque elabSourceApplication (function : Expr) (references : Array Syntax)
    (expected : Option Expr) (readArgument : Nat → Expr → TermElabM Expr) :
    TermElabM (Expr × Array Expr) := do
  let applied ← elabSourceApplicationApplicable function references expected
    fun index type => do return .ok (← readArgument index type)
  match applied with
  | .ok value => pure value
  | .error message => throwError message

/-- A formal premise of a published application can use only a proof already in the
original native context. This boundary never asks a provider for a proof and never runs
an unregistered proof search. A missing premise is missing implementation of that call,
not malformed computational data. -/
private def sourceContextProof (domain : Expr) : TermElabM Expr := do
  let domain ← instantiateMVars domain
  if domain.hasMVar || domain.hasLevelMVar then
    throwStratum .noImplementation m!"the published premise has undetermined original source parameters {domain}"
  for declaration in ← getLCtx do
    unless ← isProp declaration.type do continue
    if ← isDefEq declaration.type domain then
      let value := mkFVar declaration.fvarId
      checkWithKernel (← mkExpectedTypeHint value domain)
      return value
  throwStratum .noImplementation m!"the published application requires its original formal premise {domain}"

/-- Apply the explicit data parameters of a complete named family. Native implicit
slots are solved by the ordinary source elaborator; explicit proof slots have no external
data position and use only an original source hypothesis. The same argument-hole producer
retains every actual expression rather than returning metavariable assignments as sources. -/
opaque applySourceDataArguments (function : Expr) (count : Nat) (expected : Option Expr)
    (readArgument : Nat → Expr → TermElabM Expr) : TermElabM Expr := do
  let (_, binders, _) ← forallMetaTelescopeReducing (← inferType function)
  let references := Array.replicate (binders.filter (·.isExplicit)).size Syntax.missing
  let next ← IO.mkRef (0 : Nat)
  let (value, _) ← elabSourceApplication function references expected fun _ domain => do
    if ← isProp domain then return ← sourceContextProof domain
    let index ← next.get
    unless index < count do
      throwStratum .malformed "the named source input is missing an explicit data parameter"
    let actual ← readArgument index domain
    next.set (index + 1)
    return actual
  unless (← next.get) == count do
    throwStratum .malformed "the named source input has extra data parameters"
  return value

/-- Apply complete computational positions of an already selected source function.
This is the same native application producer as ordinary syntax. The caller supplies
one reader per wire position; proof positions are supplied by the original source scope
and have no wire slot. Every retained operand is substituted at its exact original hole.
Native implicit positions are explicit in this complete-interface entrance. -/
opaque applySourceArguments (function : Expr) (references : Array Syntax)
    (readArgument : Nat → Expr → TermElabM Expr) : TermElabM Expr := do
  let applyAt := fun (term : Expr) (reference : Syntax)
      (read : Expr → TermElabM Expr) => do
    let applied ← nativeSourceApplicationApplicable term #[reference] none
      (fun _ domain => do return .ok (← read domain)) true
    match applied with
    | .ok (result, _) => pure result
    | .error message => throwStratum .malformed message
  let applyOne := fun (term value : Expr) =>
    applyAt term Syntax.missing (fun _ => pure value)
  let insertPremises := fun initial => do
    let mut term := initial
    repeat
      let type ← whnfR (← inferType term)
      let .forallE _ domain _ _ := type | break
      unless ← isProp domain do break
      term ← applyOne term (← sourceContextProof domain)
    return term
  let mut term := function
  for reference in references, index in [:references.size] do
    term ← insertPremises term
    term ← applyAt term reference (fun domain => readArgument index domain)
  insertPremises term

end

end CasCompiler
