module

public import CasCompiler.SelectionData

public import Init.Control.StateCps
public import CasCompiler.Elaborate
public import CasCompiler.Layout
public import CasCompiler.SelectedField
public import CasContract.Failure
import Lean.Meta.Transform
import Lean.Meta.Reduce

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue


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

private def checkSourceConstruction (category : NativeSourceCategory) (object : Expr) :
    SourceReadM Unit := do
  let original ← SourceReadM.selection? object
  let construction := original.bind fun selected => selected.limit.map (·.source)
  let categorized := original.bind fun selected => selected.category.bind (·.limit)
  let same := fun (left right : Option NativeSourceLimitSelection) =>
    SourceSelection.exactlyMatches Expr.equal
      ({ value := object, category := some { category with limit := left } } : SourceSelection Expr)
      ({ value := object, category := some { category with limit := right } } : SourceSelection Expr)
  if construction.isSome && categorized.isSome && !same construction categorized then
    liftM (m := TermElabM) <| throwError (MessageData.tagged
      `CasCompiler.sourceOwner.constructionMismatch
      m!"a source owner changed its original selected construction")
  unless same category.limit (construction <|> categorized) do
    liftM (m := TermElabM) <| throwError (MessageData.tagged
      `CasCompiler.sourceOwner.constructionMismatch
      m!"a source owner changed its original selected construction")

/-- Retain an authored native structure constructor and every original field occurrence.
Only the supplied constructor syntax gives its positions; no native definition is unfolded.
A consuming type uses the same checked source correspondence without replacing the constructor. -/
opaque retainSourceConstructor (value : Expr) (declaredType : Option Expr := none) :
    SourceReadM Expr := do
  let native := value.consumeMData
  let .const declaration _ := native.getAppFn | return value
  let environment ← liftM (m := CoreM) getEnv
  let some (.ctorInfo constructor) := environment.find? declaration | return value
  unless (getStructureInfo? environment constructor.induct).isSome do return value
  unless native.getAppNumArgs == constructor.numParams + constructor.numFields do
    liftM (m := TermElabM) <| throwError "the native source constructor lost an original field position"
  check value
  let selection ← liftM (m := MetaM) <| mkFreshUserName `sourceNativeRecord
  SourceReadM.select { value, recordSelection := some selection } declaredType

/-- A projection transports only its own authored constructor field's complete selection.
The exact owner binding, declared projection, and original field ordinal are authoritative. -/
opaque retainSourceProjection? (value : Expr) :
    SourceReadM (Option NativeSourceJudgement) := do
  let some projection ← SourceProjection.ofExpr? value | return none
  let some owner ← SourceReadM.selection? projection.parent | return none
  let some selection := owner.recordSelection | return none
  if owner.application.isSome then return none
  let constructor ← liftM (m := MetaM) <| getConstInfoCtor projection.info.ctorName
  let native := owner.value.consumeMData
  unless native.getAppFn.constName? == some constructor.name &&
      native.getAppNumArgs == constructor.numParams + constructor.numFields &&
      projection.info.i < constructor.numFields do return none
  let component := native.getAppArgs[constructor.numParams + projection.info.i]!
  let some selected ← SourceReadM.selection? component | return none
  let field ← selectedFieldAt selection projection.declaration projection.parent value
  let result ← SourceReadM.select { selected with value, field := field.field }
  return some ⟨result, selected.category⟩

/-- Retain the actual complete selected object and its carrier in typed source data. -/
opaque annotateSourceType (category : NativeSourceCategory) (object type : Expr) :
    SourceReadM Expr := do
  unless category.role == .object do
    liftM (m := TermElabM) <| throwError "source provenance requires an object"
  checkSourceConstruction category object
  SourceReadM.select { value := type, typeOrigin := some ⟨category, object, type⟩ }

/-- A native object parameter keeps the same complete selected record at its exact binder. -/
opaque annotateSourceObject (category : NativeSourceCategory) (object : Expr) :
    SourceReadM Expr := do
  unless category.role == .object do
    liftM (m := TermElabM) <| throwError "source provenance requires an object"
  checkSourceConstruction category object
  let selected := (← SourceReadM.selection? object).getD { value := object }
  SourceReadM.select { selected with value := object, category := some category }

/-- Only the exact selected binder supplies an object owner; native aliases and equal
carriers cannot recover a missing selection. Authored aliases copy their record on entry. -/
opaque sourceObjectOrigin? (value : Expr) :
    SourceReadM (Option (NativeSourceCategory × Expr)) := do
  let some selected ← SourceReadM.selection? value | return none
  let some category := selected.category | return none
  if category.role == .object then return some (category, value)
  return none

/-- Read the complete type owner stored by the source producer at this exact binding. -/
opaque sourceTypeOrigin? (type : Expr) : SourceReadM (Option NativeSourceTypeOrigin) := do
  return (← SourceReadM.selection? type).bind (·.typeOrigin)

/-- Native instance search retains its original selected local dictionaries. Source readers
supply any typed original-source correspondence explicitly at their scoped application boundary;
the native lookup performs no selection recovery from expression annotations or carrier types. -/
opaque trySourceInstance (type : Expr) : MetaM (LOption Expr) := do
  let type ← instantiateMVars type
  let result ← trySynthInstance type
  let result ← match result with
    | .none => do
      let arguments ← type.getAppArgs.mapM fun argument =>
        withTransparency .all <| Meta.reduce argument (explicitOnly := false)
          (skipTypes := false) (skipProofs := true)
      trySynthInstance (mkAppN type.getAppFn arguments)
    | result => pure result
  if let .some instanceValue := result then
    unless ← withTransparency .all <| isDefEq (← inferType instanceValue) type do
      throwError "the native instance has a different complete source goal"
  return result

/-- Synthesize a native dictionary for the same retained source type. The native search
keeps every successful local choice and every unresolved result. Only a resolved missing
instance is checked in the complete recorded source interpretation; its dictionary is closed
over every original formal and reapplied to those same formals before the opaque goal is
retained. The complete source scope remains intact; unused lets need not be copied into the
generated dictionary body. No checking local escapes, and no carrier selects a row. -/
opaque SourceReadM.tryInstance (type : Expr) : SourceReadM (LOption Expr) := do
  let type ← liftM (m := MetaM) <| instantiateMVars type
  let native ← liftM (m := MetaM) <| trySourceInstance type
  match native with
  | .some _ | .undef => return native
  | .none => pure ()
  let type ← liftM (m := MetaM) <| instantiateMVars type
  if type.hasExprMVar || type.hasLevelMVar then return .none
  let original ← get
  liftM (m := MetaM) <| checkSelectedSourceContext original.context original.selections
  let formals ← liftM (m := MetaM) <| original.context.bindings.filterM fun binding => do
    return binding.originalSource.isNone && (← binding.expression.fvarId!.getDecl).value?.isNone
  let prepared : LOption Expr ← liftM (m := MetaM) <|
      original.context.withOriginalSources #[type] fun types => do
    let result ← trySourceInstance types[0]!
    let .some instanceValue := result | return result
    let instanceValue ← instantiateMVars instanceValue
    checkWithKernel instanceValue
    let locals := (← getLCtx).foldl
      (fun result declaration => result.push (mkFVar declaration.fvarId)) #[]
    unless locals.size == original.context.bindings.size do
      throwError "source instance preparation changed the original native telescope"
    let function ← mkLambdaFVars locals instanceValue (usedOnly := false) (usedLetOnly := true)
    checkWithKernel function
    return .some function
  let .some function := prepared | return prepared
  let mut instanceValue := function
  for formal in formals do
    let .forallE _ domain _ _ ← liftM (m := MetaM) <| whnfR (← inferType instanceValue)
      | liftM (m := TermElabM) <| throwError "source instance closure lost an original formal position"
    let selected := (← SourceReadM.selection? formal.expression).getD {
      value := formal.expression }
    let value ← SourceReadM.select { selected with value := formal.expression } (some domain)
    instanceValue := mkApp instanceValue value
  liftM (m := MetaM) <| checkWithKernel instanceValue
  return .some (← SourceReadM.select { value := instanceValue } (some type))


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

/-- Synthesize only the scoped operand's pending goals before its continuation runs.
The caller's queue is restored at that boundary; later continuation failures are not
reclassified as operand failures or used to discard later pending goals. -/
def withSynthesizeApplicableScoped {α : Type}
    (read : StateCpsT σ TermElabM (Except MessageData α)) :
    StateCpsT σ TermElabM (Except MessageData α) :=
  fun _ scope finish => do
    let pendingMVarsSaved := (← get).pendingMVars
    modify fun state => { state with pendingMVars := [] }
    let completed ← liftM (m := IO) <| IO.mkRef false
    let restorePending := do
      modify fun state =>
        { state with pendingMVars := state.pendingMVars ++ pendingMVarsSaved }
    try
      read.runK scope fun result scope => do
        if result matches .ok _ then
          synthesizeSyntheticMVars (postpone := .no)
        restorePending
        completed.set true
        finish result scope
    catch error =>
      unless ← completed.get do restorePending
      throw error

/-- Extend only this application's unassigned native holes into the operand continuation.
Every original declaration and selected instance remains an exact prefix. Callback locals
are fully typed before they become legal dependencies of these producer-owned goals. -/
opaque extendSourceApplicationScope (owned : Array MVarId) : TermElabM Unit := do
  let current ← getLCtx
  let currentDeclarations := current.foldl (fun result declaration => result.push declaration) #[]
  let currentInstances ← getLocalInstances
  for slot in owned do
    if ← slot.isAssignedOrDelayedAssigned then continue
    let declaration ← slot.getDecl
    let original := declaration.lctx.foldl (fun result native => result.push native) #[]
    unless original.size ≤ currentDeclarations.size do
      throwError "the native application lost an original metavariable scope"
    for previous in original, actual in currentDeclarations.extract 0 original.size do
      unless previous.fvarId == actual.fvarId && previous.index == actual.index &&
          previous.userName == actual.userName && previous.binderInfo == actual.binderInfo &&
          previous.kind == actual.kind && previous.isNondep == actual.isNondep &&
          previous.type.equal actual.type && previous.value? true == actual.value? true do
        throwError "the native application changed an original metavariable declaration"
    unless declaration.localInstances.size ≤ currentInstances.size do
      throwError "the native application lost an original selected local instance"
    for previous in declaration.localInstances,
        actual in currentInstances.extract 0 declaration.localInstances.size do
      unless previous.className == actual.className && previous.fvar == actual.fvar do
        throwError "the native application changed its selected local instance order"
    if original.size == currentDeclarations.size then continue
    for native in currentDeclarations.extract original.size currentDeclarations.size do
      let type ← instantiateMVars native.type
      if type.hasMVar || type.hasLevelMVar then
        throwError "a scoped source operand has an unresolved native declaration type"
      check type
      discard <| getLevel type
      if let some value := native.value? true then
        check value
        unless ← isDefEq (← inferType value) type do
          throwError "a scoped source operand changed an authored native definition"
    slot.modifyDecl fun declaration =>
      { declaration with lctx := current, localInstances := currentInstances }

/-- Elaborate one application in the complete scopes supplied by its original operands.
Only holes and goals allocated by this producer may acquire those later native locals.
A failed reader unwinds its continuation and restores elaboration state before returning
the mismatch. Exceptions propagate unchanged. The result uses every original argument. -/
private opaque nativeSourceApplicationApplicable (function : Expr) (references : Array Syntax)
    (expected : Option Expr)
    (readArgument : Nat → Expr → StateCpsT σ TermElabM (Except MessageData Expr))
    (allArguments : Bool := false)
    (sourceInstance : Option (Expr → StateCpsT σ TermElabM (LOption Expr)) := none) :
    StateCpsT σ TermElabM (Except MessageData (Expr × Array Expr)) :=
  fun δ initial finish => do
    let saved ← Term.saveState
    try
      let previous ← getMCtx
      let holes ← references.mapM fun _ => mkFreshExprMVar none
      let prepared ← elabAppArgs function #[] (holes.map Arg.expr) expected allArguments false
      let owned := (← getMCtx).decls.foldl (fun result identity _ =>
        if previous.decls.contains identity then result else result.push identity) #[]
      for hole in holes do
        unless (prepared.find? (· == hole)).isSome do
          throwError "the native application lost an original explicit argument"
      let instanceSlots ← (← getMVars prepared).filterM fun slot => do
        let some declaration ← getSyntheticMVarDecl? slot | return false
        return declaration.kind matches .typeClass _
      let rec complete (remaining : List MVarId) (actual : Array Expr) (state : σ) :
          TermElabM (Except MessageData δ) := do
        let slot :: rest := remaining | do
          let result := prepared.replace fun expression =>
            (holes.findIdx? (· == expression)).bind fun index => actual[index]?
          check result
          let checked ← instantiateMVars result
          unless checked.hasMVar || checked.hasLevelMVar do checkWithKernel checked
          return .ok (← finish (.ok (result, actual)) state)
        let (type, native) ← slot.withContext do
          let type ← instantiateMVars (← slot.getType)
          return (type, ← trySourceInstance type)
        let checkSlot (result : LOption Expr) : TermElabM Bool := do
          match result with
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
        let advance (solved : Bool) (state : σ) : TermElabM (Except MessageData δ) := do
          if solved then
            modify fun state => { state with syntheticMVars := state.syntheticMVars.erase slot }
          complete rest actual state
        if let (.none, some prepare) := (native, sourceInstance) then
          (prepare type).runK state fun instanceValue state => do
            -- This callback may retain a dictionary in its actual source scope. Extend
            -- only this producer's original holes before that exact value is assigned.
            extendSourceApplicationScope owned
            advance (← checkSlot instanceValue) state
        else
          advance (← slot.withContext (checkSlot native)) state

      let rec visit (remaining : List Syntax) (actual : Array Expr) (state : σ) :
          TermElabM (Except MessageData δ) := do
        let reference :: rest := remaining | return ← complete instanceSlots.toList actual state
        let index := actual.size
        let hole := holes[index]!
        withRef reference do
          let type ← instantiateMVars (← inferType hole)
          (readArgument index type).runK state fun value state => do
            let value ← match value with
              | .ok value => pure value
              | .error message => return .error message
            extendSourceApplicationScope owned
            let actualType ← inferType value
            unless ← isDefEq actualType type do
              return .error (← addMessageContext m!"the source argument does not match its dependent native type; \
                argument={index + 1}; function={function}; expected={type}; actual={actualType}; value={value}")
            unless ← isDefEq hole value do
              return .error (← addMessageContext m!"the source argument does not match its dependent native position; \
                argument={index + 1}; function={function}; expected={type}; hole={hole}; value={value}")
            visit rest (actual.push value) state
      match ← visit references.toList #[] initial with
      | .ok result => return result
      | .error message =>
        saved.restore (restoreInfo := true)
        finish (.error message) initial
    catch error =>
      saved.restore (restoreInfo := true)
      throw error

/-- Ordinary syntax uses the shared native application producer with Lean's implicit
argument convention. Complete published interfaces use the same producer with every
computational native position exposed, preserving the same original argument holes. -/
opaque elabSourceApplicationApplicableScoped (function : Expr) (references : Array Syntax)
    (expected : Option Expr)
    (readArgument : Nat → Expr → StateCpsT σ TermElabM (Except MessageData Expr))
    (allArguments : Bool := false)
    (sourceInstance : Option (Expr → StateCpsT σ TermElabM (LOption Expr)) := none) :
    StateCpsT σ TermElabM (Except MessageData (Expr × Array Expr)) :=
  nativeSourceApplicationApplicable function references expected readArgument allArguments sourceInstance

/-- Ordinary readers use the same original holes without a scoped runtime state. -/
opaque elabSourceApplicationApplicable (function : Expr) (references : Array Syntax)
    (expected : Option Expr)
    (readArgument : Nat → Expr → TermElabM (Except MessageData Expr)) :
    TermElabM (Except MessageData (Expr × Array Expr)) :=
  (elabSourceApplicationApplicableScoped function references expected
    (fun index type => liftM (readArgument index type))).run' ()

/-- Required applications keep operand continuations through the full native check. -/
opaque elabSourceApplicationScoped (function : Expr) (references : Array Syntax)
    (expected : Option Expr) (readArgument : Nat → Expr → StateCpsT σ TermElabM Expr)
    (sourceInstance : Option (Expr → StateCpsT σ TermElabM (LOption Expr)) := none) :
    StateCpsT σ TermElabM (Expr × Array Expr) := do
  let applied ← elabSourceApplicationApplicableScoped function references expected
    (sourceInstance := sourceInstance)
    fun index type => do return .ok (← readArgument index type)
  match applied with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

/-- Apply already read operands at the declaration's complete dependent types.
Each original operand and its complete selection remain in scope through the native check. -/
def elabRetainedSourceApplication (function : Expr) (arguments : Array Expr)
    (expected : Option Expr := none) : SourceReadM Expr := do
  let references := Array.replicate arguments.size (← liftM (m := TermElabM) getRef)
  let (result, _) ← elabSourceApplicationScoped function references expected
    (sourceInstance := some SourceReadM.tryInstance) fun index expected => do
    let some value := arguments[index]?
      | liftM (m := TermElabM) <| throwError "the native source application lost an original argument"
    let selected := (← SourceReadM.selection? value).getD { value }
    SourceReadM.select { selected with value } (some expected)
  return result

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
opaque applySourceDataArgumentsScoped (function : Expr) (count : Nat) (expected : Option Expr)
    (readArgument : Nat → Expr → StateCpsT σ TermElabM Expr) :
    StateCpsT σ TermElabM Expr := do
  let (_, binders, _) ← forallMetaTelescopeReducing (← inferType function)
  let references := Array.replicate (binders.filter (·.isExplicit)).size Syntax.missing
  let next ← IO.mkRef (0 : Nat)
  let applied ← nativeSourceApplicationApplicable function references expected fun _ domain => do
    if ← isProp domain then return .ok (← sourceContextProof domain)
    let index ← liftM (m := IO) next.get
    unless index < count do
      liftM (m := TermElabM) <|
        throwStratum .malformed "the named source input is missing an explicit data parameter"
    let actual ← readArgument index domain
    liftM (m := IO) <| next.set (index + 1)
    return .ok actual
  let (value, _) ← match applied with
    | .ok value => pure value
    | .error message => liftM (m := TermElabM) <| throwError message
  let supplied ← liftM (m := IO) next.get
  unless supplied == count do
    liftM (m := TermElabM) <|
      throwStratum .malformed "the named source input has extra data parameters"
  return value

/-- Apply complete computational positions of an already selected source function.
This is the same native application producer as ordinary syntax. The caller supplies
one reader per wire position; proof positions are supplied by the original source scope
and have no wire slot. Every retained operand is substituted at its exact original hole.
Native implicit positions are explicit in this complete-interface entrance. -/
opaque applySourceArgumentsScoped (function : Expr) (references : Array Syntax)
    (readArgument : Nat → Expr → StateCpsT σ TermElabM Expr) :
    StateCpsT σ TermElabM Expr := do
  let applyAt := fun (term : Expr) (reference : Syntax)
      (read : Expr → StateCpsT σ TermElabM Expr) => do
    let applied ← nativeSourceApplicationApplicable term #[reference] none
      (fun _ domain => do return .ok (← read domain)) true
    match applied with
    | .ok (result, _) => pure result
    | .error message => liftM (m := TermElabM) <| throwStratum .malformed message
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

/-- Ordinary callers use the same scoped producer without adding a runtime state. -/
opaque applySourceDataArguments (function : Expr) (count : Nat) (expected : Option Expr)
    (readArgument : Nat → Expr → TermElabM Expr) : TermElabM Expr :=
  (applySourceDataArgumentsScoped function count expected
    (fun index type => liftM (readArgument index type))).run' ()

/-- Complete ordinary applications retain the shared positional producer. -/
opaque applySourceArguments (function : Expr) (references : Array Syntax)
    (readArgument : Nat → Expr → TermElabM Expr) : TermElabM Expr :=
  (applySourceArgumentsScoped function references
    (fun index type => liftM (readArgument index type))).run' ()

end

end CasCompiler
