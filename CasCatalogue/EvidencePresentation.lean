module

public import CasCatalogue.Semantic

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.Language

/-- Expose the stored action of a supplied closed categorical map, while preserving registered
comparison and operation declarations before any value reduction. -/
def suppliedHomPresentation (state : RegistryState) (p : Expr) : MetaM Expr :=
  Meta.transform p (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then
      return .continue
    -- Guard the complete supplied object before any value WHNF or projection reduction.
    let protectedDeclarations := state.presentations.map (·.declaration) ++ state.operations.map (·.declaration)
    if (e.find? fun part => part.constName?.any protectedDeclarations.contains).isSome then
      return .continue
    let originalType ← inferType e
    let type ← withTransparency .all <| whnf originalType
    unless type.isAppOf ``TypeCat.Hom do return .continue
    let bundled ← mkAppM ``TypeCat.Hom.hom #[e]
    let action ← mkAppM ``TypeCat.Fun.toFun #[bundled]
    let action ← withTransparency .all <| whnf action
    let normalized ← mkAppM ``TypeCat.ofHom #[action]
    if normalized.hasMVar || normalized.hasLevelMVar || normalized.hasFVar || normalized.hasLooseBVars then
      throwError "closed Hom action retained unresolved data"
    unless ← isTypeCorrect normalized do throwError "closed Hom action is ill-typed"
    unless ← withTransparency .all <| isDefEq (← inferType normalized) originalType do
      throwError "closed Hom action changed its complete type"
    unless ← withTransparency .all <| isDefEq normalized e do
      throwError "closed Hom action changed its supplied value"
    return .done normalized) (skipConstInApp := true)

/-- Expose the actual field of an allowed supplied record, without unfolding the
mathematical value returned by that field. -/
def storedProjection? (allowed : Name → Bool) (e : Expr) : MetaM (Option Expr) := do
  let (structureName, index, object, arguments) ← match e.getAppFn with
    | .proj structureName index object => pure (structureName, index, object, e.getAppArgs)
    | .const name _ => do
        let some info ← getProjectionFnInfo? name | return none
        let args := e.getAppArgs
        unless args.size > info.numParams do return none
        let ctor ← getConstInfoCtor info.ctorName
        pure (ctor.induct, info.i, args[info.numParams]!,
          args.extract (info.numParams + 1) args.size)
    | _ => return none
  unless allowed structureName do return none
  let ctor := getStructureCtor (← getEnv) structureName
  let object ← withTransparency .default <| whnf object
  unless object.isAppOfArity ctor.name (ctor.numParams + ctor.numFields) &&
      index < ctor.numFields do return none
  let value := (mkAppN (object.getArg! (ctor.numParams + index)) arguments).headBeta
  return if value == e then none else some value

/-- Read stored type-valued categorical projections without unfolding the mathematical
type returned by the field. In particular a lambda's domain or a coordinate type can be
the object of a supplied functor or cone. -/
def categoricalTypeProjection? (e : Expr) : MetaM (Option Expr) := do
  unless ← isType e do return none
  if e.getAppFn.isConstOf ``CategoryTheory.ToType then
    return ← unfoldDefinition? e
  storedProjection? (fun structureName =>
    structureName == ``Prefunctor || structureName == ``CategoryTheory.Functor ||
      structureName == ``CategoryTheory.Limits.Cone ||
      structureName == ``CategoryTheory.Limits.Cocone) e

/-- A formal parameter may refer to a returned factor through its public callable
record. Expose that stored field so Lean can infer the original evidence argument
from the factor term, keeping both its mathematical value and complete target. -/
def formalParameterPresentation (p : Expr) : MetaM Expr := do
  -- An explicit proof may itself determine unresolved declaration parameters.
  -- Preserve that elaboration path until its original expected type is closed.
  if p.hasMVar || p.hasLevelMVar then return p
  let presented ← Meta.transform p (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then return .continue
    if let some value ← storedProjection?
        (· == ``CasCatalogue.MonoLiftFactorComputation) e then return .done value
    return .continue) (skipConstInApp := true)
  unless !presented.hasMVar && !presented.hasLevelMVar && (← isTypeCorrect presented) &&
      (← withTransparency .all <| isDefEq presented p) do
    throwError "the public callable field presentation changed the complete formal target"
  return presented

/-- Expose the head of an already closed computational type for instance
search. Complete categorical actions can leave the original carrier behind an
ordinary type alias rather than a stored projection. No proposition or supplied
data value is unfolded, and no category or dictionary is selected here. -/
def closedTypePresentation (target : Expr) : MetaM Expr := do
  let presented ← Meta.transform target (post := fun term => do
    if term.hasMVar || term.hasLevelMVar || term.hasFVar || term.hasLooseBVars then
      return .continue
    unless (← isType term) && !(← isProp term) do return .continue
    let presented ← withTransparency .default <| whnf term
    if presented == term then return .continue
    return .visit presented) (skipConstInApp := true)
  unless !presented.hasMVar && !presented.hasLevelMVar && (← isTypeCorrect presented) &&
      (← withTransparency .all <| isDefEq presented target) do
    throwError "the type-visibility presentation changed the complete target"
  return presented

/-- Present actual stored fields of supplied closed registered objects. Forwarding through the
same structure projection retains the original selected parameter context; fields supplied through
another structure expose their stored descriptions. Named and primitive projections use Lean's
constructor metadata. Ordinary class instances are used only when their complete types and data
are definitionally equal to the supplied dictionaries. The mathematical type returned by a field
keeps its named head; `closedTypePresentation` is a separate checked view for instance visibility.
No mathematical or proof-procedure case is selected, and the complete original target is checked
after presentation. -/
def evidencePresentation (state : RegistryState) (p : Expr) : MetaM Expr := do
  let objectTypes ← IO.mkRef ({} : Std.HashMap Expr Bool)
  let isObject (object : Expr) : MetaM Bool := do
    let type ← inferType object
    if let some cached := (← objectTypes.get).get? type then return cached
    let mut found := false
    for category in state.categories do
      if ← withoutModifyingState do
          try
            let family ← instantiateFresh category.declaration
            let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
            withTransparency .all <| isDefEq expected type
          catch error =>
            match error with
            | .internal .. => throw error
            | .error .. => pure false then
        found := true
        break
    unless type.hasMVar || type.hasLevelMVar do objectTypes.modify (·.insert type found)
    return found
  -- Forwarding the same stored projection retains its selected object context.
  -- A field supplied by a different structure can expose its actual stored data.
  let isSameForwardedProjection (struct : Name) (index : Nat) (value : Expr) : MetaM Bool := do
    let value := value.consumeMData
    if let .proj forwardedStruct forwardedIndex object := value then
      unless forwardedStruct == struct && forwardedIndex == index do return false
      return ← isObject object
    let .const name _ := value.getAppFn | return false
    let some info ← getProjectionFnInfo? name | return false
    unless value.getAppNumArgs == info.numParams + 1 do return false
    let ctor ← getConstInfoCtor info.ctorName
    unless ctor.induct == struct && info.i == index do return false
    isObject value.appArg!
  let field (struct : Name) (index : Nat) (object : Expr) : MetaM (Option Expr) := do
    unless ← isObject object do return none
    let object ← withTransparency .default <| whnf object
    let env ← getEnv
    unless (getStructureInfo? env struct).isSome do return none
    let ctor := getStructureCtor env struct
    unless object.isAppOfArity ctor.name (ctor.numParams + ctor.numFields) do return none
    if index ≥ ctor.numFields then return none
    let value := object.getArg! (ctor.numParams + index)
    if ← isType value then
      if ← isSameForwardedProjection struct index value then return none
    return value
  let presented ← Meta.transform p (pre := fun e => do
    -- Proof procedures inspect the mathematical goal. Producer addresses and
    -- their retained execution fields cannot supply unrelated mathematical
    -- subterms or obstruct the accepted declaration's own evidence procedure.
    let selected := Trace.unanchor e
    if selected == e then return .continue
    return .visit selected) (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then return .continue
    if let some value ← categoricalTypeProjection? e then return .visit value
    if let .proj struct index object := e then
      if let some value ← field struct index object then return .visit value
      return .continue
    let .const name _ := e.getAppFn | return .continue
    if let some info ← getProjectionFnInfo? name then
      if e.getAppNumArgs == info.numParams + 1 then
        let ctor ← getConstInfoCtor info.ctorName
        if let some value ← field ctor.induct info.i e.appArg! then
          return .visit value
    return .continue) (skipConstInApp := true)
  let presented ← Meta.transform presented (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars || (← isProof e) then
      return .continue
    let type ← inferType e
    unless (← isClass? type).isSome do return .continue
    let candidate? ← withoutModifyingState do
      let .some candidate ← trySynthInstance type | return none
      let candidate ← instantiateMVars candidate
      if candidate.hasMVar || candidate.hasLevelMVar || candidate.hasSorry ||
          !(← isTypeCorrect candidate) then return none
      unless ← withTransparency .all <| isDefEq (← inferType candidate) type <&&>
          isDefEq candidate e do return none
      return some candidate
    match candidate? with
    | none => return .continue
    | some candidate => return .done candidate) (skipConstInApp := true)
  unless !presented.hasMVar && !presented.hasLevelMVar && (← isTypeCorrect presented) &&
      (← withTransparency .all <| isDefEq presented p) do
    throwError "the field presentation changed the complete target"
  return presented

end CasCatalogue.Language
