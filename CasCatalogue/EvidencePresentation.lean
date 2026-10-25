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

/-- Present the stored structures of supplied closed registered objects without expanding their
carrier expressions. Carrier projections retain the selected object context needed by registered
evidence. Only an actual constructor field is exposed, using Lean's projection metadata. A class
dictionary may use an ordinary instance only when its entire type and data are definitionally equal
to the supplied dictionary. No predicate, proof procedure, or mathematical value is selected here. -/
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
  let field (struct : Name) (index : Nat) (object : Expr) : MetaM (Option Expr) := do
    unless ← isObject object do return none
    let object ← withTransparency .default <| whnf object
    let env ← getEnv
    unless (getStructureInfo? env struct).isSome do return none
    let ctor := getStructureCtor env struct
    unless object.isAppOfArity ctor.name (ctor.numParams + ctor.numFields) do return none
    if index ≥ ctor.numFields then return none
    let value := object.getArg! (ctor.numParams + index)
    if ← isType value then return none
    return value
  let presented ← Meta.transform p (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then return .continue
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
    | some candidate =>
        return .done candidate) (skipConstInApp := true)
  unless !presented.hasMVar && !presented.hasLevelMVar && (← isTypeCorrect presented) &&
      (← withTransparency .all <| isDefEq presented p) do
    throwError "the field presentation changed the complete target"
  return presented

end CasCatalogue.Language
