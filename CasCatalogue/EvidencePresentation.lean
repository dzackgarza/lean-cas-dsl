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

/-- Expose only supplied closed data presentations. A class dictionary may use the ordinary
instance presentation only when its complete data are definitionally identical to the supplied
package. Predicate heads, binders and chosen data remain the same original typed statement. -/
def evidencePresentation (state : RegistryState) (p : Expr) : MetaM Expr := do
  let objectTypes ← IO.mkRef ({} : Std.HashMap Expr Bool)
  let expose (p : Expr) : MetaM Expr :=
    Meta.transform p (post := fun e => do
      if e.hasMVar || e.hasLevelMVar || e.hasFVar || (← isProof e) || (← isProp e) then
        return .continue
      let type ← inferType e
      let classData := (← isClass? type).isSome
      let carrierAlias := !e.isConst && (← isType e) && !(← isProp e)
      let mut objectData := false
      unless classData || carrierAlias do
        if let some cached := (← objectTypes.get).get? type then
          objectData := cached
        else
          for category in state.categories do
            if ← withoutModifyingState do
                try
                  let family ← instantiateFresh category.declaration
                  let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
                  withTransparency .all <| isDefEq expected type
                catch _ => pure false then
              objectData := true
              break
          unless type.hasMVar || type.hasLevelMVar do
            objectTypes.modify (·.insert type objectData)
      if objectData || classData || carrierAlias then
        let normalized ← if carrierAlias && !objectData && !classData then
          whnfR e
        else withTransparency .all <| whnf e
        unless ← withTransparency .all <| isDefEq normalized e do
          throwError "a supplied data presentation changed its complete object"
        return .done normalized
      return .continue) (skipConstInApp := true)
  let presented ← expose (← expose p)
  let presented ← Meta.transform presented (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || (← isProof e) then return .continue
    let type ← inferType e
    unless (← isClass? type).isSome do return .continue
    let candidate? ← withoutModifyingState do
      try
        let candidate ← instantiateMVars (← synthInstance type)
        if candidate.hasMVar || candidate.hasLevelMVar || candidate.hasSorry ||
            !(← isTypeCorrect candidate) then return none
        unless ← withTransparency .all <| isDefEq candidate e do return none
        return some candidate
      catch _ => return none
    match candidate? with
    | none => return .continue
    | some candidate =>
        unless ← withTransparency .all <| isDefEq (← inferType candidate) type do
          throwError "a supplied dictionary presentation changed its complete type"
        return .done candidate) (skipConstInApp := true)
  let presented ← Core.betaReduce presented
  let presented ← suppliedHomPresentation state presented
  -- Finish only stuck, closed carrier projections after dictionary presentation. Expanding
  -- all type expressions earlier would also expose the value's function-wrapper dictionaries.
  let presented ← Meta.transform presented (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then return .continue
    unless (← isType e) && !(← isProp e) do return .continue
    let reduced ← whnfR e
    unless reduced.getAppFn.isProj do return .continue
    -- A carrier projection can itself be a function applied to its supplied object.
    -- Reducing a *closed type projection* is elaboration of a supplied carrier,
    -- not a tactic or a proof procedure.  Do not invoke Lean.Meta.Tactic.Delta:
    -- that machinery belongs exclusively to the registered evidence runner.
    let normalized ← withTransparency .all <| whnf reduced
    unless ← withTransparency .all <| isDefEq normalized e do
      throwError "presenting the carrier changed its complete type"
    return .done normalized) (skipConstInApp := true)
  unless !presented.hasMVar && !presented.hasLevelMVar &&
      (← isTypeCorrect presented) &&
      (← withTransparency .all <| isDefEq presented p) do
    throwError "the evidence presentation is not the original complete target"
  return presented


end CasCatalogue.Language
