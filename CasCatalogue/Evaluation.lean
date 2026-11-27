



module

public import CasCatalogue.Codec
public import Lean.Elab.Tactic.Basic
public import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section









open Lean Meta Elab Term

namespace CasCatalogue.Evaluation

open Decide









def runProcedure (procedure : Name) (goal : MVarId) :
    TermElabM (Except String (List MVarId)) := do
  let procedure ← unsafe evalConst (Lean.Elab.Tactic.TacticM Unit) procedure
  let messages := (← getThe Core.State).messages
  let restore : TermElabM Unit := modifyThe Core.State fun st => { st with messages }
  let outcome ← withoutErrToSorry <| Term.withoutErrToSorry do
    try
      let remaining ← Term.withSynthesize (postpone := .no) <|
        Lean.Elab.Tactic.run goal procedure
      pure (Except.ok remaining : Except String (List MVarId))


    catch e => pure (Except.error (← e.toMessageData.toString))
  let logged := (← getThe Core.State).messages.hasErrors && !messages.hasErrors
  match outcome with
  | .error message =>
      restore
      return .error message
  | .ok remaining =>
      if logged then
        let errors := (← getThe Core.State).messages.toList.filter (·.severity == .error)
        let detail ← match errors.getLast? with
          | some msg => msg.data.toString
          | none => pure ""
        restore
        return .error s!"its proof has a hole: {detail}"
      return .ok remaining






def evaluationsOf (state : SemanticState) (p : Expr) : Array Name :=
  let occurs (denotation : Name) : Bool := (p.find? (·.isConstOf denotation)).isSome
  (state.literals.filterMap fun form => if occurs form.denotation then form.evaluation else none)
    ++ (state.subsetLiterals.filterMap fun form =>
      if occurs form.denotation then form.evaluation else none)








def evaluatedDecides (evaluations : Array Name) (p : Expr) : TermElabM Bool := do
  let attempt : TermElabM Bool := do
    let goal ← mkFreshExprMVar p .syntheticOpaque
    let mut remaining := [goal.mvarId!]
    for evaluation in evaluations do
      let [current] := remaining | return false
      match ← runProcedure evaluation current with
      | .ok goals => remaining := goals


      | .error _ => return false
    match remaining with
    | [] => pure ()
    | [residue] => residue.withContext do
        let condition ← instantiateMVars (← residue.getDecl).type
        let structural ← if condition.hasFVar || condition.hasMVar || condition.hasLevelMVar then
          pure none else Codec.conditionProof condition
        let proof ← match structural with
          | some proof => pure proof
          | none => mkDecideProof condition
        residue.assign proof
    | _ => return false
    let proof ← instantiateMVars goal
    if proof.hasMVar || proof.hasLevelMVar || proof.hasSorry then return false
    kernelAccepts p proof
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := decideBudget * 1000 }) <|


      tryCatchRuntimeEx attempt fun _ => pure false




def decideEvaluated (p : Expr) (extra : Array Name := #[]) : TermElabM (Option Bool) := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then return none
  let evaluations := extra ++ evaluationsOf (← semanticState) p
  if ← evaluatedDecides evaluations p then return some true
  if ← evaluatedDecides evaluations (mkNot p) then return some false
  return none





def plumbingRoots : List Name :=
  [`CasCatalogue, `LeanCategories, `CategoryTheory, `TypeCat, `DFunLike, `FunLike, `Function,
   `id, `Prod.fst, `Prod.snd, `Prod.map, `inferInstance, `inferInstanceAs]






def plumbingApplication (e : Expr) : MetaM Bool := do
  unless e.isAppOf ``DFunLike.coe do return true
  let some F := e.getAppArgs[4]? | return true
  let type ← whnfR (← inferType F)
  return type.isAppOf ``Quiver.Hom || (type.getAppFn.constName?.map
    (fun c => [`CategoryTheory, `TypeCat].any (·.isPrefixOf c))).getD false





partial def plumbingValue (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  match e with
  | .lam .. => lambdaTelescope e fun xs body => do mkLambdaFVars xs (← plumbingValue body)
  | .app .. | .const .. =>
      let f := e.getAppFn
      if let .const c _ := f then
        if plumbingRoots.any (·.isPrefixOf c) && (← plumbingApplication e) then
          if let some e' ← unfoldDefinition? e then return ← plumbingValue e'
          if let some e' ← unfoldProjInst? e then return ← plumbingValue e'
      let args ← e.getAppArgs.mapM fun a => do
        if (← isProp (← inferType a)) || (← isType a) then pure a else plumbingValue a
      let e' := mkAppN f args

      let r ← whnfCore e'
      if r != e' then plumbingValue r else pure e'
  | _ => pure e


def normalizedValue (v : Expr) : MetaM Expr := do
  let v' ← plumbingValue v
  unless ← withTransparency .default (isDefEq v' v) do
    throwError "the kernel's normal form of {v} is not the value itself"
  return v'



def suppliedHomPresentation (state : SemanticState) (p : Expr) : MetaM Expr :=
  Meta.transform p (pre := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then
      return .continue
    if ← isProof e then return .done e
    return .continue) (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then
      return .continue

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




def evidencePresentation (state : SemanticState) (p : Expr) : MetaM Expr := do
  let objectTypes ← IO.mkRef ({} : Std.HashMap Expr Bool)
  let expose (p : Expr) : MetaM Expr :=
    Meta.transform p (pre := fun e => do
      if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then
        return .continue
      if ← isProof e then return .done e
      return .continue) (post := fun e => do
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
                  let constant ← mkConstWithFreshMVarLevels category.declaration
                  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
                  let family := mkAppN constant arguments
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
  let presented ← Meta.transform presented (pre := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then
      return .continue
    if ← isProof e then return .done e
    return .continue) (post := fun e => do
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


  let presented ← Meta.transform presented (pre := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then
      return .continue
    if ← isProof e then return .done e
    return .continue) (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then return .continue
    unless (← isType e) && !(← isProp e) do return .continue
    let reduced ← whnfR e
    unless reduced.isProj do return .continue



    let normalized ← withTransparency .all <| whnf reduced
    unless ← withTransparency .all <| isDefEq normalized e do
      throwError "presenting the carrier changed its complete type"
    return .done normalized) (skipConstInApp := true)
  unless !presented.hasMVar && !presented.hasLevelMVar &&
      (← isTypeCorrect presented) &&
      (← withTransparency .all <| isDefEq presented p) do
    throwError "the evidence presentation is not the original complete target"
  return presented

end CasCatalogue.Evaluation
