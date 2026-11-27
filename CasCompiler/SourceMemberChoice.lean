module

public import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue




structure SourceMemberPath where
  receiver : NativeSourceJudgement
  inherited : Option Route := none

def SourceMemberPath.route? (path : SourceMemberPath) : TermElabM (Option Route) := do
  let some selected := path.receiver.category
    | if path.inherited.isSome then
        throwError "an inherited member lost its complete selected source category"
      else return none
  if let some route := path.inherited then
    unless route.source.syntacticEq selected.expression do
      throwError "an inherited member changed its actual source category"
    return some route
  return some ⟨selected.expression, selected.expression, #[]⟩



structure SourceMemberChoice (Evidence : Type) where
  path : SourceMemberPath
  evidence : Evidence
  judgement : NativeSourceJudgement
  nativeState : Lean.Elab.Term.SavedState
  sourceScope : SourceReadScope
  localContext : LocalContext
  localInstances : LocalInstances



def SourceMemberChoice.capture (path : SourceMemberPath) (evidence : Evidence)
    (judgement : NativeSourceJudgement) : SourceReadM (SourceMemberChoice Evidence) := do
  return {
    path, evidence, judgement
    nativeState := ← liftM (m := TermElabM) saveState
    sourceScope := ← get
    localContext := ← liftM (m := MetaM) getLCtx
    localInstances := ← liftM (m := MetaM) getLocalInstances }



def SourceMemberChoice.collectApplicable
    (readings : Array (SourceReadM (Except MessageData (Option (SourceMemberChoice Evidence))))) :
    SourceReadM (Array (SourceMemberChoice Evidence) × Array MessageData) :=
  fun _ initial finish => do
    let original ← saveState
    let context ← getLCtx
    let instances ← getLocalInstances
    let result ← try
      let mut choices : Array (SourceMemberChoice Evidence) := #[]
      let mut mismatches : Array MessageData := #[]
      for reading in readings do
        original.restore
        let result : Except MessageData (Option (SourceMemberChoice Evidence)) ←
            withLCtx context instances <| reading.runK initial fun result _ => do
              match result with
              | .ok value => return .ok value
              | .error message => return .error (← addMessageContext message)
        match result with
        | .ok (some choice) => choices := choices.push choice
        | .ok none => pure ()
        | .error message => mismatches := mismatches.push message
      pure (choices, mismatches)
    finally
      original.restore
    finish result initial



def SourceMemberChoice.withScope (choice : SourceMemberChoice Evidence)
    (action : SourceReadM α) : SourceReadM α :=
  fun _ _ finish => do
    let previous ← saveState
    let completed ← liftM (m := IO) <| IO.mkRef false
    try
      choice.nativeState.restore
      withLCtx choice.localContext choice.localInstances <|
        action.runK choice.sourceScope fun value scope => do
          completed.set true
          finish value scope
    catch error =>
      unless ← completed.get do previous.restore
      throw error

private structure MemberResultSelection where
  type : Expr
  category : Option NativeSourceCategory
  declarations : NativeDeclarations



private def memberResultSelection (context : OpenContext)
    (judgement : NativeSourceJudgement) : MetaM MemberResultSelection := do
  let terms ← liftM (m := IO) <| IO.mkRef (#[] : Array Expr)
  let close := fun original => do
    let value ← instantiateMVars original
    if value.hasMVar || value.hasLevelMVar || value.hasLooseBVars then
      throwError "a competing member result has undetermined complete selection data"
    let value ← context.withOriginalSources #[value] fun expressions => do
      let formals := (← getLCtx).foldl
        (fun result declaration => result.push (mkFVar declaration.fvarId)) #[]
      mkLambdaFVars formals expressions[0]! (usedOnly := false) (usedLetOnly := false)
    terms.modify (·.push value)
    return value
  let type ← close (← inferType judgement.value)
  let category ← judgement.category.mapM fun category => category.mapM close
  return ⟨type, category, ← NativeDeclarations.capture (← terms.get)⟩

private def memberExprAgrees (left right : Expr) : MetaM Bool :=
  withoutModifyingState do
    unless ← isDefEq (← inferType left) (← inferType right) do return false
    isDefEq left right

private def memberExprArrayAgrees (left right : Array Expr) : MetaM Bool := do
  unless left.size == right.size do return false
  for left in left, right in right do
    unless ← memberExprAgrees left right do return false
  return true

private def memberCategoryAgrees (left right : Option NativeSourceCategory) : MetaM Bool := do
  let leftRecord : SourceSelection Expr := { value := mkSort .zero, category := left }
  let rightRecord : SourceSelection Expr := { value := mkSort .zero, category := right }
  unless SourceSelection.exactlyMatches (fun _ _ => true) leftRecord rightRecord do
    return false
  let terms ← liftM (m := IO) <| IO.mkRef (#[] : Array Expr)
  let collect := fun value => do
    terms.modify (·.push value)
    return value
  discard <| left.mapM fun category => category.mapM collect
  let first ← terms.get
  terms.set #[]
  discard <| right.mapM fun category => category.mapM collect
  memberExprArrayAgrees first (← terms.get)





def checkSourceMemberSelections (choices : Array (SourceMemberChoice Evidence)) :
    TermElabM Unit := do
  if choices.size ≤ 1 then return
  let original ← saveState
  try
    let selections ← choices.mapM fun choice => do
      choice.nativeState.restore
      withLCtx choice.localContext choice.localInstances <|
        memberResultSelection choice.sourceScope.context choice.judgement
    original.restore
    let some first := selections[0]?
      | throwError "member comparison lost its first completed selection"
    for other in selections.drop 1 do


      for declaration in other.declarations.constants do
        if let some current := ((← getEnv).setExporting false).find? declaration.name then
          unless nativeConstantExactlyMatches declaration current do
            throwSemanticAmbiguity "member result selections have different native declarations"
      other.declarations.ensure
      unless (← memberExprAgrees first.type other.type) &&
          (← memberCategoryAgrees first.category other.category) do
        throwSemanticAmbiguity "member families have different complete result selections"
  finally
    original.restore





def sourceMemberPreference (name : String) (considered : Array NativeSourceCategory)
    (surviving : Array SourceMemberPath) : TermElabM (Option (Array (Nat × Route))) := do
  let state ← semanticState
  let sources := considered.foldl (fun found category =>
    if found.any (·.syntacticEq category.expression) then found
    else found.push category.expression) (#[] : Array CategoryExpr)
  let routes ← surviving.mapM SourceMemberPath.route?
  let mut selected : Array (Nat × Route) := #[]
  let mut preferred := false
  for source in sources do
    let candidates := routes.filterMap id |>.filter (·.source.syntacticEq source)
    let some route ← preferredRoute? state source name candidates | continue
    preferred := true
    for index in [:routes.size] do
      let some actual := routes[index]! | continue
      if actual.source.syntacticEq source && actual.refs == route.refs then
        selected := selected.push (index, actual)
  return if preferred then some selected else none



def retainMemberPreference (judgement : NativeSourceJudgement) (route : Option Route) :
    SourceReadM NativeSourceJudgement := do
  let some route := route | return judgement
  let selected := (← SourceReadM.selection? judgement.value).getD { value := judgement.value }
  let value ← SourceReadM.select { selected with
    value := judgement.value
    category := judgement.category
    preferredRoute := some route.refs }
  return { judgement with value }

end CasCompiler
