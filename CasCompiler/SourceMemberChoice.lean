module

public import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- The actual receiver of a member candidate and its structural transport, if any.
A direct projection or parameter use has no structural transport; when its receiver has a
selected category, that direct use is the empty route at that complete category. -/
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

/-- A produced reading and the exact native elaboration state which formed it. The evidence
belongs to the producer; neither a printed result nor a recovered carrier selects a route. -/
structure SourceMemberChoice (Evidence : Type) where
  path : SourceMemberPath
  evidence : Evidence
  judgement : NativeSourceJudgement
  nativeState : Lean.Elab.Term.SavedState

private structure MemberResultSelection where
  type : Expr
  category : Option NativeSourceCategory
  declarations : NativeDeclarations

-- Freeze only in the state which actually completed this reading. No candidate's assigned
-- metavariables or local native declarations may be interpreted in another candidate state.
private def memberResultSelection (judgement : NativeSourceJudgement) :
    MetaM MemberResultSelection := do
  let resolved := fun value => do
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar || value.hasLooseBVars then
      throwError "a competing member result has undetermined complete selection data"
    return value
  let type ← resolved (← inferType judgement.value)
  let category ← judgement.category.mapM fun category => do
    let bundle ← resolved category.bundle
    let carrier ← category.carrier.mapM fun carrier => do
      let actions ← carrier.actions.mapM resolved
      let comparisons ← carrier.comparisons.mapM resolved
      return { carrier with actions, comparisons }
    let limit ← category.limit.mapM fun limit => do
      let cone ← resolved limit.cone
      let bundle ← resolved limit.bundle
      let presentation ← resolved limit.presentation
      let diagram ← resolved limit.diagram
      let interface ← limit.interface.mapM resolved
      return { limit with cone, bundle, presentation, diagram, interface }
    return { category with bundle, carrier, limit }
  let expressions := #[type] ++ category.toArray.flatMap fun category =>
    #[category.bundle] ++
      category.carrier.toArray.flatMap (fun carrier => carrier.actions ++ carrier.comparisons) ++
      category.limit.toArray.flatMap (fun limit =>
        #[limit.cone, limit.bundle, limit.presentation, limit.diagram,
          limit.interface.presentation, limit.interface.diagram] ++
          limit.interface.standardization.toArray ++ limit.interface.dataConstructor.toArray)
  return ⟨type, category, ← NativeDeclarations.capture expressions⟩

private def memberExprAgrees (left right : Expr) : MetaM Bool :=
  withoutModifyingState do
    unless ← isDefEq (← inferType left) (← inferType right) do return false
    isDefEq left right

private def memberExprArrayAgrees (left right : Array Expr) : MetaM Bool := do
  unless left.size == right.size do return false
  for left in left, right in right do
    unless ← memberExprAgrees left right do return false
  return true

private def memberExprOptionAgrees (left right : Option Expr) : MetaM Bool := do
  match left, right with
  | none, none => return true
  | some left, some right => memberExprAgrees left right
  | _, _ => return false

private def memberCategoryAgrees (left right : Option NativeSourceCategory) : MetaM Bool := do
  match left, right with
  | none, none => return true
  | some left, some right =>
    unless left.role == right.role && left.expression.syntacticEq right.expression &&
        (← memberExprAgrees left.bundle right.bundle) do return false
    match left.carrier, right.carrier with
    | none, none => pure ()
    | some left, some right =>
      unless left.refs == right.refs && left.target.syntacticEq right.target &&
          left.identifications == right.identifications &&
          (← memberExprArrayAgrees left.actions right.actions) &&
          (← memberExprArrayAgrees left.comparisons right.comparisons) do return false
    | _, _ => return false
    match left.limit, right.limit with
    | none, none => return true
    | some left, some right =>
      unless left.row == right.row && left.declaration == right.declaration &&
          left.colimit == right.colimit && left.category.syntacticEq right.category do
        return false
      unless ← memberExprArrayAgrees
          #[left.cone, left.bundle, left.presentation, left.diagram,
            left.interface.presentation, left.interface.diagram]
          #[right.cone, right.bundle, right.presentation, right.diagram,
            right.interface.presentation, right.interface.diagram] do return false
      unless ← memberExprOptionAgrees left.interface.standardization
          right.interface.standardization do return false
      memberExprOptionAgrees left.interface.dataConstructor right.interface.dataConstructor
    | _, _ => return false
  | _, _ => return false

/-- Whole-family agreement does not erase a later result's selected structure. Compare the
complete completed selection in addition to that independent family proof. Only full native
bundles, unapplied carrier actions and the actual universal presentation are compared here;
an equality of values at one receiver is never consulted. The chosen state stays unchanged. -/
def checkSourceMemberSelections (choices : Array (SourceMemberChoice Evidence)) :
    TermElabM Unit := do
  if choices.size ≤ 1 then return
  let original ← saveState
  try
    let selections ← choices.mapM fun choice => do
      choice.nativeState.restore
      return ← memberResultSelection choice.judgement
    original.restore
    let some first := selections[0]?
      | throwError "member comparison lost its first completed selection"
    for other in selections.drop 1 do
      -- Candidate-local auxiliary names may coincide after rollback. Different checked
      -- payloads cannot become equal by restoring one over the other's environment.
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

/-- Apply the existing C6 preference check to all actually surviving member kinds together.
The considered categories include candidates rejected by their own native expected check,
so a declared preference cannot silently disappear when its route fails that check. The
returned indices refer to the original typed candidates; no reading is reconstructed. -/
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

/-- Retain the admitted route as an observation of the chosen reading. Its typed route and
original receiver have already selected the candidate; this annotation is never a selector. -/
def retainMemberPreference (judgement : NativeSourceJudgement) (route : Option Route) :
    NativeSourceJudgement :=
  match route with
  | none => judgement
  | some route =>
    let data := KVMap.empty.setString `CasCompiler.source.preferredRoute
      (reprStr (route.refs.map (·.label)))
    { judgement with value := .mdata data judgement.value }

end CasCompiler
