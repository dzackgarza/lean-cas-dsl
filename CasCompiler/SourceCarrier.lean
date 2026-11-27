module

public import CasCompiler.SourceRoutes
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.Surface
public import CasContract.Registration
public import CasContract.Failure

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue



initialize preferredRoutesExtension : EnvExtension (Array PreferredRoute) ←
  registerEnvExtension (pure #[])


def setPreferredRoutes (routes : Array PreferredRoute) : CoreM Unit :=
  modifyEnv (preferredRoutesExtension.setState · routes)




def preferredRoute? (state : SemanticState) (receiver : CategoryExpr) (name : String)
    (routes : Array Route) : MetaM (Option Route) := do
  let applicable := (preferredRoutesExtension.getState (← getEnv)).filter fun preference =>
    preference.name == name && state.categories.any fun entry =>
      entry.id.raw == preference.receiver && entry.expression.syntacticEq receiver
  let declared := applicable.foldl (fun found preference =>
    if found.contains preference.route then found else found.push preference.route) #[]
  match declared with
  | #[] => return none
  | #[labels] =>
    let some route := routes.find? (·.refs.map (·.label) == labels)
      | throwStratum .invalid
          m!"the declared preferred route {labels} of {name} is not a surviving route"
    return some route
  | _ => throwSemanticAmbiguity m!"several declared preferred routes of {name} apply: {declared}"

private structure CarrierCategoryFamily where
  value : Expr
  universes : List Name



private partial def carrierCategoryFamily (state : SemanticState) (source : CategoryExpr) :
    MetaM CarrierCategoryFamily := do
  let value ← nativeCategoryFamily state source fun _ => do
    return .param (← mkFreshUserName `carrierUniverse)
  let levels : CollectLevelParams.State := {}
  return ⟨value, (levels.collect value).params.toList⟩

private def carrierRoutes (source : CategoryExpr) : MetaM (Array Route) := do
  let sets := CategoryExpr.atom CategoryId.sets
  let routes ← SourceRoutes.forOwner source sets
  let some candidates ← routes.finiteRoutes
    | throwUnsupportedSource "the carrier route family requires its supplied uniform comparison"
  if candidates.isEmpty then
    throwError "the selected category has no structural carrier route in the source inventory"
  return candidates




def sourceRouteAgreements (state : SemanticState) (source : NativeSourceCategory)
    (routes : Array Route) : MetaM (Array Expr) := do
  if routes.size == 1 then return #[]
  let family ← carrierCategoryFamily state source.expression
  let functions ← routes.mapM fun route => do
    let value ← forallTelescopeReducing (← inferType family.value) fun parameters _ => do
      let selected ← nativeRouteFunctor state route (mkAppN family.value parameters)
      mkLambdaFVars parameters (← instantiateMVars selected.functor)
    if value.hasMVar || value.hasLevelMVar then
      throwError "the whole carrier functor has undetermined source parameters"
    return value
  let first := functions[0]!
  let proofs ← (functions.drop 1).mapM fun other => do
    unless ← isDefEq (← inferType first) (← inferType other) <&&> isDefEq first other do
      throwSemanticAmbiguity
        "structural carrier families require their supplied selection or equality"
    let proposition ← mkEq first other
    let proof ← mkExpectedTypeHint (← mkEqRefl first) proposition
    checkWithKernel proof
    return proof


  let levels ← family.universes.mapM fun _ => mkFreshLevelMVar
  let actual := family.value.instantiateLevelParams family.universes levels
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType actual)
  unless ← expandSourceStructures arguments do
    throwError "the selected carrier has inconsistent native parameter structures"
  unless ← isDefEq (mkAppN actual arguments) source.bundle do
    throwError "the selected carrier has a different complete native category family"
  let levels ← levels.mapM instantiateLevelMVars
  let arguments ← arguments.mapM instantiateMVars
  proofs.mapM fun proof => do
    let mut proof := proof.instantiateLevelParams family.universes levels
    for argument in arguments do
      proof ← mkAppM ``congrFun #[proof, argument]
    instantiateMVars proof


private def carrierAction (role : SourceCategoryRole) (functor value target : Expr) :
    MetaM Expr :=
  match role with
  | .object => functorObject functor value target
  | .morphism => mkAppM ``CategoryTheory.Functor.map #[functor, value]





opaque sourceCarrierSelection (source : NativeSourceJudgement) :
    MetaM (SourceSelection Expr) := do
  let some category := source.category
    | do
      discard <| getLevel source.value
      return { value := source.value, category := source.category }
  if category.expression.syntacticEq (.atom CategoryId.sets) then
    if category.role == .object then discard <| getLevel source.value
    return { value := source.value, category := source.category }
  let state ← semanticState
  let mut value := source.value
  let mut bundle := category.bundle
  let mut start := category.expression
  let mut selectedEdges := #[]
  if let some selected := category.carrier then
    for declaration in selected.identifications do discard <| checkedDeclaration declaration
    unless (state.routeEdges? start selected.target selected.refs).isSome &&
        selected.refs.size == selected.actions.size do
      throwError "the selected carrier prefix has incomplete source boundaries or applications"
    for ref in selected.refs, action in selected.actions do
      checkEdgeDeclarations state ref
      unless ← isDefEq (← state.edgeFunctor ref) action do
        throwError "the selected carrier application differs from its declared edge"
      let (domain, target) ← functorCategoryBundles action
      unless ← isDefEq domain bundle do
        throwError "the selected carrier application has a different complete source category"
      value ← carrierAction category.role action value target
      bundle := target
    selectedEdges := selected.refs
    start := selected.target
  let routes ← carrierRoutes start
  let proofs ← sourceRouteAgreements state ⟨category.role, start, bundle, none, none⟩ routes
  let some route := routes[0]?
    | throwError "carrier formation requires its source route"
  if !route.steps.isEmpty then
    let selected ← nativeRouteFunctor state route bundle
    value ← carrierAction category.role selected.functor value selected.target
    bundle := selected.target
  for proof in proofs.reverse do
    let body := value
    value ← withLetDecl (← mkFreshUserName `carrierAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] body
        (usedLetOnly := false) (generalizeNondepLet := false)
  let selection := category.carrier.map fun selected =>
    { selected with refs := #[], target := .atom CategoryId.sets, actions := #[] }
  return {
    value
    category := some ⟨category.role, .atom CategoryId.sets, bundle, selection, none⟩
    typeOrigin := if category.role == .object then some ⟨category, source.value, value⟩ else none
    carrierRoutes := routes.map fun route => selectedEdges ++ route.refs }


opaque sourceCarrier (source : NativeSourceJudgement) : SourceReadM NativeSourceJudgement := do
  if source.category.isNone || source.category.any (fun category =>
      category.expression.syntacticEq (.atom CategoryId.sets)) then
    if source.category.isNone || source.category.any (·.role == .object) then
      discard <| getLevel source.value
    return source
  let selected ← sourceCarrierSelection source
  let value ← SourceReadM.select selected
  return ⟨value, selected.category⟩



def sourceObjectCategory? (type : Expr) : TermElabM (Option NamedCategoryEntry) := do
  let mut found := #[]
  for entry in (← semanticState).categories do
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let objects ← mkAppM ``CategoryTheory.Bundled.α #[mkAppN family parameters]
    if ← withoutModifyingState (isDefEq objects type) then found := found.push entry
  match found with
  | #[] => return none
  | #[entry] => return some entry
  | _ => throwSemanticAmbiguity "several registered categories have these objects"






opaque sourceStructuralView (source : NativeSourceJudgement) (target : CategoryExpr)
    (name : Option String) : SourceReadM NativeSourceJudgement := do
  let some category := source.category
    | liftM (m := TermElabM) <| throwError "a structural view requires its selected category"
  unless category.role == .object do liftM (m := TermElabM) <| throwError "a structural view acts on an object"
  if category.expression.syntacticEq target then return source
  let state ← semanticState
  let routes ← SourceRoutes.forOwner category.expression target
  let some routes ← routes.finiteRoutes
    | liftM (m := TermElabM) <| throwUnsupportedSource "the structural view requires its supplied uniform comparison"
  let some route := routes[0]?
    | liftM (m := TermElabM) <| throwError "the selected category has no structural route to the expected category"


  let preferred ← if routes.size > 1 then
      match name with
      | some name => preferredRoute? state category.expression name routes
      | none => pure none
    else pure none
  let (route, proofs) ← match preferred with
    | some route => pure (route, #[])
    | none => pure (route, ← sourceRouteAgreements state category routes)
  let selected ← nativeRouteFunctor state route category.bundle
  let mut value ← functorObject selected.functor source.value selected.target
  for proof in proofs.reverse do
    let body := value
    value ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `viewAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] body
        (usedLetOnly := false) (generalizeNondepLet := false)
  let carrier : NativeSourceCarrierSelection := {
    refs := route.refs, target
    identifications := category.carrier.map (·.identifications) |>.getD #[]
    actions := selected.actions
    comparisons := category.carrier.map (·.comparisons) |>.getD #[] }
  let selection : SourceSelection Expr := {
    value
    category := some ⟨.object, target, selected.target, none, none⟩
    typeOrigin := if target.syntacticEq (.atom CategoryId.sets) then
      some ⟨{ category with carrier := some carrier }, source.value, value⟩ else none
    carrierRoutes := #[route.refs]
    preferredRoute := preferred.map (·.refs) }
  return ⟨← SourceReadM.select selection, selection.category⟩




def sourceCommonCategory (left right : NativeSourceJudgement) :
    SourceReadM (NativeSourceJudgement × NativeSourceJudgement) := do
  let some first := left.category | return (left, right)
  let some second := right.category | return (left, right)
  unless first.role == second.role do
    liftM (m := TermElabM) <| throwError "source values have different object and morphism roles"
  let sets := CategoryExpr.atom CategoryId.sets
  let (left, right) ←
    if first.expression.syntacticEq sets && !second.expression.syntacticEq sets then
      pure (left, ← sourceCarrier right)
    else if second.expression.syntacticEq sets && !first.expression.syntacticEq sets then
      pure (← sourceCarrier left, right)
    else pure (left, right)
  let some first := left.category
    | liftM (m := TermElabM) <| throwError "source carrier comparison lost its first selected category"
  let some second := right.category
    | liftM (m := TermElabM) <| throwError "source carrier comparison lost its second selected category"
  unless first.expression.syntacticEq second.expression &&
      (← isDefEq first.bundle second.bundle) do
    liftM (m := TermElabM) <| throwError "source values have different complete selected categories"
  return (left, right)




def sourceCarrierFamilyObject (source : NativeSourceCategory) (bundle object : Expr) :
    TermElabM Expr := do
  let state ← semanticState
  let selection ← source.carrier.mapM fun selection => do
    let some steps := state.routeEdges? source.expression selection.target selection.refs
      | throwError "the source carrier family lost its selected prefix"
    let route : Route := { source := source.expression, target := selection.target, steps }
    let native ← nativeRouteFunctor state route bundle
    return { selection with actions := native.actions }
  let carrier ← sourceCarrierSelection ⟨object, some ⟨.object, source.expression, bundle, selection, none⟩⟩
  return carrier.value



def sourceFunction (source : NativeSourceJudgement) : MetaM Expr := do
  if source.category.any (·.role == .morphism) then
    let carrier ← sourceCarrierSelection source
    sourceSetFunction carrier.value
  else pure source.value

private partial def elementTypeBody (type : Expr) : Expr :=
  match type with
  | .mdata _ body => elementTypeBody body
  | .letE _ _ value body _ => elementTypeBody (body.instantiate1 value)
  | _ => type


private def elementTypeOrigin (type : Expr) : Option (Expr × (Expr → Expr)) :=
  match elementTypeBody type with
  | .app function object => some (object, mkApp function)
  | .proj name index object => some (object, Expr.proj name index)
  | _ => none



def sourceElementOwners
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (expected : Expr) (hints : Array Expr) : SourceReadM (Array NativeSourceElementOwner) := do
  let mut selected : Array NativeSourceElementOwner := #[]
  for hint in hints do
    let origin ← sourceTypeOrigin? hint
    let candidate := match origin with
      | some origin => some (origin.object, fun object =>
          origin.type.replace fun part => if part == origin.object then some object else none)
      | none => elementTypeOrigin hint
    let some (value, typeAt) := candidate | continue
    let retained ← if origin.isSome then pure none else sourceObjectOrigin? value
    let value := retained.map (·.2) |>.getD value
    let category ← match origin, retained with
      | some origin, _ => pure (some origin.category)
      | none, some (category, _) => pure (some category)
      | none, none => if let .fvar id := value then categoryOf id else pure none
    let category ← match category with
      | some category => pure (some category)
      | none => pure ((← SourceReadM.selection? value).bind (·.category))
    let some category := category | continue
    unless category.role == .object &&
        !category.expression.syntacticEq (.atom CategoryId.sets) do continue
    if selected.any (·.value == value) then continue
    let carrier ← sourceCarrierSelection ⟨value, some category⟩
    unless ← withoutModifyingState <| isDefEq carrier.value expected do continue
    let proof ← liftM (m := TermElabM) <| withLocalDeclD `elementOwner (← inferType value) fun object => do
      let carrier ← sourceCarrierSelection ⟨object, some category⟩
      let original ← mkLambdaFVars #[object] (typeAt object)
      let canonical ← mkLambdaFVars #[object] carrier.value
      unless ← isDefEq (← inferType original) (← inferType canonical) <&&>
          isDefEq original canonical do
        throwUnsupportedSource "element provenance requires its whole carrier-family comparison"
      let proof ← mkExpectedTypeHint (← mkEqRefl original) (← mkEq original canonical)
      checkWithKernel proof
      return proof
    selected := selected.push ⟨category, value, proof⟩
  return selected

end CasCompiler
