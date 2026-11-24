module

public import CasCompiler.SourceRoutes
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.Surface
public import CasContract.Registration
public import CasContract.Failure

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- The declared preferred routes (constitution C6) of the admitted registrations that the current
statement is read with; the kernel session sets them before reading. -/
initialize preferredRoutesExtension : EnvExtension (Array PreferredRoute) ←
  registerEnvExtension (pure #[])

/-- Read the statements that follow with the declared preferred routes `routes`. -/
def setPreferredRoutes (routes : Array PreferredRoute) : CoreM Unit :=
  modifyEnv (preferredRoutesExtension.setState · routes)

/-- Of the surviving routes `routes` from the category `receiver` for the surface name `name`, the
one that the admitted registrations declare preferred. None when no preference applies; two
different applicable preferences are not ranked (contract api/manifest.md). -/
def preferredRoute? (state : SemanticState) (receiver : CategoryExpr) (name : String)
    (routes : Array Route) : TermElabM (Option Route) := do
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

-- Reuse the named-category and unary-constructor families in the semantic registry.
-- All source parameters and universes stay rigid while comparing complete functors.
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

-- Eq.refl is checked on full functor families before any object, category parameter,
-- or universe is specialized. A natural isomorphism is not used as functor equality.
-- Reuse: SourceSession.operationConversion's native conversion rule and congrFun.
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
  -- Instantiate a proof already checked at the complete rigid family. These fresh
  -- arguments are constrained by the actual full category bundle, including str.
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

-- Apply the already selected native functor at the judgement's unchanged role.
private def carrierAction (role : SourceCategoryRole) (functor value target : Expr) :
    MetaM Expr :=
  match role with
  | .object => functorObject functor value target
  | .morphism => mkAppM ``CategoryTheory.Functor.map #[functor, value]

/-- Consume a supplied carrier prefix, or the complete structural carrier family.
Only checked uniform native equality identifies implicit alternatives. Actual functor
actions, original objects or arrows, route references and equality evidence remain in the term.
Source: ObjectRefinement, structuralEdges and the native family-conversion rule. -/
opaque sourceCarrier (source : NativeSourceJudgement) : MetaM NativeSourceJudgement := do
  let some category := source.category
    | do
      discard <| getLevel source.value
      return source
  if category.expression.syntacticEq (.atom CategoryId.sets) then
    if category.role == .object then discard <| getLevel source.value
    return source
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
  let refs := reprStr (routes.map fun route => selectedEdges ++ route.refs)
  value := .mdata (KVMap.empty.setString `CasCompiler.source.carrierRoutes refs) value
  if category.role == .object then
    value ← annotateSourceType category source.value value
  let selection := category.carrier.map fun selected =>
    { selected with refs := #[], target := .atom CategoryId.sets, actions := #[] }
  return ⟨value, some ⟨category.role, .atom CategoryId.sets, bundle, selection, none⟩⟩

/-- The registered category whose objects are the native type `type` (`MonCat` for `Monoids`).
Several categories with that object type are ambiguous. -/
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

/-- An object of one selected category read where an object of `target` is expected: its image
along the structural route from its category to `target`, with the whole-family agreement of
competing routes (a ring of matrices as the monoid whose units are formed). The route functor
and its actual object action remain in the term. Source: SourceRoutes, structural edges and
the native family-conversion rule, as for `sourceCarrier`. -/
opaque sourceStructuralView (source : NativeSourceJudgement) (target : CategoryExpr)
    (name : Option String) : TermElabM NativeSourceJudgement := do
  let some category := source.category
    | throwError "a structural view requires its selected category"
  unless category.role == .object do throwError "a structural view acts on an object"
  if category.expression.syntacticEq target then return source
  let state ← semanticState
  let routes ← SourceRoutes.forOwner category.expression target
  let some routes ← routes.finiteRoutes
    | throwUnsupportedSource "the structural view requires its supplied uniform comparison"
  let some route := routes[0]?
    | throwError "the selected category has no structural route to the expected category"
  -- Competing routes for a name are resolved by a declared preferred route, recorded with the
  -- reading, or else by their whole-family agreement (constitution C6).
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
    value ← withLetDecl (← mkFreshUserName `viewAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] body
        (usedLetOnly := false) (generalizeNondepLet := false)
  if preferred.isSome then
    value := .mdata (KVMap.empty.setString `CasCompiler.source.preferredRoute
      (reprStr (route.refs.map (·.label)))) value
  if target.syntacticEq (.atom CategoryId.sets) then
    -- This image is a native type parameter. Preserve its already selected carrier
    -- action and original owner before the parameter's outer object annotation.
    -- Existing comparisons keep their own declared domains; the image's agreement
    -- proofs remain in the unchanged native let envelope above.
    let carrier : NativeSourceCarrierSelection := {
      refs := route.refs, target
      identifications := category.carrier.map (·.identifications) |>.getD #[]
      actions := selected.actions
      comparisons := category.carrier.map (·.comparisons) |>.getD #[] }
    value ← annotateSourceType { category with carrier := some carrier } source.value value
  return ⟨value, some ⟨.object, target, selected.target, none, none⟩⟩

/-- Put source values in the category explicitly selected by a set-valued operand.
Reuse: sourceCarrier's whole functor checks and retained native actions. Two structured
operands keep their selected category; an explicit set operand supplies the carrier context. -/
def sourceCommonCategory (left right : NativeSourceJudgement) :
    TermElabM (NativeSourceJudgement × NativeSourceJudgement) := do
  let some first := left.category | return (left, right)
  let some second := right.category | return (left, right)
  unless first.role == second.role do
    throwError "source values have different object and morphism roles"
  let sets := CategoryExpr.atom CategoryId.sets
  let (left, right) ←
    if first.expression.syntacticEq sets && !second.expression.syntacticEq sets then
      pure (left, ← sourceCarrier right)
    else if second.expression.syntacticEq sets && !first.expression.syntacticEq sets then
      pure (← sourceCarrier left, right)
    else pure (left, right)
  let some first := left.category
    | throwError "source carrier comparison lost its first selected category"
  let some second := right.category
    | throwError "source carrier comparison lost its second selected category"
  unless first.expression.syntacticEq second.expression &&
      (← isDefEq first.bundle second.bundle) do
    throwError "source values have different complete selected categories"
  return (left, right)

/-- Apply the selected carrier to an arbitrary object in its complete category family.
Reuse: nativeRouteFunctor and sourceCarrier. Typed provenance stays with source types;
family comparisons use the actual carrier expression after removing that annotation. -/
def sourceCarrierFamilyObject (source : NativeSourceCategory) (bundle object : Expr) :
    TermElabM Expr := do
  let state ← semanticState
  let selection ← source.carrier.mapM fun selection => do
    let some steps := state.routeEdges? source.expression selection.target selection.refs
      | throwError "the source carrier family lost its selected prefix"
    let route : Route := { source := source.expression, target := selection.target, steps }
    let native ← nativeRouteFunctor state route bundle
    return { selection with actions := native.actions }
  let carrier ← sourceCarrier ⟨object, some ⟨.object, source.expression, bundle, selection, none⟩⟩
  return (← sourceTypeOrigin? carrier.value).map (·.type) |>.getD carrier.value

/-- Apply the selected complete carrier functor to an arrow before taking its function.
Ordinary native functions retain their original expression and context. -/
def sourceFunction (source : NativeSourceJudgement) : MetaM Expr := do
  if source.category.any (·.role == .morphism) then
    let carrier ← sourceCarrier source
    sourceSetFunction carrier.value
  else pure source.value

private partial def elementTypeBody (type : Expr) : Expr :=
  match type with
  | .mdata _ body => elementTypeBody body
  | .letE _ _ value body _ => elementTypeBody (body.instantiate1 value)
  | _ => type

-- Vary only the final object argument. All other data remain fixed.
private def elementTypeOrigin (type : Expr) : Option (Expr × (Expr → Expr)) :=
  match elementTypeBody type with
  | .app function object => some (object, mkApp function)
  | .proj name index object => some (object, Expr.proj name index)
  | _ => none

/-- Recover an element owner from its principal source object, with a checked family
comparison. Reuse: registeredDomain, objectCarrierSelection and sourceCarrier. -/
def sourceElementOwners
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (expected : Expr) (hints : Array Expr) : TermElabM (Array NativeSourceElementOwner) := do
  let state ← semanticState
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
      | none => do
        let (_, entries) ← registeredDomain value
        if entries.isEmpty then pure none
        else do
          let #[entry] := entries
            | throwSemanticAmbiguity "the element owner requires its selected source object"
          let #[category] := state.categories.filter (·.id == entry.category)
            | throwError "the element owner requires one complete source category"
          discard <| checkedDeclaration category.declaration
          let family ← mkConstWithFreshMVarLevels category.declaration
          let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
          let bundle := mkAppN family parameters
          let objectType ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
          unless ← isDefEq objectType (← inferType value) do
            throwError "the source element owner has a different native category"
          let bundle ← instantiateMVars bundle
          let carrier ← objectCarrierSelection entry bundle value
          pure (some ⟨.object, category.expression, bundle, carrier, none⟩)
    let some category := category | continue
    unless category.role == .object &&
        !category.expression.syntacticEq (.atom CategoryId.sets) do continue
    if selected.any (·.value == value) then continue
    let carrier ← sourceCarrier ⟨value, some category⟩
    unless ← withoutModifyingState <| isDefEq carrier.value expected do continue
    let proof ← withLocalDeclD `elementOwner (← inferType value) fun object => do
      let carrier ← sourceCarrier ⟨object, some category⟩
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
