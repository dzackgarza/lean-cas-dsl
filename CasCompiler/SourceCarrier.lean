module

public import CasCompiler.Resolve
public import CasCompiler.SourceTypeOrigin

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

private structure CarrierCategoryFamily where
  value : Expr
  universes : List Name

-- Reuse the named-category and unary-constructor family rules in Resolve.lean.
-- All source parameters and universes stay rigid while comparing complete functors.
private partial def carrierCategoryFamily (state : SemanticState) (source : CategoryExpr) :
    MetaM CarrierCategoryFamily := do
  let value ← nativeCategoryFamily state source fun _ => do
    return .param (← mkFreshUserName `carrierUniverse)
  let levels : CollectLevelParams.State := {}
  return ⟨value, (levels.collect value).params.toList⟩

private def carrierRoutes (source : CategoryExpr) : TermElabM (Array Route) := do
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
    (routes : Array Route) : TermElabM (Array Expr) := do
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

/-- Consume a supplied carrier prefix, or the complete structural carrier family.
Only checked uniform native equality identifies implicit alternatives. Actual functor
actions, original objects or arrows, route references and equality evidence remain in the term.
Source: ObjectRefinement, structuralEdges and the native family-conversion rule. -/
opaque sourceCarrier (source : NativeSourceJudgement) : TermElabM NativeSourceJudgement := do
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
      value ← match category.role with
        | .object => functorObject action value target
        | .morphism => mkAppM ``CategoryTheory.Functor.map #[action, value]
      bundle := target
    selectedEdges := selected.refs
    start := selected.target
  let routes ← carrierRoutes start
  let proofs ← sourceRouteAgreements state ⟨category.role, start, bundle, none⟩ routes
  let some route := routes[0]?
    | throwError "carrier formation requires its source route"
  if !route.steps.isEmpty then
    let selected ← nativeRouteFunctor state route bundle
    value ← match category.role with
      | .object => functorObject selected.functor value selected.target
      | .morphism => mkAppM ``CategoryTheory.Functor.map #[selected.functor, value]
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
  return ⟨value, some ⟨category.role, .atom CategoryId.sets, bundle, selection⟩⟩

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
  let carrier ← sourceCarrier ⟨object, some ⟨.object, source.expression, bundle, selection⟩⟩
  return (← sourceTypeOrigin? carrier.value).map (·.type) |>.getD carrier.value

/-- Apply the selected complete carrier functor to an arrow before taking its function.
Ordinary native functions retain their original expression and context. -/
def sourceFunction (source : NativeSourceJudgement) : TermElabM Expr := do
  if source.category.any (·.role == .morphism) then
    let carrier ← sourceCarrier source
    sourceSetFunction carrier.value
  else pure source.value

/-- The actual object and checked whole carrier family that supply an element type. -/
structure NativeSourceElementOwner where
  category : NativeSourceCategory
  value : Expr
  evidence : Expr

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
    let category ← match origin with
      | some origin => pure (some origin.category)
      | none => if let .fvar id := value then categoryOf id else pure none
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
          pure (some ⟨.object, category.expression, bundle, carrier⟩)
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
