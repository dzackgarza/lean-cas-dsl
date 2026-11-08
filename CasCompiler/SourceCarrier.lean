module

public import CasCompiler.Resolve

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
  match state.categories.filter (·.expression.syntacticEq source) with
  | #[entry] =>
    let info ← checkedDeclaration entry.declaration
    let universes ← info.levelParams.mapM fun _ => mkFreshUserName `carrierUniverse
    return ⟨mkConst entry.declaration (universes.map Level.param), universes⟩
  | #[] =>
    let .construct id #[.category argument] := source
      | throwUnsupportedSource "carrier comparison requires its complete source category family"
    let some constructor := state.constructor? id
      | throwError "the carrier category constructor is absent"
    unless constructor.signature == #[.category] do
      throwUnsupportedSource "carrier comparison requires its declared constructor parameters"
    discard <| checkedDeclaration constructor.semantics
    let family ← carrierCategoryFamily state argument
    let value ← forallTelescopeReducing (← inferType family.value) fun parameters _ => do
      let category := mkAppN family.value parameters
      let result ← applyConstructorInterface constructor.semantics #[category] #[category]
      mkLambdaFVars parameters result
    return ⟨value, family.universes⟩
  | _ => throwSemanticAmbiguity "carrier comparison requires one complete source category family"

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
private def carrierAgreements (state : SemanticState) (source : NativeSourceCategory)
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
actions, original objects, route references and equality evidence remain in the term.
Source: ObjectRefinement, structuralEdges and the native family-conversion rule. -/
opaque sourceCarrier (source : NativeSourceJudgement) : TermElabM NativeSourceJudgement := do
  let some category := source.category
    | do
      discard <| getLevel source.value
      return source
  unless category.role == .object do throwError "a source function domain must be an object"
  if category.expression.syntacticEq (.atom CategoryId.sets) then
    discard <| getLevel source.value
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
      value ← functorObject action value target
      bundle := target
    selectedEdges := selected.refs
    start := selected.target
  let routes ← carrierRoutes start
  let proofs ← carrierAgreements state ⟨.object, start, bundle, none⟩ routes
  let some route := routes[0]?
    | throwError "carrier formation requires its source route"
  if !route.steps.isEmpty then
    let selected ← nativeRouteFunctor state route bundle
    value ← functorObject selected.functor value selected.target
    bundle := selected.target
  for proof in proofs.reverse do
    let body := value
    value ← withLetDecl (← mkFreshUserName `carrierAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] body
        (usedLetOnly := false) (generalizeNondepLet := false)
  let refs := reprStr (routes.map fun route => selectedEdges ++ route.refs)
  value := .mdata (KVMap.empty.setString `CasCompiler.source.carrierRoutes refs) value
  let selection := category.carrier.map fun selected =>
    { selected with refs := #[], target := .atom CategoryId.sets, actions := #[] }
  return ⟨value, some ⟨.object, .atom CategoryId.sets, bundle, selection⟩⟩

end CasCompiler
