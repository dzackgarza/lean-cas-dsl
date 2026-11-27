module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.RoutedMethodFamily
public import CasCompiler.SourceReference

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue




opaque PropertyFamily.forSelection (source : CategoryExpr) (id : PropertyId)
    (refs : Array EdgeRef) : MetaM PropertyFamily := withLCtx {} #[] do
  let state ← semanticState
  let some entry := state.properties.find? (·.id == id)
    | throwError "the selected property is absent from the source registry"
  unless entry.receiver.all (·.syntacticEq source) do
    throwError "the property has a different complete source category"
  let some classifier := state.classifier? entry.classifier
    | throwError "the property lost its accepted classifier"
  discard <| checkedDeclaration classifier.declaration
  discard <| checkedDeclaration ``CasCatalogue.Classifier.Holds
  let query ← SourceRoutes.forOwner source classifier.host
  let some routes ← query.finiteRoutes
    | throwUnsupportedSource "the property route family requires its supplied uniform comparison"
  let #[route] := routes.filter (fun route => route.refs == refs &&
      route.target.syntacticEq classifier.host)
    | throwError "the property lost its exact complete source route"
  let actionFamilies ← route.refs.mapM SourceActionFamily.forEdge
  let receiverViews ← sourceReceiverViewPlans state route
  let categoryFamily ← nativeCategoryFamily state source fun _ => mkFreshLevelMVar
  let (family, actions, count) ←
      forallTelescopeReducing (← inferType categoryFamily) fun parameters _ => do
    let bundle := mkAppN categoryFamily parameters
    let selected ← nativeRouteFunctor state route bundle
    let classifierValue ← classifierInstance classifier
    let rigid := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false)
      classifierValue `propertyUniverse
    setMCtx rigid.mctx
    let classifierValue := rigid.expr
    let declared ← inferType classifierValue
    let declared ← if declared.isAppOfArity ``LeanCategories.Classifier 1 then pure declared
      else whnfR declared
    unless declared.isAppOfArity ``LeanCategories.Classifier 1 do
      throwError "the accepted property declaration lost its complete native classifier type"


    let expected := mkApp declared.getAppFn selected.target
    unless ← withoutModifyingState <| isDefEq (← inferType classifierValue) expected do
      unless ← expandSourceStructures ((← getMVars classifierValue).map mkMVar) do
        throwError "the property's classifier has inconsistent native category parameters"
    unless ← isDefEq (← inferType classifierValue) expected do
      throwError "the property classifier has a different complete native host"
    let classifierValue ← instantiateMVars classifierValue
    let sourceType ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    let callable ← withLocalDeclD `propertyReceiver sourceType fun receiver => do
      let image ← if route.refs.isEmpty then pure receiver
        else functorObject selected.functor receiver selected.target
      let proposition ← mkAppM ``CasCatalogue.Classifier.Holds #[classifierValue, image]
      mkLambdaFVars #[receiver] proposition (usedOnly := false) (usedLetOnly := false)
    let close := fun term => do
      mkLambdaFVars parameters (← instantiateMVars term)
        (usedOnly := false) (usedLetOnly := false)
    return (← close callable, ← selected.actions.mapM close, parameters.size)
  let (expressions, universes) ← closeRoutedUniverses (#[categoryFamily, family] ++ actions)
  return ⟨entry, classifier, route, expressions[0]!, expressions[1]!,
    expressions.drop 2, actionFamilies, receiverViews, universes, count⟩

def PropertyFamily.instantiate (family : PropertyFamily) : MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)



def PropertyFamily.selected (family : PropertyFamily) (levels : List Level)
    (parameters : Array Expr) (receiver : Expr) : MetaM (SourceSelection Expr) := do
  unless levels.length == family.universeParams.length &&
      parameters.size == family.parameterCount do
    throwError "the property lost its complete original source application"
  let applied := mkAppN (family.family.instantiateLevelParams family.universeParams levels)
    (parameters.push receiver)
  let proposition := applied.headBeta
  unless proposition.isAppOfArity ``CasCatalogue.Classifier.Holds 3 do
    throwError "the property family lost its native Holds proposition"
  check proposition
  return {
    value := proposition
    originalApplication := some applied
    observation := some (.classifier family.classifier)
    application := some {
      family := .property family
      universes := levels
      parameters
      arguments := #[receiver] } }



opaque PropertyFamily.atReceiver (family : PropertyFamily) (selected : NativeSourceCategory)
    (receiver : Expr) : MetaM (SourceSelection Expr) := do
  unless selected.role == .object do
    throwError "a property requires its selected source object category"
  unless family.route.source.syntacticEq selected.expression do
    throwError "the property changed its complete selected source category"
  let (head, levels) ← family.instantiate
  let category := family.categoryFamily.instantiateLevelParams family.universeParams levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType category)
  unless ← isDefEq (mkAppN category parameters) selected.bundle do
    throwError "the property changed its complete selected category parameters"
  let domain ← mkAppM ``CategoryTheory.Bundled.α #[selected.bundle]
  unless ← isDefEq (← inferType receiver) domain do
    throwError "the property receiver has a different complete native source category"
  let applied ← instantiateMVars (mkAppN head (parameters.push receiver))
  if applied.hasMVar || applied.hasLevelMVar then
    throwError "the property leaves a complete source parameter undetermined"
  family.selected (← levels.mapM instantiateLevelMVars)
    (← parameters.mapM instantiateMVars) (← instantiateMVars receiver)




opaque PropertyFamily.forReceiver (selected : NativeSourceCategory) (id : PropertyId)
    (receiver : Expr) : MetaM (PropertyFamily × SourceSelection Expr) := do
  unless selected.role == .object do
    throwError "a property requires its selected source object category"
  let state ← semanticState
  let some entry := state.properties.find? (·.id == id)
    | throwError "the selected property is absent from the source registry"
  let some classifier := state.classifier? entry.classifier
    | throwError "the property lost its accepted classifier"
  let query ← SourceRoutes.forOwner selected.expression classifier.host
  let some routes ← query.finiteRoutes
    | throwUnsupportedSource "the property route family requires its supplied uniform comparison"
  let preferred ← preferredRoute? state selected.expression entry.name routes
  let routes := match preferred with
    | none => routes
    | some route => routes.filter (·.refs == route.refs)
  let some route := routes[0]?
    | throwError "the property is not reachable from the receiver's category"
  let agreements ← sourceRouteAgreements state selected routes
  let family ← PropertyFamily.forSelection selected.expression entry.id route.refs
  let selected ← family.atReceiver selected receiver
  let mut proposition := selected.value
  for proof in agreements.reverse do
    proposition ← withLetDecl (← mkFreshUserName `propertyRouteAgreement)
      (← inferType proof) proof fun binding => mkLetFVars #[binding] proposition
        (usedLetOnly := false) (generalizeNondepLet := false)
  return (family, { selected with value := proposition })

def PropertyFamily.specializeActions (family : PropertyFamily) (levels : List Level)
    (arguments : Array Expr) : MetaM (Array Expr) := do
  unless levels.length == family.universeParams.length &&
      arguments.size == family.parameterCount do
    throwError "the property changed its complete category parameter telescope"
  return family.actions.map fun action =>
    (mkAppN (action.instantiateLevelParams family.universeParams levels) arguments).headBeta




private partial def originalPropertyProposition (context : OpenContext)
    (selections : SourceSelectionScope Expr) (expression : Expr)
    (seen : Array BindingId := #[]) : MetaM Expr := do
  if let .fvar localId := expression then
    if let some binding := context.bindings.find? (·.expression.fvarId! == localId) then
      if let some selected := selections[binding.id]? then
        unless selected.formalBindings.isEmpty && !seen.contains binding.id do
          throwError "the property source lost its complete original value alias"
        return ← originalPropertyProposition context selections selected.value (seen.push binding.id)
    if let some value := (← localId.getDecl).value? then
      return ← originalPropertyProposition context selections value seen
    return expression
  match expression with
  | .mdata _ body => originalPropertyProposition context selections body seen
  | .letE _ type value body _ =>
    unless ← isProp type do
      throwError "the property source introduced a data-bearing proposition alias"
    originalPropertyProposition context selections (body.instantiate1 value) seen
  | _ => pure expression




opaque PropertyFamily.checkSelection (family : PropertyFamily) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (selected : SourceSelection Expr) : MetaM Unit := do
  let some application := selected.application
    | throwError "the property source lost its complete original application"
  unless (SelectedApplicationFamily.property family).exactlyMatches application.family &&
      application.universes.length == family.universeParams.length &&
      application.parameters.size == family.parameterCount &&
      application.arguments.size == 1 && application.owner.isNone &&
      application.ownerSelection.isNone do
    throwError "the property source changed its complete selected family or input positions"
  let applied := mkAppN
    (family.family.instantiateLevelParams family.universeParams application.universes)
    (application.parameters ++ application.arguments)
  let some original := selected.originalApplication
    | throwError "the property source lost its original native application"
  unless original.equal applied do
    throwError "the property source witness changed its original native proposition"
  let expected := applied.headBeta
  unless expected.isAppOfArity ``CasCatalogue.Classifier.Holds 3 do
    throwError "the property source lost its original Holds proposition"
  let actual ← originalPropertyProposition context selections selected.value
  unless actual.equal expected do
    throwError "the property source witness changed its original native proposition"
  check expected

end CasCompiler
