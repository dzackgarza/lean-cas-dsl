module

public import CasCompiler.RoutedMethodFamily
public import CasCompiler.SourceReference

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The accepted property proposition over a complete rigid source category family.
Its native result is Prop. Computational observations of that proposition are not proofs. -/
structure PropertyFamily where
  private mk ::
  entry : PropertyEntry
  classifier : ClassifierEntry
  route : Route
  categoryFamily : Expr
  family : Expr
  actions : Array Expr
  universeParams : List Name
  parameterCount : Nat

/-- Retain an exact accepted property, classifier and structural route before specialization.
Reuse: PropertyEntry, nativeRouteFunctor, Classifier.Holds and whole-family universe closure. -/
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
    let expected ← mkAppM ``LeanCategories.Classifier #[selected.target]
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
    expressions.drop 2, universes, count⟩

def PropertyFamily.instantiate (family : PropertyFamily) : MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)

/-- Retain the complete original application beside Holds' native image, using the existing
typed Function.const provenance layout. Holds remains the proposition's literal native head;
the retained application supplies parameter and receiver occurrences independently of its image. -/
def PropertyFamily.mark (family : PropertyFamily) (applied : Expr) : MetaM Expr := do
  unless applied.getAppNumArgs == family.parameterCount + 1 do
    throwError "the property lost its complete original source application"
  let proposition := applied.headBeta
  unless proposition.isAppOfArity ``CasCatalogue.Classifier.Holds 3 do
    throwError "the property family lost its native Holds proposition"
  let image ← mkAppM ``Function.const #[← inferType applied, proposition.appArg!, applied]
  let image := Expr.mdata (KVMap.empty.setName `CasCompiler.source.propertyApplication
    ``PropertyFamily) image
  return .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``PropertyEntry
    |>.setString `CasCompiler.source.id family.entry.id.raw
    |>.setName `CasCompiler.source.declaration family.classifier.declaration
    |>.setString `CasCompiler.source.propertySource (toJson family.route.source).compress
    |>.setString `CasCompiler.source.propertyRoute (toJson family.route.refs).compress)
    (mkApp proposition.appFn! image)

/-- The source reader and deferred children form the same complete native proposition.
Route alternatives are compared before specializing any category parameter or receiver. -/
opaque PropertyFamily.forReceiver (selected : NativeSourceCategory) (id : PropertyId)
    (receiver : Expr) : MetaM (PropertyFamily × Expr) := do
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
  let some route := routes[0]?
    | throwError "the property is not reachable from the receiver's category"
  let agreements ← sourceRouteAgreements state selected routes
  let family ← PropertyFamily.forSelection selected.expression entry.id route.refs
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
  let .mdata data proposition ← family.mark applied
    | throwError "the property lost its complete source marker"
  let mut proposition := proposition
  for proof in agreements.reverse do
    proposition ← withLetDecl (← mkFreshUserName `propertyRouteAgreement)
      (← inferType proof) proof fun binding => mkLetFVars #[binding] proposition
        (usedLetOnly := false) (generalizeNondepLet := false)
  return (family, .mdata data proposition)

def PropertyFamily.fromMark (data : MData) : MetaM PropertyFamily := do
  unless data.getName `CasCompiler.source.kind == ``PropertyEntry do
    throwError "the property lost its original source marker"
  let source ← IO.ofExcept <| ((Json.parse (data.getString `CasCompiler.source.propertySource)).bind
    (fromJson? (α := CategoryExpr))).mapError IO.userError
  let route ← IO.ofExcept <| ((Json.parse (data.getString `CasCompiler.source.propertyRoute)).bind
    (fromJson? (α := Array EdgeRef))).mapError IO.userError
  let family ← PropertyFamily.forSelection source ⟨data.getString `CasCompiler.source.id⟩ route
  unless data.getName `CasCompiler.source.declaration == family.classifier.declaration do
    throwError "the property marker changed its accepted classifier declaration"
  return family

private partial def propertyBody (source : Expr) : MetaM Expr := do
  match ← instantiateMVars source with
  | .mdata data body =>
    if data.contains `CasCompiler.lower.value then
      throwError "a property source cannot replace its proposition with a retained value"
    propertyBody body
  | .letE _ _ value body _ =>
    unless ← isProof value do
      throwError "a property source lost its native proposition boundary"
    propertyBody (body.instantiate1 value)
  | value => pure value

/-- Read the explicitly retained original source application, then validate its complete
native proposition. No parameter or receiver is inferred from the resultant classifier image. -/
opaque PropertyFamily.application (family : PropertyFamily) (source : Expr) :
    MetaM (List Level × Array Expr × Expr) := do
  let body ← propertyBody source
  unless body.isAppOfArity ``CasCatalogue.Classifier.Holds 3 do
    throwError "the property changed its complete native Holds proposition"
  let .mdata data retained := body.appArg!
    | throwError "the property lost its original source application witness"
  unless data.getName `CasCompiler.source.propertyApplication == ``PropertyFamily &&
      retained.isAppOfArity ``Function.const 4 do
    throwError "the property changed its typed source application witness"
  let applied := retained.getAppArgs[3]!
  let (head, levels) ← family.instantiate
  unless applied.getAppNumArgs == family.parameterCount + 1 &&
      (← isDefEq head applied.getAppFn) do
    throwError "the property changed its complete original source family application"
  let parameters := applied.getAppArgs.extract 0 family.parameterCount
  let some receiver := applied.getAppArgs[family.parameterCount]?
    | throwError "the property lost its original receiver position"
  unless ← isDefEq applied body do
    throwError "the property changed its selected classifier, route or original receiver"
  let parameters ← parameters.mapM instantiateMVars
  let levels ← levels.mapM instantiateLevelMVars
  let receiver ← instantiateMVars receiver
  if parameters.any (fun parameter => parameter.hasMVar || parameter.hasLevelMVar) ||
      receiver.hasMVar || receiver.hasLevelMVar || levels.any (·.hasMVar) then
    throwError "the property leaves a complete source parameter undetermined"
  return (levels, parameters, receiver)

def PropertyFamily.specializeActions (family : PropertyFamily) (levels : List Level)
    (arguments : Array Expr) : MetaM (Array Expr) := do
  unless levels.length == family.universeParams.length &&
      arguments.size == family.parameterCount do
    throwError "the property changed its complete category parameter telescope"
  return family.actions.map fun action =>
    (mkAppN (action.instantiateLevelParams family.universeParams levels) arguments).headBeta

/-- Recognize only an original property source marker through ordinary native aliases.
This selects an observation contract, never a mathematical truth value. -/
partial def propertySource? (source : Expr) : MetaM (Option (MData × Expr)) := do
  match ← instantiateMVars source with
  | .mdata data body =>
    if data.getName `CasCompiler.source.kind == ``PropertyEntry then return some (data, body)
    propertySource? body
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => propertySource? value
    | none => pure none
  | .letE _ _ value body _ => propertySource? (body.instantiate1 value)
  | value =>
    let reduced := value.headBeta
    if reduced == value then pure none else propertySource? reduced

end CasCompiler
