module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.SourceCarrier
public import CasCompiler.RoutedMethodReturn
public import CasCompiler.Layout
public import CasCompiler.InputCoverage
public import CasCompiler.FamilyConversion
public import CasContract.Port

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue




opaque closeRoutedUniverses (expressions : Array Expr) : MetaM (Array Expr × List Name) := do
  let mut used : CollectLevelParams.State := {}
  for expression in expressions do used := used.collect (← instantiateMVars expression)
  for expression in expressions do
    let generalized := (← getMCtx).levelMVarToParam used.params.contains (fun _ => false)
      (← instantiateMVars expression) `methodUniverse
    setMCtx generalized.mctx
    used := used.collect generalized.expr
  let expressions ← expressions.mapM instantiateMVars
  if expressions.any (fun expression =>
      expression.hasFVar || expression.hasMVar || expression.hasLevelMVar) then
    throwUnsupportedSource "the source family requires its complete declaration parameters"
  let mut levels : CollectLevelParams.State := {}
  for expression in expressions do levels := levels.collect expression
  let originalUniverses := levels.params.toList
  let universes := (List.range originalUniverses.length).map fun index =>
    (`routedUniverse).appendIndexAfter index
  return (expressions.map (fun expression =>
    expression.instantiateLevelParams originalUniverses (universes.map Level.param)), universes)




def sourceReceiverViewPlans (state : SemanticState) (route : Route) :
    MetaM (Array (Option ConstructorEntry)) := do
  (#[route.source] ++ route.steps.map (·.target)).mapM fun category => do
    match category with
    | .construct constructor _ =>
      let #[entry] := state.constructors.filter (·.id == constructor)
        | throwError "the source route lost its unique original receiver constructor"
      return some entry
    | _ => return none




private opaque routedMethodWithReturns (route : Route) (method : MethodEntry)
    (returnRows : Array LiftEntry) (returning : Route) : MetaM RoutedMethodFamily := withLCtx {} #[] do
  let state ← semanticState
  let some registered := state.methods.find? (·.id == method.id)
    | throwError "the routed method is not registered"
  unless registered.functor == method.functor && registered.name == method.name &&
      registered.shape == method.shape && registered.returnsToSource == method.returnsToSource &&
      registered.owner.syntacticEq method.owner && route.target.syntacticEq method.owner do
    throwError "the routed method changed its independently selected owner"
  let query ← SourceRoutes.forMethod route.source method.name
  let some routes ← query.finiteRoutes
    | throwUnsupportedSource "method inheritance requires its supplied uniform comparison"
  unless routes.any (fun selected => selected.exactlyMatches route) do
    throwError (MessageData.tagged `CasCompiler.RoutedMethodFamily.invalidRoute
      m!"the selected method route is not a complete first-hit source route")


  if method.returnsToSource && !route.refs.isEmpty then
    unless !returning.refs.isEmpty && returnRows.size == returning.refs.size do
      throwUnsupportedSource "source method lifting requires its actual selected return data"
    unless returning.source.syntacticEq route.source &&
        returning.target.syntacticEq route.target &&
        routes.any (fun selected => selected.exactlyMatches returning) do
      throwError "the selected method return route is not an original first-hit source route"
  else unless returnRows.isEmpty do
    throwError "the method has no declared return positions"
  let some entry := state.functor? method.functor
    | throwError "the source method has no registered functor"
  discard <| checkedDeclaration entry.declaration
  let actionFamilies ← (route.refs.push (.functor entry.id)).mapM SourceActionFamily.forEdge
  let receiverViews ← sourceReceiverViewPlans state route



  let categoryFamily ← nativeCategoryFamily state route.source fun _ => mkFreshLevelMVar
  let (functorFamily, family, actions, returns, count) ←
      forallTelescopeReducing (← inferType categoryFamily) fun parameters _ => do
    let bundle := mkAppN categoryFamily parameters
    let selected ← nativeRouteFunctor state route bundle
    let transport ← match method.shape with
      | .object => pure selected.functor
      | .isoInvariant => mkAppM ``CategoryTheory.Functor.core #[selected.functor]
    let function ← registeredFunctorInstance entry
    let rigid := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false)
      function `methodUniverse
    setMCtx rigid.mctx
    let function := rigid.expr
    let (_, expected) ← functorCategoryBundles transport
    let (declared, _) ← functorCategoryBundles function



    unless ← withoutModifyingState <| isDefEq declared expected do
      unless ← expandSourceStructures ((← getMVars function).map mkMVar) do
        throwError "the method functor has inconsistent native category parameters"
    unless ← isDefEq declared expected do
      throwError "the method functor has a different complete selected source category"
    let complete ← instantiateMVars (← mkFunctorComp transport function)
    let actions ← (selected.actions.push function).mapM instantiateMVars
    if complete.hasMVar || actions.any (·.hasMVar) then
      throwUnsupportedSource "the source method requires its complete declaration parameters"
    let (_, target) ← functorCategoryBundles complete
    let sourceType ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    let callable ← withLocalDeclD `methodReceiver sourceType fun receiver => do
      let input ← match method.shape with
        | .object => pure receiver
        | .isoInvariant => mkAppM ``CategoryTheory.Core.mk #[receiver]
      mkLambdaFVars #[receiver] (← functorObject complete input target)
        (usedOnly := false) (usedLetOnly := false)
    let close := fun term => mkLambdaFVars parameters term
      (usedOnly := false) (usedLetOnly := false)
    let returns ← if returnRows.isEmpty then pure none else do
      let returnSelected ← if returning.refs == route.refs then pure selected
        else nativeRouteFunctor state returning bundle
      let agreement ← if returning.refs == route.refs then pure none else do
        let some proof ← methodReturnRouteAgreement? state route returning bundle
          | throwSemanticAmbiguity "method return routes require whole-family equality"
        unless ← isDefEq (← inferType proof)
            (← mkEq (← instantiateMVars selected.functor)
              (← instantiateMVars returnSelected.functor)) do
          throwError "the method return agreement changed the actual transport"
        pure (some proof)
      let evidences ← (returnRows.zip (returning.refs.zip returnSelected.actions)).mapM
        fun (row, edge, action) => methodReturnEvidence state row edge action
      let (resultCategory, resultBundle) ← methodReturnCategory state route.source bundle
      let resultFamily ← withLocalDeclD `methodReceiver sourceType fun receiver => do
        let result ← applyMethodReturns returnRows evidences returnSelected.actions receiver
          (mkApp callable receiver)
          (fun selected expected => do
            if let some expected := expected then
              return ← mkExpectedTypeHint selected.value expected
            return selected.value)
          (fun _ _ action original => do
            let (_, target) ← functorCategoryBundles action
            functorObject action original target)
        let result ← retainMethodReturnAgreement agreement result
        unless ← isDefEq (← inferType result)
            (← mkAppM ``CategoryTheory.Bundled.α #[resultBundle]) do
          throwError "the returning method changed its complete selected result category"
        mkLambdaFVars #[receiver] result (usedOnly := false) (usedLetOnly := false)
      pure (some ({
        route := returning
        rows := returnRows
        actions := ← returnSelected.actions.mapM close
        actionFamilies := ← returning.refs.mapM SourceActionFamily.forEdge
        agreement := ← agreement.mapM close
        evidences := ← evidences.mapM close
        category := resultCategory
        categoryFamily := ← close resultBundle
        resultFamily := ← close resultFamily } : RoutedMethodReturn))
    return (← close complete, ← close callable, ← actions.mapM close, returns, parameters.size)
  let returnExpressions := returns.toArray.flatMap fun returned =>
    #[returned.categoryFamily, returned.resultFamily] ++ returned.evidences ++
      returned.actions ++ returned.agreement.toArray
  let (expressions, universes) ← closeRoutedUniverses
    (#[categoryFamily, functorFamily, family] ++ actions ++ returnExpressions)



  if returns.isSome then
    for expression in expressions do checkWithKernel expression
  let returns := returns.map fun returned =>
    let start := 5 + actions.size
    let afterEvidence := start + returned.evidences.size
    let afterActions := afterEvidence + returned.actions.size
    { returned with
      categoryFamily := expressions[3 + actions.size]!
      resultFamily := expressions[4 + actions.size]!
      evidences := expressions.extract start afterEvidence
      actions := expressions.extract afterEvidence afterActions
      agreement := if returned.agreement.isSome then expressions[afterActions]? else none }
  return ⟨method, route, entry, expressions[0]!, expressions[1]!,
    expressions[2]!, expressions.extract 3 (3 + actions.size), actionFamilies, receiverViews,
    universes, count, returns⟩



opaque RoutedMethodFamily.forRoute (route : Route) (method : MethodEntry) :
    MetaM RoutedMethodFamily :=
  routedMethodWithReturns route method #[] route



opaque RoutedMethodFamily.forRouteWithReturns (route : Route) (method : MethodEntry)
    (rows : Array LiftEntry) : MetaM RoutedMethodFamily :=
  routedMethodWithReturns route method rows route



opaque RoutedMethodFamily.forComparedReturn (route : Route) (method : MethodEntry)
    (returning : Route) (rows : Array LiftEntry) : MetaM RoutedMethodFamily :=
  routedMethodWithReturns route method rows returning

def RoutedMethodFamily.returnIdentities (family : RoutedMethodFamily) : Array String :=
  family.returns.toArray.flatMap fun returned => returned.rows.map (·.id.raw)

def RoutedMethodFamily.resultCategory (family : RoutedMethodFamily) : CategoryExpr :=
  family.returns.map (·.category) |>.getD family.functor.target

def RoutedMethodFamily.comparisonFamily (family : RoutedMethodFamily) : Expr :=
  family.returns.map (·.resultFamily) |>.getD family.functorFamily


def RoutedMethodFamily.forSelection (source : CategoryExpr) (method : String)
    (refs : Array EdgeRef) (returnIds : Array String := #[])
    (returnRefs : Option (Array EdgeRef) := none) : MetaM RoutedMethodFamily := do
  let some entry := (← semanticState).methods.find? (·.id.raw == method)
    | throwError "the selected routed method is absent from the source registry"
  let query ← SourceRoutes.forMethod source entry.name
  let some routes ← query.finiteRoutes
    | throwUnsupportedSource "method inheritance requires its supplied uniform comparison"
  let #[route] := routes.filter (fun route => route.refs == refs &&
      route.target.syntacticEq entry.owner)
    | throwError "the selected routed method lost its exact first-hit route"
  let state ← semanticState
  let rows ← returnIds.mapM fun id => do
    let #[row] := state.lifts.filter (·.id.raw == id)
      | throwSemanticAmbiguity "the selected method return lost its exact registered identity"
    pure row
  match returnRefs with
  | none => RoutedMethodFamily.forRouteWithReturns route entry rows
  | some refs =>
    let #[returning] := routes.filter (fun candidate => candidate.refs == refs &&
        candidate.target.syntacticEq entry.owner)
      | throwError "the selected method return lost its original route"
    RoutedMethodFamily.forComparedReturn route entry returning rows



def RoutedMethodFamily.atSource (source : CategoryExpr) (name : String) :
    MetaM (Array RoutedMethodFamily) := do
  let state ← semanticState
  let query ← SourceRoutes.forMethod source name
  let some routes ← query.finiteRoutes
    | throwUnsupportedSource "method inheritance requires its supplied uniform comparison"
  let mut families := #[]
  for route in routes do
    for entry in state.methods do
      if entry.name == name && entry.owner.syntacticEq route.target then
        if entry.returnsToSource && !route.refs.isEmpty then
          if let some alternatives := methodReturnRows? state route then
            for rows in alternatives do
              families := families.push (← RoutedMethodFamily.forRouteWithReturns route entry rows)
          else
            let category ← nativeCategoryFamily state source fun _ => mkFreshLevelMVar
            let mut returned := false
            for returning in routes do
              unless returning.target.syntacticEq route.target do continue
              let some alternatives := methodReturnRows? state returning | continue
              let agrees ← withoutModifyingState <| forallTelescopeReducing (← inferType category) fun parameters _ => do
                return (← methodReturnRouteAgreement? state route returning
                  (mkAppN category parameters)).isSome
              unless agrees do continue
              for rows in alternatives do
                families := families.push (← RoutedMethodFamily.forComparedReturn route entry returning rows)
                returned := true
            unless returned do
              throwUnsupportedSource "source method lifting requires its actual selected return data"
        else
          families := families.push (← RoutedMethodFamily.forRoute route entry)
  return families



def RoutedMethodFamily.agreementsWith (family : RoutedMethodFamily)
    (families : Array RoutedMethodFamily) (evidence : Array Expr) :
    MetaM (Array Expr) := do
  let mut proofs := #[]
  for other in families do
    unless family.route.source.syntacticEq other.route.source &&
        family.entry.name == other.entry.name do
      throwError "the compared method families have different source questions"
    if other.entry.id == family.entry.id && other.route.refs == family.route.refs &&
        other.returnIdentities == family.returnIdentities &&
        other.returns.map (·.route.refs) == family.returns.map (·.route.refs) then continue
    unless family.resultCategory.syntacticEq other.resultCategory do
      throwSemanticAmbiguity "method families have different complete result categories"
    let some proof ← sourceFamilyConversion family.comparisonFamily other.comparisonFamily evidence
      | throwSemanticAmbiguity "inherited methods require their supplied whole-family agreement"
    proofs := proofs.push proof
  return proofs




def RoutedMethodFamily.agreements (family : RoutedMethodFamily) (evidence : Array Expr) :
    MetaM (Array Expr) := do
  let families ← RoutedMethodFamily.atSource family.route.source family.entry.name
  let preferred ← preferredRoute? (← semanticState) family.route.source family.entry.name
    (families.map (·.route))
  let surviving := match preferred with
    | none => families
    | some route => families.filter (·.route.refs == route.refs)
  unless surviving.any (fun other => other.entry.id == family.entry.id &&
      other.route.refs == family.route.refs &&
      other.returnIdentities == family.returnIdentities &&
      other.returns.map (·.route.refs) == family.returns.map (·.route.refs)) do
    throwStratum .invalid "the selected method does not use its declared preferred route"
  family.agreementsWith surviving evidence

def RoutedMethodFamily.instantiate (family : RoutedMethodFamily) : MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)


def RoutedMethodFamily.selected (family : RoutedMethodFamily) (levels : List Level)
    (parameters : Array Expr) (receiver : Expr)
    (inputs : Option (Array (Array Expr)) := none) : MetaM (SourceSelection Expr) := do
  unless levels.length == family.universeParams.length &&
      parameters.size == family.parameterCount do
    throwError "the routed method changed its complete native parameter telescope"
  let value := mkAppN
    (family.family.instantiateLevelParams family.universeParams levels) (parameters.push receiver)
  check value
  return {
    value, reference := some (.method family.entry family.functor), originalApplication := some value
    application := some {
      family := .routedMethod family, universes := levels, parameters, arguments := #[receiver] }
    routedInputs := inputs }



def RoutedMethodFamily.specializeActions (family : RoutedMethodFamily) (levels : List Level)
    (arguments : Array Expr) : MetaM (Array Expr) := do
  unless levels.length == family.universeParams.length &&
      arguments.size == family.parameterCount do
    throwError "the routed method changed its complete category parameter telescope"
  return family.actions.map fun action =>
    (mkAppN (action.instantiateLevelParams family.universeParams levels) arguments).headBeta




structure MethodCategoryAssembly where
  private mk ::
  arity : Nat
  positions : Array Nat
  family : Expr



inductive MethodCategoryParameter
  | input (index : Nat) (path : Array Name)
  | fixed (source : Expr)
  | assembly (source : MethodCategoryAssembly)
  | unavailable

private def methodCategoryAssembly? (context : OpenContext) (originals : Array Expr)
    (parameter : Expr) : MetaM (Option MethodCategoryAssembly) := do
  let family ← mkLambdaFVars originals parameter (usedOnly := false) (usedLetOnly := false)
  let function ← SourceLayout.ofTerm (← context.close family)
  let arguments ← originals.mapM context.close
  let (_, application) ← ApplicationLayout.ofSource function context arguments
  let some required ← application.inputResultArguments | return none
  let dependencies ← localDependencies originals parameter
  let typeDependencies ← localDependencies originals (← inferType parameter)
  unless (dependencies ++ typeDependencies).all required.contains do return none
  let selected := required.map (fun index => originals[index]!)
  let family ← mkLambdaFVars selected parameter (usedOnly := false) (usedLetOnly := false)
  if family.hasFVar || family.hasMVar || family.hasLevelMVar then return none
  return some ⟨originals.size, required, family⟩

private def sourceCategoryRoutesAt (categoryFamily : Expr) (universeParams : List Name)
    (parameterCount : Nat) (originals : Array Expr) (result : Expr) : MetaM (Array MethodCategoryParameter) := do
  let levels ← universeParams.mapM fun _ => mkFreshLevelMVar
  let category := categoryFamily.instantiateLevelParams universeParams levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType category)
  unless parameters.size == parameterCount do
    throwError "the routed method lost its complete abstract category telescope"
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[mkAppN category parameters]
  unless ← isDefEq expected result do return Array.replicate parameters.size .unavailable
  let parameters ← parameters.mapM instantiateMVars
  let bindings := originals.mapIdx fun index expression =>
    ({
      id := {
        session := "method-category-parameter"
        serial := index }
      role := BindingRole.parameter
      expression := expression } : LocalBinding)
  let context ← ContextTelescope.capture bindings
  parameters.mapM fun parameter => do
    if parameter.hasMVar || parameter.hasLevelMVar then return .unavailable
    if !parameter.hasFVar then return .fixed parameter
    if let some selected ← (← context.close parameter).inputProjectionAt #[] (bindings.map (·.id)) then
      if let .context id := selected.target then
        let some index := bindings.findIdx? (·.id == id)
          | throwError "the category parameter lost its original rigid declaration slot"
        return .input index selected.path
    if let some assembly ← methodCategoryAssembly? context originals parameter then
      return .assembly assembly
    return .unavailable






opaque sourceCategoryParameterRoutes (categoryFamily : Expr) (universeParams : List Name)
    (parameterCount : Nat) (declaration : Name) (morphism : Bool := false) : MetaM (Array MethodCategoryParameter) :=
    withLCtx {} #[] do
  let information ← checkedDeclaration declaration
  let declared := mkConst declaration (information.levelParams.map Level.param)
  forallTelescopeReducing (← inferType declared) fun originals result => do
    let result ← if morphism then
        inferType (← mkAppM ``CategoryTheory.Arrow.mk #[mkAppN declared originals])
      else pure result
    sourceCategoryRoutesAt categoryFamily universeParams parameterCount originals result






opaque sourceCategoryProjectionInputRoutes (categoryFamily : Expr)
    (universeParams : List Name) (parameterCount : Nat) (declaration : Name) (path : Array Name) (position : Nat) (inputDeclaration : Name) :
    MetaM (Array MethodCategoryParameter) := withLCtx {} #[] do
  let unavailable := Array.replicate parameterCount MethodCategoryParameter.unavailable
  let information ← checkedDeclaration inputDeclaration
  let input := mkConst inputDeclaration (information.levelParams.map Level.param)
  forallTelescopeReducing (← inferType input) fun originals _ => do
    discard <| checkedDeclaration declaration
    let outer ← mkConstWithFreshMVarLevels declaration
    let (arguments, binders, _) ← forallMetaTelescopeReducing (← inferType outer)
    let mut explicit := #[]
    for argument in arguments, binder in binders, index in [:arguments.size] do
      if binder.isExplicit && !(← isProof argument) then explicit := explicit.push index
    unless explicit == #[position] do return unavailable
    let some selected := arguments[position]? | return unavailable
    let actual := mkAppN input originals
    unless ← isDefEq (← inferType selected) (← inferType actual) <&&>
        isDefEq selected actual do return unavailable
    let produced ← instantiateMVars (mkAppN outer arguments)
    if produced.hasMVar || produced.hasLevelMVar then return unavailable
    let mut result := produced
    for projection in path do
      unless ((← getEnv).getProjectionFnInfo? projection).isSome do
        throwError "the selected producer result lost its native projection declaration"
      result ← mkAppM projection #[result]
    sourceCategoryRoutesAt categoryFamily universeParams parameterCount originals (← inferType result)


def RoutedMethodFamily.receiverParameterRoutes (family : RoutedMethodFamily)
    (declaration : Name) (morphism : Bool := false) : MetaM (Array MethodCategoryParameter) :=
  sourceCategoryParameterRoutes family.categoryFamily family.universeParams family.parameterCount
    declaration morphism

def RoutedMethodFamily.receiverProjectionInputRoutes (family : RoutedMethodFamily)
    (declaration : Name) (path : Array Name) (position : Nat) (inputDeclaration : Name) :
    MetaM (Array MethodCategoryParameter) :=
  sourceCategoryProjectionInputRoutes family.categoryFamily family.universeParams family.parameterCount
    declaration path position inputDeclaration

private def projectionArgument (name : Name) (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData
  unless expression.getAppFn.isConstOf name do
    throwError "the routed action changed its native wrapper {name}"
  let info ← getFunInfoNArgs expression.getAppFn expression.getAppNumArgs
  let mut explicit := #[]
  for argument in expression.getAppArgs, index in [:expression.getAppNumArgs] do
    if (info.paramInfo[index]?.map (·.isExplicit)).getD false then
      explicit := explicit.push argument
  let #[argument] := explicit
    | throwError "the routed action wrapper lost its single declared input"
  return argument

private def declaredApplication (name : Name) (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData
  unless expression.getAppFn.isConstOf name do
    throwError "the routed action lost its original declaration {name}"
  let arity ← forallTelescopeReducing (← inferType expression.getAppFn)
    fun parameters _ => pure parameters.size
  unless expression.getAppNumArgs == arity do
    throwError "the routed action lost its complete original declaration telescope"
  return expression




private partial def routedActionApplicationCore (edge : EdgeRef)
    (references : List SelectedSourceReference) (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData
  match edge, references with
  | .functor id, [.functor entry] =>
    unless entry.id == id do
      throwError "the routed functor changed its complete selected row"
    let expression ← if expression.getAppFn.isConstOf ``CategoryTheory.Cat.Hom.toFunctor then
        projectionArgument ``CategoryTheory.Cat.Hom.toFunctor expression
      else pure expression
    declaredApplication entry.declaration expression
  | .classifierForget id, [.classifierForget entry] =>
    unless entry.id == id do
      throwError "the routed classifier changed its complete selected row"
    let expression ← projectionArgument ``CategoryTheory.Cat.Hom.toFunctor expression
    let expression ← projectionArgument ``LeanCategories.Classifier.forget expression
    let expression ← if expression.getAppFn.isConstOf ``LeanCategories.PropertyClassifier.toClassifier then
        projectionArgument ``LeanCategories.PropertyClassifier.toClassifier expression
      else if expression.getAppFn.isConstOf ``LeanCategories.StructureClassifier.toClassifier then
        projectionArgument ``LeanCategories.StructureClassifier.toClassifier expression
      else pure expression
    declaredApplication entry.declaration expression
  | .constructMap constructor inner, .constructorInterface entry .functorialAction :: remaining =>
    unless entry.id == constructor do
      throwError "the routed constructor changed its complete selected row"
    let some action := entry.functorialAction
      | throwError "the routed constructor lost its declared action"
    let expression ← declaredApplication action expression
    routedActionApplicationCore inner remaining (← projectionArgument action expression)
  | _, _ => throwError "the routed action lost its complete original selected rows"


opaque routedActionApplication (family : SourceActionFamily) (expression : Expr) : MetaM Expr := do
  let declared ← routedActionApplicationCore family.edge family.references.toList expression
  unless declared.getAppFn.isConstOf family.declaration &&
      declared.getAppNumArgs == family.parameterCount &&
      declared.getAppFn.constLevels!.length == family.universeParams.length do
    throwError "the routed action changed its complete selected declaration"
  return declared




def routedActionParameters (family : SourceActionFamily) (expression : Expr) :
    MetaM (Array (Nat × Expr)) := do
  let declared ← routedActionApplication family expression
  let info ← getFunInfoNArgs declared.getAppFn declared.getAppNumArgs
  let mut parameters := #[]
  for argument in declared.getAppArgs, index in [:declared.getAppNumArgs] do
    if (info.paramInfo[index]?.map (·.isExplicit)).getD false && !(← isProof argument) then
      parameters := parameters.push (index, argument)
  return parameters

private def mapProjectionArgument (name : Name) (expression : Expr)
    (transform : Expr → MetaM Expr) : MetaM Expr := do
  discard <| projectionArgument name expression
  let info ← getFunInfoNArgs expression.getAppFn expression.getAppNumArgs
  let indices := (Array.range expression.getAppNumArgs).filter fun index =>
    (info.paramInfo[index]?.map (·.isExplicit)).getD false
  let #[index] := indices
    | throwError "the routed action wrapper changed its exact declared input position"
  let some original := expression.getAppArgs[index]?
    | throwError "the routed action wrapper lost its complete input"
  return mkAppN expression.getAppFn (expression.getAppArgs.set! index (← transform original))



private partial def mapRoutedAction (edge : EdgeRef)
    (references : List SelectedSourceReference) (expression : Expr)
    (transform : Expr → MetaM Expr) : MetaM Expr := do
  match edge, references with
  | .functor id, [.functor entry] =>
    unless entry.id == id do
      throwError "the routed functor changed its complete selected row"
    let declaredMap := fun expression => do transform (← declaredApplication entry.declaration expression)
    if expression.getAppFn.isConstOf ``CategoryTheory.Cat.Hom.toFunctor then
      mapProjectionArgument ``CategoryTheory.Cat.Hom.toFunctor expression declaredMap
    else declaredMap expression
  | .classifierForget id, [.classifierForget entry] =>
    unless entry.id == id do
      throwError "the routed classifier changed its complete selected row"
    mapProjectionArgument ``CategoryTheory.Cat.Hom.toFunctor expression fun forget =>
      mapProjectionArgument ``LeanCategories.Classifier.forget forget fun classifier => do
        let declaredMap := fun expression => do transform (← declaredApplication entry.declaration expression)
        if classifier.getAppFn.isConstOf ``LeanCategories.PropertyClassifier.toClassifier then
          mapProjectionArgument ``LeanCategories.PropertyClassifier.toClassifier classifier declaredMap
        else if classifier.getAppFn.isConstOf ``LeanCategories.StructureClassifier.toClassifier then
          mapProjectionArgument ``LeanCategories.StructureClassifier.toClassifier classifier declaredMap
        else declaredMap classifier
  | .constructMap constructor inner, .constructorInterface entry .functorialAction :: remaining =>
    unless entry.id == constructor do
      throwError "the routed constructor changed its complete selected row"
    let some action := entry.functorialAction
      | throwError "the routed constructor lost its declared action"
    discard <| declaredApplication action expression
    mapProjectionArgument action expression fun selected =>
      mapRoutedAction inner remaining selected transform
  | _, _ => throwError "the routed action lost its complete original selected rows"



opaque routedActionWithParameters (family : SourceActionFamily) (expression : Expr)
    (parameters : Array Expr) : MetaM Expr := do
  let originals ← routedActionParameters family expression
  let result ← mapRoutedAction family.edge family.references.toList expression fun declared => do
    unless originals.size == parameters.size do
      throwError "the routed action changed its complete explicit parameter arity"
    let mut arguments := declared.getAppArgs
    for (index, _original) in originals, parameter in parameters do
      arguments := arguments.set! index parameter
    return mkAppN declared.getAppFn arguments
  checkWithKernel result
  return result




def RoutedMethodFamily.actionParameterInputs (family : RoutedMethodFamily) :
    MetaM (Array (Array (Option Nat))) := withLCtx {} #[] do
  forallTelescopeReducing (← inferType family.categoryFamily) fun parameters _ => do
    let bindings := parameters.mapIdx fun index expression =>
      ({
        id := {
          session := "method-action-parameter"
          serial := index }
        role := BindingRole.parameter
        expression := expression } : LocalBinding)
    let context ← ContextTelescope.capture bindings
    let actions ← family.specializeActions (family.universeParams.map Level.param) parameters
    let edges := family.route.refs.push (.functor family.functor.id)
    unless edges.size == actions.size && actions.size == family.actionFamilies.size do
      throwError "the routed method lost a complete selected action family"
    let mut result := #[]
    for edge in edges, action in actions, actionFamily in family.actionFamilies do
      unless actionFamily.edge == edge do
        throwError "the routed method changed an original action position"
      let mut selected := #[]
      for (_, source) in ← routedActionParameters actionFamily action do
        let route ← (← context.close source).inputProjectionAt #[] (bindings.map (·.id))
        let index := do
          let route ← route
          unless route.path.isEmpty do none
          let .context id := route.target | none
          bindings.findIdx? (·.id == id)
        selected := selected.push index
      result := result.push selected
    return result


def routedActionDescriptor (edge : EdgeRef) (parameters : Array Json) : Json :=
  match edge with
  | .functor id => Json.mkObj [("ctor", toJson id.raw), ("args", .arr parameters)]
  | .classifierForget id => Json.mkObj [("ctor", toJson "classifierForget"),
      ("args", .arr #[toJson id.raw, .arr parameters])]
  | .constructMap constructor inner => Json.mkObj [("ctor", toJson "constructorMap"),
      ("args", .arr #[toJson constructor.raw, routedActionDescriptor inner parameters])]


def routedActionParameterPath (edge : EdgeRef) (index : Nat) : Array CasCatalogue.Backend.InputPathStep :=
  match edge with
  | .functor _ => #[.field "args", .index index]
  | .classifierForget _ => #[.field "args", .index 1, .index index]
  | .constructMap _ inner => #[.field "args", .index 1] ++ routedActionParameterPath inner index



def RoutedMethodFamily.resultAt [Monad m] [MonadLiftT MetaM m]
    (family : RoutedMethodFamily) (levels : List Level) (parameters : Array Expr)
    (receiver forward : Expr) (select : SourceSelection Expr → Option Expr → m Expr) :
    m (Expr × Expr) := do
  liftM (m := MetaM) do
    unless levels.length == family.universeParams.length &&
        parameters.size == family.parameterCount do
      throwError "the returning method changed its complete native parameter telescope"
  let specialize := fun expression =>
    (mkAppN (expression.instantiateLevelParams family.universeParams levels) parameters).headBeta
  match family.returns with
  | none =>
    let (_, target) ← liftM (m := MetaM) <|
      functorCategoryBundles (specialize family.functorFamily)
    return (forward, target)
  | some returned =>
    liftM (m := MetaM) do
      unless returned.actionFamilies.size == returned.rows.size do
        throwError "the returning method lost a complete original action family"
    let result ← applyMethodReturns returned.rows (returned.evidences.map specialize)
      (returned.actions.map specialize) receiver forward select fun index edge action original => do
        let selected ← liftM (m := MetaM) do
          let some actionFamily := returned.actionFamilies[index]?
            | throwError "the returning route lost its original selected action position"
          unless actionFamily.edge == edge do
            throwError "the returning route changed its complete selected action"
          let declared ← routedActionApplication actionFamily action
          let .const _ levels := declared.getAppFn
            | throwError "the returning route lost its original declared action"
          actionFamily.selected levels declared.getAppArgs original
        select selected none
    liftM (m := MetaM) do
      let result ← retainMethodReturnAgreement (returned.agreement.map specialize) result
      let bundle := specialize returned.categoryFamily
      unless ← isDefEq (← inferType result)
          (← mkAppM ``CategoryTheory.Bundled.α #[bundle]) do
        throwError "the returning method changed its complete actual result category"
      return (result, bundle)


def RoutedMethodFamily.applyAt [Monad m] [MonadLiftT MetaM m]
    (family : RoutedMethodFamily) (levels : List Level)
    (parameters : Array Expr) (receiver : Expr)
    (select : SourceSelection Expr → Option Expr → m Expr)
    (inputs : Array (Array Expr) := #[]) : m (Expr × Expr) := do
  let selected ← liftM (m := MetaM) <| family.selected levels parameters receiver
    (if inputs.isEmpty then none else some inputs)
  let forward ← select selected none
  family.resultAt levels parameters receiver forward select

end CasCompiler
