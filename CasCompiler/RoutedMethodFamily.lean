module

public import CasCompiler.SourceCarrier
public import CasCompiler.Layout
public import CasCompiler.InputCoverage
public import CasCompiler.FamilyConversion
public import CasContract.Port

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- A whole inherited method before its receiver is transported. The native actions and final
functor are closed over the same complete category telescope as the callable result family.
Source: SourceMethod's whole-family comparison and tasks.md T061/T026 boundary rule. -/
structure RoutedMethodFamily where
  private mk ::
  entry : MethodEntry
  route : Route
  functor : FunctorEntry
  categoryFamily : Expr
  functorFamily : Expr
  family : Expr
  actions : Array Expr
  universeParams : List Name
  parameterCount : Nat

/-- Generalize and canonically order the universes of one complete native source family.
The input expressions remain closed together; no actual receiver or runtime data participates. -/
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

/-- Check a selected first-hit route and retain all its original native declaration applications.
The formal receiver remains abstract while the result family is prepared. No registration,
runtime value or equality of specialized receivers chooses this source family. -/
opaque RoutedMethodFamily.forRoute (route : Route) (method : MethodEntry) :
    MetaM RoutedMethodFamily := withLCtx {} #[] do
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
  unless routes.any (fun selected => selected.refs == route.refs &&
      selected.target.syntacticEq route.target) do
    throwError "the selected method route is not a complete first-hit source route"
  -- A validated identity route has no return leg. Its declared result already belongs
  -- to the source; nonidentity routes still require their actual selected lifting data.
  if method.returnsToSource && !route.refs.isEmpty then
    throwUnsupportedSource "source method lifting requires its actual selected return data"
  let some entry := state.functor? method.functor
    | throwError "the source method has no registered functor"
  discard <| checkedDeclaration entry.declaration
  -- The accepted method declaration fixes its own universe family. The independently named
  -- owner may have more universe parameters (for example the two ModuleCat levels), whose
  -- relations are determined only by the complete unapplied native functor boundary below.
  let categoryFamily ← nativeCategoryFamily state route.source fun _ => mkFreshLevelMVar
  let (functorFamily, family, actions, count) ←
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
    -- Unify the complete unapplied source with whole declaration parameters first. Expanding
    -- an already determined structure parameter would replace its original formal slot by
    -- an eta constructor, whose later evaluation creates another computational occurrence.
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
    return (← close complete, ← close callable, ← actions.mapM close, parameters.size)
  let (expressions, universes) ← closeRoutedUniverses
    (#[categoryFamily, functorFamily, family] ++ actions)
  return ⟨method, route, entry, expressions[0]!, expressions[1]!,
    expressions[2]!, expressions.drop 3, universes, count⟩

/-- Recover only an independently registered first-hit route from the retained source syntax. -/
def RoutedMethodFamily.forSelection (source : CategoryExpr) (method : String)
    (refs : Array EdgeRef) : MetaM RoutedMethodFamily := do
  let some entry := (← semanticState).methods.find? (·.id.raw == method)
    | throwError "the selected routed method is absent from the source registry"
  let query ← SourceRoutes.forMethod source entry.name
  let some routes ← query.finiteRoutes
    | throwUnsupportedSource "method inheritance requires its supplied uniform comparison"
  let #[route] := routes.filter (fun route => route.refs == refs &&
      route.target.syntacticEq entry.owner)
    | throwError "the selected routed method lost its exact first-hit route"
  RoutedMethodFamily.forRoute route entry

/-- All independently read first-hit method families at the nominal source category. Provider
availability and a particular receiver play no part in this source inventory. -/
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
        families := families.push (← RoutedMethodFamily.forRoute route entry)
  return families

/-- A complete family is usable only with the same source agreement required by ordinary
method reading. Evidence consists solely of actual supplied proof terms. -/
def RoutedMethodFamily.agreements (family : RoutedMethodFamily) (evidence : Array Expr) :
    MetaM (Array Expr) := do
  let families ← RoutedMethodFamily.atSource family.route.source family.entry.name
  let mut proofs := #[]
  for other in families do
    if other.entry.id == family.entry.id && other.route.refs == family.route.refs then continue
    unless family.functor.target.syntacticEq other.functor.target do
      throwSemanticAmbiguity "method families have different complete result categories"
    let some proof ← sourceFamilyConversion family.functorFamily other.functorFamily evidence
      | throwSemanticAmbiguity "inherited methods require their supplied whole-family agreement"
    proofs := proofs.push proof
  return proofs

def RoutedMethodFamily.instantiate (family : RoutedMethodFamily) : MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)

/-- Only source syntax is metadata. Native abstraction and substitution retain every parameter
inside the original unapplied family application; no encoded local-expression cache is used. -/
def RoutedMethodFamily.mark (family : RoutedMethodFamily) (applied : Expr) : Expr :=
  .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``RoutedMethodFamily
    |>.setString `CasCompiler.source.id family.entry.id.raw
    |>.setString `CasCompiler.source.methodSource (toJson family.route.source).compress
    |>.setString `CasCompiler.source.methodRoute (toJson family.route.refs).compress) applied

/-- Retain complete actual action inputs of a deferred call as typed native source data.
Function.const leaves the mathematical method application unchanged; metadata contains only
the complete array arities. Lowering admits these data into the ordinary family's scope. -/
def RoutedMethodFamily.markInputs (family : RoutedMethodFamily) (applied : Expr)
    (inputs : Array (Array Expr)) : MetaM Expr := do
  let mut body := applied
  for input in inputs.flatten.reverse do
    body ← mkAppM ``Function.const #[← inferType input, body, input]
  let .mdata data _ := family.mark applied
    | throwError "the routed method lost its source marker"
  return .mdata (data.setString `CasCompiler.source.methodInputs
    (toJson (inputs.map (·.size))).compress) body

/-- Read precisely the typed source wrappers emitted above, before any head reduction. -/
def routedMethodInputs (data : MData) (source : Expr) :
    MetaM (Expr × Option (Array (Array Expr))) := do
  let encoded := data.getString `CasCompiler.source.methodInputs
  if encoded.isEmpty then return (source, none)
  let counts ← IO.ofExcept <| ((Json.parse encoded).bind
    (fromJson? (α := Array Nat))).mapError IO.userError
  let mut body := source
  let mut inputs := #[]
  for count in counts do
    let mut parameters := #[]
    for _ in [:count] do
      unless body.isAppOfArity ``Function.const 4 do
        throwError "the method call lost a typed actual action input"
      let some input := body.getAppArgs[3]?
        | throwError "the method call lost its original typed input"
      let some next := body.getAppArgs[2]?
        | throwError "the method call lost its original native application"
      parameters := parameters.push input
      body := next
    inputs := inputs.push parameters
  return (body, some inputs)

/-- Decode the exact selected source syntax, then rebuild its checked native family. -/
def RoutedMethodFamily.fromMark (data : MData) : MetaM RoutedMethodFamily := do
  let source ← IO.ofExcept <| ((Json.parse (data.getString `CasCompiler.source.methodSource)).bind
    (fromJson? (α := CategoryExpr))).mapError IO.userError
  let route ← IO.ofExcept <| ((Json.parse (data.getString `CasCompiler.source.methodRoute)).bind
    (fromJson? (α := Array EdgeRef))).mapError IO.userError
  RoutedMethodFamily.forSelection source (data.getString `CasCompiler.source.id) route

/-- Specialize the same complete actions in their original source order, including the final
registered method functor. Only native beta substitution is performed. -/
def RoutedMethodFamily.specializeActions (family : RoutedMethodFamily) (levels : List Level)
    (arguments : Array Expr) : MetaM (Array Expr) := do
  unless levels.length == family.universeParams.length &&
      arguments.size == family.parameterCount do
    throwError "the routed method changed its complete category parameter telescope"
  return family.actions.map fun action =>
    (mkAppN (action.instantiateLevelParams family.universeParams levels) arguments).headBeta

/-- A native parameter view certified against the complete original declaration telescope.
The selected positions retain their original ordinals. Every computational result field and
its source/type dependencies are covered before the executable telescope is restricted. -/
structure MethodCategoryAssembly where
  private mk ::
  arity : Nat
  positions : Array Nat
  family : Expr

/-- The source of one category parameter in a receiver's independently authored family. A fixed
term contains no receiver parameter; an assembly is only a complete native input view. -/
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

/-- Locate category parameters in the receiver declaration's complete rigid source telescope.
Only this abstract type family determines the positions. A source projection route identifies
an original slot; complete native record views retain their original input positions. For the
reader's Arrow wrapper, inspect the original hom declaration under that same native wrapper.
No actual receiver expression participates in this correspondence. -/
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

/-- Compose an original selected result projection with its sole actual declared input.
Both declarations stay abstract over the input producer's complete rigid telescope. Only
native typing determines the outer declaration's parameters; no actual input or result is
substituted, and no missing argument is synthesized. The returned routes name the input
producer's original positions, using the same coverage rules as direct receivers. -/
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

/-- Method callers use the same original category-parameter correspondence as properties. -/
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
  unless expression.getAppFn.isConstOf name do
    throwError "the routed action lost its original declaration {name}"
  let arity ← forallTelescopeReducing (← inferType expression.getAppFn)
    fun parameters _ => pure parameters.size
  unless expression.getAppNumArgs == arity do
    throwError "the routed action lost its complete original declaration telescope"
  return expression

/-- The exact declaration application inside the wrappers installed by registeredFunctorInstance,
classifierForgetInstance and applyConstructorInterface. This follows the selected native spine;
it does not search for a declaration or a value elsewhere in the source expression. -/
private partial def routedActionApplicationCore (edge : EdgeRef) (expression : Expr) : MetaM Expr := do
  let state ← semanticState
  match edge with
  | .functor id =>
    let some entry := state.functor? id | throwError "the routed functor is not registered"
    let expression ← if expression.getAppFn.isConstOf ``CategoryTheory.Cat.Hom.toFunctor then
        projectionArgument ``CategoryTheory.Cat.Hom.toFunctor expression
      else pure expression
    declaredApplication entry.declaration expression
  | .classifierForget id =>
    let some entry := state.classifier? id | throwError "the routed classifier is not registered"
    let expression ← projectionArgument ``CategoryTheory.Cat.Hom.toFunctor expression
    let expression ← projectionArgument ``LeanCategories.Classifier.forget expression
    let expression ← if expression.getAppFn.isConstOf ``LeanCategories.PropertyClassifier.toClassifier then
        projectionArgument ``LeanCategories.PropertyClassifier.toClassifier expression
      else if expression.getAppFn.isConstOf ``LeanCategories.StructureClassifier.toClassifier then
        projectionArgument ``LeanCategories.StructureClassifier.toClassifier expression
      else pure expression
    declaredApplication entry.declaration expression
  | .constructMap constructor inner =>
    let some action := (state.constructor? constructor).bind (·.functorialAction)
      | throwError "the routed constructor lost its declared action"
    let expression ← declaredApplication action expression
    routedActionApplicationCore inner (← projectionArgument action expression)

/-- Read the checked native action spine while keeping its implementation helpers private. -/
opaque routedActionApplication (edge : EdgeRef) (expression : Expr) : MetaM Expr :=
  routedActionApplicationCore edge expression

/-- Original explicit computational positions of one complete action declaration. Implicit and
proof positions remain in the checked native application; every nonproof explicit occurrence
is returned in order, even when two occurrences have equal source terms. -/
def routedActionParameters (edge : EdgeRef) (expression : Expr) :
    MetaM (Array (Nat × Expr)) := do
  let declared ← routedActionApplication edge expression
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

/-- Replace only the original declared application along the independently accepted wrapper
spine. This is position-preserving source substitution, never an expression/value search. -/
private partial def mapRoutedAction (edge : EdgeRef) (expression : Expr)
    (transform : Expr → MetaM Expr) : MetaM Expr := do
  let state ← semanticState
  match edge with
  | .functor id =>
    let some entry := state.functor? id | throwError "the routed functor is absent"
    let declaredMap := fun expression => do transform (← declaredApplication entry.declaration expression)
    if expression.getAppFn.isConstOf ``CategoryTheory.Cat.Hom.toFunctor then
      mapProjectionArgument ``CategoryTheory.Cat.Hom.toFunctor expression declaredMap
    else declaredMap expression
  | .classifierForget id =>
    let some entry := state.classifier? id | throwError "the routed classifier is absent"
    mapProjectionArgument ``CategoryTheory.Cat.Hom.toFunctor expression fun forget =>
      mapProjectionArgument ``LeanCategories.Classifier.forget forget fun classifier => do
        let declaredMap := fun expression => do transform (← declaredApplication entry.declaration expression)
        if classifier.getAppFn.isConstOf ``LeanCategories.PropertyClassifier.toClassifier then
          mapProjectionArgument ``LeanCategories.PropertyClassifier.toClassifier classifier declaredMap
        else if classifier.getAppFn.isConstOf ``LeanCategories.StructureClassifier.toClassifier then
          mapProjectionArgument ``LeanCategories.StructureClassifier.toClassifier classifier declaredMap
        else declaredMap classifier
  | .constructMap constructor inner =>
    let some action := (state.constructor? constructor).bind (·.functorialAction)
      | throwError "the routed constructor lost its declared action"
    discard <| declaredApplication action expression
    mapProjectionArgument action expression fun selected => mapRoutedAction inner selected transform

/-- Install already checked actual inputs at the complete native explicit parameter positions.
Both prefix evaluation and final descriptor encoding then read these same supplied nodes. -/
opaque routedActionWithParameters (edge : EdgeRef) (expression : Expr) (parameters : Array Expr) :
    MetaM Expr := do
  let result ← mapRoutedAction edge expression fun declared => do
    let originals ← routedActionParameters edge expression
    unless originals.size == parameters.size do
      throwError "the routed action changed its complete explicit parameter arity"
    let mut arguments := declared.getAppArgs
    for (index, _original) in originals, parameter in parameters do
      arguments := arguments.set! index parameter
    return mkAppN declared.getAppFn arguments
  checkWithKernel result
  return result

/-- Which complete category slot supplies an entire explicit action parameter. This is read
from the rigid native family before specialization. It lets a deferred call retain an actual
supplied parameter at that original position; native equality does not recover a value. -/
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
    let mut result := #[]
    for edge in edges, action in actions do
      let mut selected := #[]
      for (_, source) in ← routedActionParameters edge action do
        let route ← (← context.close source).inputProjectionAt #[] (bindings.map (·.id))
        let index := do
          let route ← route
          unless route.path.isEmpty do none
          let .context id := route.target | none
          bindings.findIdx? (·.id == id)
        selected := selected.push index
      result := result.push selected
    return result

/-- Existing public action grammar, with complete parameters supplied at their native positions. -/
def routedActionDescriptor (edge : EdgeRef) (parameters : Array Json) : Json :=
  match edge with
  | .functor id => Json.mkObj [("ctor", toJson id.raw), ("args", .arr parameters)]
  | .classifierForget id => Json.mkObj [("ctor", toJson "classifierForget"),
      ("args", .arr #[toJson id.raw, .arr parameters])]
  | .constructMap constructor inner => Json.mkObj [("ctor", toJson "constructorMap"),
      ("args", .arr #[toJson constructor.raw, routedActionDescriptor inner parameters])]

/-- The wire path of the same positioned declaration parameter inside its action descriptor. -/
def routedActionParameterPath (edge : EdgeRef) (index : Nat) : Array CasCatalogue.Backend.InputPathStep :=
  match edge with
  | .functor _ => #[.field "args", .index index]
  | .classifierForget _ => #[.field "args", .index 1, .index index]
  | .constructMap _ inner => #[.field "args", .index 1] ++ routedActionParameterPath inner index

end CasCompiler
