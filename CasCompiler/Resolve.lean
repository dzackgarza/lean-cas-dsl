module

public import CasCompiler.RouteGrammar
public import CasCompiler.Surface
public import LeanCategories.Catalogue.Registry.Semantic
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Lean.Meta.Simp

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- Compare complete rigid source families with the accepted library's rewrite evidence.
Reuse: Lean.Meta.SimpTheorems.addDeclToUnfold and Mathlib's Simp.Result.ofTrue. Only the supplied
declarations are unfolded explicitly; imported simp theorems supply checked equalities.
The native constants present in the families include their route applications. Lean's
getUsedConstants supplies these definitions without a subject-specific unfolding list.
The returned proof retains both complete families before actual source specialization. -/
def sourceFamilyConversion (left right : Expr) (declarations : Array Name) :
    MetaM (Option Expr) := do
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar then
    throwError "whole source family comparison requires rigid parameters and universes"
  unless ← isDefEq (← inferType left) (← inferType right) do return none
  let proposition ← mkEq left right
  let mut theorems ← getSimpTheorems
  for declaration in declarations ++ left.getUsedConstants ++ right.getUsedConstants do
    if let some (.defnInfo _) := (← getEnv).find? declaration then
      theorems ← theorems.addDeclToUnfold declaration
  -- Route applications also occur inside the selected algebraic dictionaries.
  -- Normalize those native arguments while retaining the original whole equality.
  let context ← Simp.mkContext { instances := true } (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← simp proposition context
  let some proof ← result.ofTrue | return none
  let proof ← mkExpectedTypeHint proof proposition
  checkWithKernel proof
  return some proof

private inductive SourceSymbol
  | atom (expression : CategoryExpr)
  | constructor (id : ConstructorId)

private def SourceSymbol.same : SourceSymbol → SourceSymbol → Bool
  | .atom left, .atom right => left.syntacticEq right
  | .constructor left, .constructor right => left == right
  | _, _ => false

private def symbol (value : SourceSymbol) : StateM (Array SourceSymbol) Nat := do
  let symbols ← get
  if let some index := symbols.findIdx? (·.same value) then return index
  set (symbols.push value)
  return symbols.size

/-- Exact source decomposition follows the same active unary-context test as edgesFrom.
Residual atoms retain their entire parameter syntax and selected symbolic structure. -/
private partial def encode (constructors : Array ConstructorId) (category : CategoryExpr) :
    StateM (Array SourceSymbol) RouteGrammar.Word := do
  match category with
  | .construct id args =>
    match args with
    | #[.category inner] =>
      if constructors.contains id then
        let leading ← encode constructors inner
        return leading.push (← symbol (.constructor id))
      else return #[← symbol (.atom category)]
    | _ => return #[← symbol (.atom category)]
  | _ => return #[← symbol (.atom category)]

inductive RouteQuery
  | owner (category : CategoryExpr)
  | operation (name : String)

inductive RouteTarget
  | owner (category : CategoryExpr)
  | operation (category : NamedCategoryEntry) (binding : OperationEntry)

def RouteTarget.category : RouteTarget → CategoryExpr
  | .owner category => category
  | .operation category _ => category.expression

/-- Symbolic route family over the exact frozen registry inventory.
Native dependent operation formation and comparison evidence are separate consumers. -/
structure SourceRoutes where
  private mk ::
  private state : SemanticState
  source : CategoryExpr
  query : RouteQuery
  targets : Array RouteTarget
  private symbols : Array SourceSymbol
  edges : Array StructuralEdge
  language : RouteGrammar.RouteLanguage

private def sourceRoutes (state : SemanticState) (source : CategoryExpr)
    (query : RouteQuery) : CoreM SourceRoutes := do
  Core.checkSystem "source route construction"
  let targets := match query with
    | .owner category => #[RouteTarget.owner category]
    | .operation name => state.categories.flatMap fun category =>
      (state.operationBindings category.expression name).map (RouteTarget.operation category)
  let constructors := (state.constructors.filter (·.functorialAction.isSome)).map (·.id)
  let edges := state.structuralEdges
  let build : StateM (Array SourceSymbol)
      (RouteGrammar.Word × Array RouteGrammar.Word × Array RouteGrammar.PrefixRule) := do
    let initial ← encode constructors source
    let targets ← targets.mapM (fun target => encode constructors target.category)
    let rules ← edges.mapM fun edge => do
      let lhs ← encode constructors edge.source
      let rhs ← encode constructors edge.target
      return ({ lhs, rhs } : RouteGrammar.PrefixRule)
    return (initial, targets, rules)
  let ((initial, encodedTargets, rules), symbols) := build.run #[]
  let .ok language := RouteGrammar.compile rules initial encodedTargets
    | throwError "the source registry produced an invalid ground-prefix route system"
  Core.checkSystem "source route saturation"
  return ⟨state, source, query, targets, symbols, edges, language⟩

/-- Project one independently supplied owner target from the current accepted source inventory.
Reuse: structuralEdges/edgesFrom and the source correspondence in #66 comment 6693871042. -/
opaque SourceRoutes.forOwner (source owner : CategoryExpr) : CoreM SourceRoutes := do
  sourceRoutes (← semanticState) source (.owner owner)

/-- Bind the surface operation name before any arity filtering, exactly as the source does. -/
opaque SourceRoutes.forOperation (source : CategoryExpr) (name : String) : CoreM SourceRoutes := do
  sourceRoutes (← semanticState) source (.operation name)

/-- Reconstruct a selected symbolic derivation and validate it against the frozen source.
Actual edge references and constructor actions remain attached to each source occurrence. -/
opaque SourceRoutes.reconstruct (routes : SourceRoutes) (trace : RouteGrammar.Word) :
    CoreM Route := do
  let .ok occurrences := routes.language.reconstruct trace
    | throwError "the selected trace is not a first-hit source derivation"
  let mut current := routes.source
  let mut refs := #[]
  for occurrence in occurrences do
    Core.checkSystem "source route reconstruction"
    let some base := routes.edges[occurrence.rule]?
      | throwError "the selected trace lost its original structural edge"
    let mut edge := base
    for ordinal in occurrence.outerContext do
      let some (.constructor id) := routes.symbols[ordinal]?
        | throwError "the source constructor suffix contains a residual atom"
      edge := {
        source := .construct id #[.category edge.source]
        target := .construct id #[.category edge.target]
        expression := .constructMap id edge.expression
        ref := .constructMap id edge.ref }
    unless current.syntacticEq edge.source do
      throwError "the reconstructed source route has incompatible complete endpoints"
    refs := refs.push edge.ref
    current := edge.target
  unless routes.targets.any (·.category.syntacticEq current) do
    throwError "the reconstructed source route lost its exact binding target"
  let some steps := routes.state.routeEdges? routes.source current refs
    | throwError "the reconstructed route does not belong to the retained source inventory"
  let route : Route := { source := routes.source, target := current, steps }
  if let .operation name := routes.query then
    unless routes.state.isFirstOperationBindingRoute name route do
      throwError "the reconstructed route does not reach its first actual operation binding"
  Core.checkSystem "source route validation"
  return route

/-- Reconstruct every finite raw candidate family; none denotes an infinite trace language.
Each returned route retains and validates its actual source edges and constructor actions. -/
opaque SourceRoutes.finiteRoutes (routes : SourceRoutes) : CoreM (Option (Array Route)) := do
  Core.checkSystem "finite source route extraction"
  let words := routes.language.grammar.finiteWords
  Core.checkSystem "finite source route saturation"
  let result ← match words with
    | none => pure none
    | some words => return some (← words.mapM routes.reconstruct)
  Core.checkSystem "finite source route publication"
  return result

/-- An exact symbolic source category and its retained native bundle. -/
structure SourceCategory where
  private mk ::
  expression : CategoryExpr
  value : SourceTerm

/-- Form the registered category family at actual arguments and explicit rigid universes.
Reuse: whole-declaration intake, native application and the actual category structure. -/
opaque SourceSession.namedCategory (session : SourceSession) (reference : Syntax) (name : String)
    (universes : List Level) (arguments : Array SourceTerm) : TermElabM SourceCategory := do
  let entry ← selectCategory (← semanticState) name
  let constant ← session.constant reference entry.declaration universes
  let value ← session.elaborate reference fun context => do
    let arguments ← arguments.mapM fun argument => do
      return Arg.expr (← argument.source.inContext context)
    let value ← elabAppArgs (← constant.source.inContext context) #[] arguments none false false
    discard <| categoryIdentity value
    return value
  return ⟨entry.expression, value⟩

/-- Form an actual registered unary category constructor at the retained category bundle.
Reuse: the same semantics interface checked by source validateConstructor. -/
opaque SourceSession.unaryCategory (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (argument : SourceCategory) : TermElabM SourceCategory := do
  let some entry := (← semanticState).constructor? id
    | throwError "the source category constructor is absent"
  unless entry.signature == #[.category] do
    throwError "the selected source constructor does not take one category argument"
  discard <| checkedDeclaration entry.semantics
  let value ← session.elaborate reference fun context => do
    let category ← argument.value.source.inContext context
    let value ← applyConstructorInterface entry.semantics #[category] #[category]
    discard <| categoryIdentity value
    return value
  return ⟨.construct id #[.category argument.expression], value⟩

/-- Retain the exact category already formed by registered object intake. -/
opaque SourceObject.sourceCategory (object : SourceObject) : SourceCategory :=
  ⟨object.categoryEntry.expression, object.category⟩

/-- One explicitly selected source derivation and its actual native functor. -/
structure SourceRoute where
  private mk ::
  route : Route
  source : SourceCategory
  target : SourceCategory
  functor : SourceTerm

/-- Interpret the selected route in the complete native context, preserving both bundle fields.
Reuse: the independent routeFunctor/functorCategoryBundles/applyConstructorInterface APIs.
This operation selects no representative from a family of mathematical readings. -/
opaque SourceRoutes.prepareFunctor (routes : SourceRoutes) (session : SourceSession)
    (reference : Syntax) (trace : RouteGrammar.Word) (source : SourceCategory) :
    TermElabM SourceRoute := do
  unless routes.source.syntacticEq source.expression do
    throwError "the native source category differs from the exact symbolic route source"
  let route ← routes.reconstruct trace
  let #[functor, target] ← session.elaborateMany reference fun context => do
      let category ← source.value.source.inContext context
      let selected ← nativeRouteFunctor routes.state route category
      return #[selected.functor, selected.target]
    | throwError "native route formation returned an invalid number of expressions"
  return ⟨route, source, ⟨route.target, target⟩, functor⟩

/-- Exact source provenance for an explicitly registered functor or checked structural route. -/
inductive SourceFunctorDerivation where
  | registered (entry : FunctorEntry) (parameters : Array SourceTerm)
  | structural (route : SourceRoute)
  | identity (category : SourceCategory)
  | composition (first second : SourceFunctorDerivation)
  | constructed (constructor : ConstructorEntry) (functor : SourceFunctorDerivation)

/-- A whole native functor with both complete category bundles and original source references. -/
structure SourceFunctor where
  private mk ::
  derivation : SourceFunctorDerivation
  source : SourceCategory
  target : SourceCategory
  functor : SourceTerm

/-- Retain the actual functor already formed by checked source-route interpretation. -/
opaque SourceRoute.asFunctor (route : SourceRoute) : SourceFunctor :=
  ⟨.structural route, route.source, route.target, route.functor⟩

/-- Form an explicitly registered functor at its actual native parameters and source bundle.
Reuse: FunctorEntry, native elabAppArgs and the source registeredFunctorInstance interface.
Explicit selection admits nonstructural functors without changing structural inheritance. -/
opaque SourceSession.namedFunctor (session : SourceSession) (reference : Syntax)
    (id : FunctorId) (parameters : Array SourceTerm) (source : SourceCategory) :
    TermElabM SourceFunctor := do
  let #[entry] := (← semanticState).functors.filter (·.id == id)
    | throwError "explicit source functor selection requires one registered functor"
  let #[functor, target] ← session.elaborateMany reference fun context => do
      let arguments ← parameters.mapM fun parameter => do
        return Arg.expr (← parameter.source.inContext context)
      let selected ← viewExpressions (.inl entry)
        (some (source.expression, ← source.value.source.inContext context)) fun constant =>
          elabAppArgs constant #[] arguments none false false
      return #[selected.functor, selected.targetBundle]
    | throwError "registered functor formation returned an invalid expression family"
  return ⟨.registered entry parameters, source, ⟨entry.target, target⟩, functor⟩

/-- Form the identity at the exact retained category structure.
Reuse: native Functor.id with both the actual carrier and category dictionary. -/
opaque SourceSession.identityFunctor (session : SourceSession) (reference : Syntax)
    (category : SourceCategory) : TermElabM SourceFunctor := do
  let functor ← session.elaborate reference fun context => do
    categoryIdentity (← category.value.source.inContext context)
  return ⟨.identity category, category, category, functor⟩

/-- Compose the actual retained native functors at their complete intermediate category.
Reuse: Semantic.mkFunctorComp, including its carrier/dictionary/universe checks. -/
opaque SourceSession.composeFunctors (session : SourceSession) (reference : Syntax)
    (first second : SourceFunctor) : TermElabM SourceFunctor := do
  unless first.target.expression.syntacticEq second.source.expression do
    throwError "source functor composition has different complete symbolic middle categories"
  let functor ← session.elaborate reference fun context => do
    unless ← isDefEq (← first.target.value.source.inContext context)
        (← second.source.value.source.inContext context) do
      throwError "source functor composition has different complete native middle categories"
    mkFunctorComp (← first.functor.source.inContext context)
      (← second.functor.source.inContext context)
  return ⟨.composition first.derivation second.derivation, first.source, second.target, functor⟩

/-- Apply a registered unary constructor's original functor action to the retained source value.
Reuse: ConstructorEntry.functorialAction and the complete applyConstructorInterface contract. -/
opaque SourceSession.constructFunctor (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (functor : SourceFunctor) : TermElabM SourceFunctor := do
  let some constructor := (← semanticState).constructor? id
    | throwError "the source functor constructor is absent"
  unless constructor.signature == #[.category] do
    throwError "the source constructor does not expose a unary category functor interface"
  let some action := constructor.functorialAction
    | throwError "the source constructor has no declared functor action"
  discard <| checkedDeclaration constructor.semantics
  discard <| checkedDeclaration action
  let source ← session.unaryCategory reference id functor.source
  let target ← session.unaryCategory reference id functor.target
  let value ← session.elaborate reference fun context => do
    let categories := #[← functor.source.value.source.inContext context,
      ← functor.target.value.source.inContext context]
    let value ← applyConstructorInterface action categories
      #[← functor.functor.source.inContext context]
    let (domain, codomain) ← functorCategoryBundles value
    unless ← isDefEq domain (← source.value.source.inContext context) <&&>
        isDefEq codomain (← target.value.source.inContext context) do
      throwError "the constructor functor has different complete native category endpoints"
    return value
  return ⟨.constructed constructor functor.derivation, source, target, value⟩

/-- An actual functor image retains the original native functor and source object. -/
structure SourceFunctorImage where
  private mk ::
  functor : SourceFunctor
  object : SourceTerm
  value : SourceTerm

/-- Apply the retained functor to the actual checked source object in the complete context.
Reuse: Functor.toPrefunctor/Prefunctor.obj and stable-ID context transport. -/
opaque SourceSession.functorImage (session : SourceSession) (reference : Syntax)
    (functor : SourceFunctor) (object : SourceTerm) : TermElabM SourceFunctorImage := do
  let value ← session.elaborate reference fun context => do
    let native ← functor.functor.source.inContext context
    let object ← object.source.inContext context
    functorObject native object (← functor.target.value.source.inContext context)
  return ⟨functor, object,
    ← value.inCategory functor.target.expression functor.target.value⟩

/-- A whole category declaration, before any of its formal parameters are selected. -/
structure SourceCategoryFamily where
  private mk ::
  expression : CategoryExpr
  family : SourceTerm

/-- Retain the unapplied source declaration at explicit rigid universes. -/
opaque SourceSession.categoryFamily (session : SourceSession) (reference : Syntax) (name : String)
    (universes : List Level) : TermElabM SourceCategoryFamily := do
  let entry ← selectCategory (← semanticState) name
  return ⟨entry.expression, ← session.constant reference entry.declaration universes⟩

/-- Apply unary semantics under the whole native parameter telescope. -/
opaque SourceSession.unaryCategoryFamily (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (argument : SourceCategoryFamily) : TermElabM SourceCategoryFamily := do
  let some entry := (← semanticState).constructor? id
    | throwError "the source category constructor is absent"
  unless entry.signature == #[.category] do
    throwError "the selected source constructor does not take one category argument"
  discard <| checkedDeclaration entry.semantics
  let family ← session.elaborate reference fun context => do
    let function ← argument.family.source.inContext context
    forallTelescopeReducing (← inferType function) fun parameters _ => do
      let category := mkAppN function parameters
      let value ← applyConstructorInterface entry.semantics #[category] #[category]
      discard <| categoryIdentity value
      mkLambdaFVars parameters value
  return ⟨.construct id #[.category argument.expression], family⟩

private partial def withRigidArguments {α : Type} (arguments : Array Expr)
    (infos : Array BinderInfo) (start stop : Nat)
    (action : Array Expr → MetaM α) : MetaM α := do
  let rec visit (index : Nat) (rigid : Array Expr) : MetaM α := do
    if index >= stop then return ← action rigid
    let argument ← instantiateMVars arguments[index]!
    if !argument.isMVar then return ← visit (index + 1) rigid
    let declaration ← argument.mvarId!.getDecl
    withLocalDecl declaration.userName infos[index]! (← instantiateMVars declaration.type)
        fun parameter => do
      argument.mvarId!.assign parameter
      visit (index + 1) (rigid.push parameter)
  visit start #[]

/-- Exact source binding and route, with the entire generic morphism family. -/
structure SourceOperationFamily where
  private mk ::
  private state : SemanticState
  source : SourceCategoryFamily
  route : Route
  binding : OperationEntry
  term : SourceTerm

/-- A complete declaration family and the position of its original source object. -/
structure NativeOwnedFamily where
  value : Expr
  objectIndex : Nat

/-- Route a whole declaration at a rigid source object, retaining independent parameters.
Reuse: nativeOperationFamily's source telescope and withRigidArguments; the actual operation
or numeral signature determines its object position. -/
def nativeOwnedFamily (state : SemanticState) (source : CategoryExpr)
    (categoryFamily : Expr) (route : Route) (declaration : Name)
    (objectPosition : Array BinderInfo → Option Nat) : MetaM NativeOwnedFamily := do
  unless source.syntacticEq route.source do
    throwError "the declaration family has a different complete symbolic source"
  discard <| checkedDeclaration declaration
  forallTelescopeReducing (← inferType categoryFamily) fun parameters _ => do
    let category := mkAppN categoryFamily parameters
    let selected ← nativeRouteFunctor state route category
    let functor := selected.functor
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
    withLocalDeclD `sourceObject carrier fun object => do
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let image ← mkAppM ``Prefunctor.obj #[prefunctor, object]
      let constant ← mkConstWithFreshMVarLevels declaration
      let (arguments, infos, result) ← forallMetaTelescopeReducing (← inferType constant)
      let some position := objectPosition infos
        | throwError "the whole declaration family has no object parameter"
      unless (← whnfR result).isAppOf ``Quiver.Hom do
        throwError "the declaration family does not retain its whole morphism result"
      unless ← isDefEq (← inferType arguments[position]!) (← inferType image) <&&>
          isDefEq arguments[position]! image do
        throwError "the declaration family has a different complete routed object"
      withRigidArguments arguments infos 0 position fun prefixParameters => do
        withRigidArguments arguments infos (position + 1) arguments.size
            fun suffixParameters => do
          let body ← instantiateMVars (mkAppN constant arguments)
          let value ← mkLambdaFVars
            (parameters ++ prefixParameters ++ #[object] ++ suffixParameters) body
          return ⟨value, parameters.size + prefixParameters.size⟩

/-- Form the whole native operation before selecting its source object or operands.
Reuse: validateOperation's object/numeral boundary and nativeOwnedFamily. -/
def nativeOperationFamily (state : SemanticState) (source : CategoryExpr)
    (categoryFamily : Expr) (route : Route) (binding : OperationEntry) : MetaM Expr := do
  let family ← nativeOwnedFamily state source categoryFamily route binding.declaration fun infos =>
    if infos.size > binding.numerals then some (infos.size - 1 - binding.numerals) else none
  return family.value

private def operationTerm (state : SemanticState) (session : SourceSession) (reference : Syntax)
    (source : SourceCategoryFamily) (route : Route) (binding : OperationEntry) :
    TermElabM SourceTerm :=
  session.elaborate reference fun context => do
    nativeOperationFamily state source.expression
      (← source.family.source.inContext context) route binding

/-- Form every binding at an explicitly selected first-hit target before choosing objects/operands.
Reuse: validateOperation's native object/numeral telescope boundary and native abstraction.
Category parameters and remaining declaration parameters are rigid, never chosen by providers. -/
opaque SourceRoutes.operationFamilies (routes : SourceRoutes) (session : SourceSession)
    (reference : Syntax) (trace : RouteGrammar.Word) (source : SourceCategoryFamily) :
    TermElabM (Array SourceOperationFamily) := do
  let .operation _ := routes.query
    | throwError "whole operation preparation requires an operation-name query"
  unless routes.source.syntacticEq source.expression do
    throwError "the whole category family differs from the exact symbolic route source"
  let route ← routes.reconstruct trace
  let bindings := routes.targets.filterMap fun
    | .operation category binding =>
      if category.expression.syntacticEq route.target then some binding else none
    | _ => none
  if bindings.isEmpty then throwError "the selected source target lost its operation binding"
  bindings.mapM fun binding => do
    let term ← operationTerm routes.state session reference source route binding
    return ⟨routes.state, source, route, binding, term⟩

/-- A declared operation restriction, retaining its first-hit binding and full general family. -/
structure SourceOperationRefinement where
  private mk ::
  original : SourceOperationFamily
  base : OperationEntry
  route : Route
  term : SourceTerm
  proposition : SourceTerm
  proof : SourceTerm

/-- Lift the actual registered restriction equality to the whole rigid operation family.
Reuse: OperationRefinement, validateOperation's full declaration-argument interface and funext.
The original first-hit reading is retained; the general family is reached by its declared route. -/
opaque SourceSession.operationRefinement (session : SourceSession) (reference : Syntax)
    (family : SourceOperationFamily) : TermElabM SourceOperationRefinement := do
  let some refinement := family.binding.refines
    | throwError "the source operation has no registered restriction equality"
  let state := family.state
  let #[base] := state.operations.filter (·.id == refinement.base)
    | throwError "the source restriction requires one registered general operation"
  let #[owner] := state.categories.filter (·.id == family.binding.category)
    | throwError "the source restriction has no unique original owner category"
  let #[baseOwner] := state.categories.filter (·.id == base.category)
    | throwError "the source restriction has no unique general owner category"
  unless family.route.target.syntacticEq owner.expression do
    throwError "the source restriction has a different complete original owner"
  let some steps := state.routeEdges? owner.expression baseOwner.expression refinement.route
    | throwError "the source restriction lost its actual structural route"
  discard <| checkedDeclaration refinement.identification
  let route : Route := {
    source := family.route.source
    target := baseOwner.expression
    steps := family.route.steps ++ steps }
  let term ← operationTerm state session reference family.source route base
  let #[proposition, proof] ← session.elaborateMany reference fun context => do
      let left ← family.term.source.inContext context
      let right ← term.source.inContext context
      unless ← isDefEq (← inferType left) (← inferType right) do
        throwError "the source restriction has a different complete operation family type"
      let proposition ← mkEq left right
      let proof ← lambdaTelescope left fun parameters body => do
        unless body.getAppFn.constName? == some family.binding.declaration do
          throwError "the retained operation family lost its original source declaration"
        let constant ← mkConstWithFreshMVarLevels refinement.identification
        let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
        let originalArguments := body.getAppArgs
        unless arguments.size == originalArguments.size do
          throwError "the source restriction equality has different complete declaration parameters"
        for argument in arguments, original in originalArguments do
          unless ← isDefEq (← inferType argument) (← inferType original) <&&>
              isDefEq argument original do
            throwError "the source restriction equality changes a rigid declaration parameter"
        let mut proof ← instantiateMVars (mkAppN constant arguments)
        let expected ← mkEq body (mkAppN right parameters).headBeta
        unless ← isDefEq (← inferType proof) expected do
          throwError "the source restriction equality has a different complete morphism equation"
        for parameter in parameters.reverse do
          proof ← mkAppM ``funext #[← mkLambdaFVars #[parameter] proof]
        return proof
      unless ← isDefEq (← inferType proof) proposition do
        throwError "the restriction evidence has a different complete operation family equation"
      checkWithKernel (← mkExpectedTypeHint proof proposition)
      return #[proposition, proof]
    | throwError "source operation restriction returned an invalid evidence family"
  return ⟨family, base, route, term, proposition, proof⟩

/-- A checked equality of entire native operation families with both original derivations. -/
structure SourceOperationAgreement where
  private mk ::
  left : SourceOperationFamily
  right : SourceOperationFamily
  proposition : SourceTerm
  proof : SourceTerm

/-- Discharge whole-family agreement by native conversion and checked equality introduction.
Reuse: the source operation-agreement contract, Lean.mkEq/mkEqRefl and Meta.checkWithKernel.
An unsuccessful conversion supplies no evidence about other permitted comparisons. -/
opaque SourceSession.operationConversion (session : SourceSession) (reference : Syntax)
    (left right : SourceOperationFamily) : TermElabM (Option SourceOperationAgreement) := do
  unless left.source.expression.syntacticEq right.source.expression do
    throwError "operation comparison requires the same complete symbolic source"
  let evidence ← session.elaborateMany reference fun context => do
    let leftCategory ← left.source.family.source.inContext context
    let rightCategory ← right.source.family.source.inContext context
    unless ← isDefEq (← inferType leftCategory) (← inferType rightCategory) <&&>
        isDefEq leftCategory rightCategory do
      throwError "operation comparison requires the same complete native category family"
    let left ← left.term.source.inContext context
    let right ← right.term.source.inContext context
    unless ← isDefEq (← inferType left) (← inferType right) <&&> isDefEq left right do
      return #[]
    let proposition ← mkEq left right
    let proof ← mkEqRefl left
    unless ← isDefEq (← inferType proof) proposition do
      throwError "conversion evidence has a different complete family equation"
    checkWithKernel (← mkExpectedTypeHint proof proposition)
    return #[proposition, proof]
  match evidence with
  | #[] => return none
  | #[proposition, proof] => return some ⟨left, right, proposition, proof⟩
  | _ => throwError "operation conversion returned an invalid evidence shape"

/-- All-pairs evidence for the complete finite raw operation family.
The retained original derivations have no selected representative. -/
structure SourceFiniteOperationAgreement where
  private mk ::
  routes : SourceRoutes
  source : SourceCategoryFamily
  families : Array SourceOperationFamily
  agreements : Array (Array SourceOperationAgreement)

/-- Check conversion on every ordered pair of complete finite first-hit operation families.
Reuse: exact finite trace extraction and the source-authorized whole-family conversion rule.
None supplies no semantic judgment: infinite families and unresolved comparisons need evidence. -/
opaque SourceRoutes.finiteOperationConversion (routes : SourceRoutes) (session : SourceSession)
    (reference : Syntax) (source : SourceCategoryFamily) :
    TermElabM (Option SourceFiniteOperationAgreement) := do
  let .operation _ := routes.query
    | throwError "finite operation comparison requires an operation-name query"
  unless routes.source.syntacticEq source.expression do
    throwError "finite operation comparison has a different complete symbolic source"
  Core.checkSystem "finite operation trace extraction"
  let words := routes.language.grammar.finiteWords
  Core.checkSystem "finite operation trace saturation"
  let some words := words | return none
  let mut families : Array SourceOperationFamily := #[]
  for word in words do
    families := families ++ (← routes.operationFamilies session reference word source)
  if families.isEmpty then return none
  let mut agreements : Array (Array SourceOperationAgreement) := #[]
  for left in families do
    let mut row := #[]
    for right in families do
      Core.checkSystem "finite whole operation comparison"
      let some agreement ← session.operationConversion reference left right | return none
      row := row.push agreement
    agreements := agreements.push row
  return some ⟨routes, source, families, agreements⟩

inductive WhiskerSide where
  | left | right
  deriving BEq

/-- Actual source arguments of a registered constructor identity or composition comparison. -/
inductive ConstructorCoherence where
  | identity (category : SourceCategory)
  | composition (first second : SourceFunctor)

/-- Source-owned atoms and licensed composition/inversion in their original order. -/
inductive SourceCellDerivation where
  | registered (entry : CellEntry) (parameters : Array SourceTerm) (inverse : Bool)
  | vertical (first second : SourceCellDerivation)
  | horizontal (first second : SourceCellDerivation)
  | whisker (side : WhiskerSide) (functor : SourceFunctor) (cell : SourceCellDerivation)
  | constructed (constructor : ConstructorEntry) (cell : SourceCellDerivation)
  | coherence (constructor : ConstructorEntry) (input : ConstructorCoherence)
  | inverse (original : SourceCellDerivation)

/-- A whole directed transformation, before selecting any source object for its component. -/
structure SourceCell where
  private mk ::
  derivation : SourceCellDerivation
  source : SourceCategory
  target : SourceCategory
  transformation : SourceTerm
  left : SourceTerm
  right : SourceTerm
  isomorphism : Option SourceTerm

/-- Form the whole directed transformation of a source-owned cell in the complete context.
Reuse: CellEntry, SemanticState.cellEndpoints and Iso.hom/inv.
The source row and full native functor/category structures fix the endpoints and direction. -/
opaque SourceSession.cell (session : SourceSession) (reference : Syntax)
    (id : NaturalTransformationId) (parameters : Array SourceTerm) (source : SourceCategory)
    (inverse : Bool := false) : TermElabM SourceCell := do
  let state ← semanticState
  let #[entry] := state.cells.filter (·.id == id)
    | throwError "a source cell component requires one registered cell"
  unless source.expression.syntacticEq entry.source do
    throwError "the cell has a different complete symbolic source category"
  if inverse && !entry.invertible then
    throwError "the source cell has no registered inverse"
  discard <| checkedDeclaration entry.declaration
  for ref in entry.left ++ entry.right do checkEdgeDeclarations state ref
  let terms ← session.elaborateMany reference
      fun context => do
    let category ← source.value.source.inContext context
    let arguments ← parameters.mapM fun parameter => do
      return Arg.expr (← parameter.source.inContext context)
    let constant ← mkConstWithFreshMVarLevels entry.declaration
    let cell ← elabAppArgs constant #[] arguments none false false
    let transformation ← if entry.invertible then
        mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[cell]
      else pure cell
    let (declaredLeft, declaredRight) ← state.cellEndpoints entry.left entry.right
    let (left, right) := if inverse then (declaredRight, declaredLeft)
      else (declaredLeft, declaredRight)
    let (leftSource, leftTarget) ← functorCategoryBundles left
    let (rightSource, rightTarget) ← functorCategoryBundles right
    unless ← isDefEq leftSource category <&&> isDefEq rightSource category <&&>
        isDefEq leftTarget rightTarget do
      throwError "the source cell routes have different complete native categories"
    let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
    unless ← isDefEq (← inferType transformation) expected do
      throwError "the source cell has different complete native functor endpoints"
    if entry.invertible then
      let isomorphism ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[cell] else pure cell
      let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
      unless ← isDefEq (← inferType isomorphism) expected <&&>
          isDefEq (← mkAppM ``CategoryTheory.Iso.hom #[isomorphism]) transformation do
        throwError "the source isomorphism does not witness its complete directed transformation"
      return #[transformation, left, right, leftTarget, isomorphism]
    return #[transformation, left, right, leftTarget]
  match terms with
  | #[transformation, left, right, target] =>
    return ⟨.registered entry parameters inverse, source, ⟨entry.target, target⟩,
      transformation, left, right, none⟩
  | #[transformation, left, right, target, isomorphism] =>
    return ⟨.registered entry parameters inverse, source, ⟨entry.target, target⟩,
      transformation, left, right, some isomorphism⟩
  | _ => throwError "source cell formation returned an invalid expression family"

/-- Compose whole native transformations at the same complete intermediate functor.
Reuse: Mathlib's CategoryStruct.comp on natural transformations and Iso.trans on isomorphisms.
Original source derivations and all data-bearing components remain attached to the program. -/
opaque SourceSession.composeCells (session : SourceSession) (reference : Syntax)
    (first second : SourceCell) : TermElabM SourceCell := do
  unless first.source.expression.syntacticEq second.source.expression &&
      first.target.expression.syntacticEq second.target.expression do
    throwError "cell composition has different complete symbolic categories"
  let terms ← session.elaborateMany reference fun context => do
    unless ← isDefEq (← first.source.value.source.inContext context)
          (← second.source.value.source.inContext context) <&&>
        isDefEq (← first.target.value.source.inContext context)
          (← second.target.value.source.inContext context) do
      throwError "cell composition has different complete native categories"
    unless ← isDefEq (← first.right.source.inContext context)
        (← second.left.source.inContext context) do
      throwError "cell composition has different complete intermediate functors"
    let left ← first.left.source.inContext context
    let right ← second.right.source.inContext context
    let transformation ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[← first.transformation.source.inContext context,
        ← second.transformation.source.inContext context]
    let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
    unless ← isDefEq (← inferType transformation) expected do
      throwError "cell composition has different complete native endpoints"
    match first.isomorphism, second.isomorphism with
    | some firstIso, some secondIso =>
      let isomorphism ← mkAppM ``CategoryTheory.Iso.trans
        #[← firstIso.source.inContext context, ← secondIso.source.inContext context]
      let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
      unless ← isDefEq (← inferType isomorphism) expected <&&>
          isDefEq (← mkAppM ``CategoryTheory.Iso.hom #[isomorphism]) transformation do
        throwError "the composite isomorphism does not witness its complete directed transformation"
      return #[transformation, isomorphism]
    | _, _ => return #[transformation]
  match terms with
  | #[transformation] =>
    return ⟨.vertical first.derivation second.derivation, first.source, first.target,
      transformation, first.left, second.right, none⟩
  | #[transformation, isomorphism] =>
    return ⟨.vertical first.derivation second.derivation, first.source, first.target,
      transformation, first.left, second.right, some isomorphism⟩
  | _ => throwError "cell composition returned an invalid expression family"

/-- Compose whole cell actions horizontally through the exact complete intermediate category.
Reuse: native Functor.comp, NatTrans.hcomp and NatIso.hcomp, including their checked laws. -/
opaque SourceSession.horizontalCells (session : SourceSession) (reference : Syntax)
    (first second : SourceCell) : TermElabM SourceCell := do
  unless first.target.expression.syntacticEq second.source.expression do
    throwError "horizontal cell composition has different complete symbolic middle categories"
  let terms ← session.elaborateMany reference fun context => do
    unless ← isDefEq (← first.target.value.source.inContext context)
        (← second.source.value.source.inContext context) do
      throwError "horizontal cell composition has different complete native middle categories"
    let left ← mkFunctorComp (← first.left.source.inContext context)
      (← second.left.source.inContext context)
    let right ← mkFunctorComp (← first.right.source.inContext context)
      (← second.right.source.inContext context)
    let transformation ← mkAppM ``CategoryTheory.NatTrans.hcomp
      #[← first.transformation.source.inContext context,
        ← second.transformation.source.inContext context]
    let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
    unless ← isDefEq (← inferType transformation) expected do
      throwError "horizontal cell composition has different complete native endpoints"
    match first.isomorphism, second.isomorphism with
    | some firstIso, some secondIso =>
      let isomorphism ← mkAppM ``CategoryTheory.NatIso.hcomp
        #[← firstIso.source.inContext context, ← secondIso.source.inContext context]
      let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
      unless ← isDefEq (← inferType isomorphism) expected <&&>
          isDefEq (← mkAppM ``CategoryTheory.Iso.hom #[isomorphism]) transformation do
        throwError "horizontal isomorphism does not witness its complete directed transformation"
      return #[transformation, left, right, isomorphism]
    | _, _ => return #[transformation, left, right]
  match terms with
  | #[transformation, left, right] =>
    return ⟨.horizontal first.derivation second.derivation, first.source, second.target,
      transformation, left, right, none⟩
  | #[transformation, left, right, isomorphism] =>
    return ⟨.horizontal first.derivation second.derivation, first.source, second.target,
      transformation, left, right, some isomorphism⟩
  | _ => throwError "horizontal cell composition returned an invalid expression family"

/-- Reverse a retained source-authorized invertible transformation in the full current scope.
Reuse: Iso.symm and Iso.hom on the actual retained native isomorphism. -/
opaque SourceSession.inverseCell (session : SourceSession) (reference : Syntax)
    (cell : SourceCell) : TermElabM SourceCell := do
  let some original := cell.isomorphism | throwError "the source transformation has no inverse"
  let #[transformation, isomorphism, left, right] ← session.elaborateMany reference
      fun context => do
    let isomorphism ← mkAppM ``CategoryTheory.Iso.symm #[← original.source.inContext context]
    let left ← cell.right.source.inContext context
    let right ← cell.left.source.inContext context
    let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
    unless ← isDefEq (← inferType isomorphism) expected do
      throwError "the inverse isomorphism has different complete native endpoints"
    return #[← mkAppM ``CategoryTheory.Iso.hom #[isomorphism], isomorphism, left, right]
    | throwError "source inverse formation returned an invalid expression family"
  return ⟨.inverse cell.derivation, cell.source, cell.target,
    transformation, left, right, some isomorphism⟩

/-- Whisker the actual source transformation on the selected side by a retained whole functor.
Reuse: Functor.whiskerLeft/Right and isoWhiskerLeft/Right at complete native endpoints. -/
opaque SourceSession.whiskerCell (session : SourceSession) (reference : Syntax)
    (side : WhiskerSide) (functor : SourceFunctor) (cell : SourceCell) : TermElabM SourceCell := do
  let (source, target, firstMiddle, secondMiddle) := match side with
    | .left => (functor.source, cell.target, functor.target, cell.source)
    | .right => (cell.source, functor.target, cell.target, functor.source)
  unless firstMiddle.expression.syntacticEq secondMiddle.expression do
    throwError "whiskering has different complete symbolic middle categories"
  let terms ← session.elaborateMany reference fun context => do
    unless ← isDefEq (← firstMiddle.value.source.inContext context)
        (← secondMiddle.value.source.inContext context) do
      throwError "whiskering has different complete native middle categories"
    let functor ← functor.functor.source.inContext context
    let compose (part : Expr) := match side with
      | .left => mkFunctorComp functor part
      | .right => mkFunctorComp part functor
    let arguments (part : Expr) := match side with
      | .left => #[functor, part]
      | .right => #[part, functor]
    let left ← compose (← cell.left.source.inContext context)
    let right ← compose (← cell.right.source.inContext context)
    let operation := match side with
      | .left => ``CategoryTheory.Functor.whiskerLeft
      | .right => ``CategoryTheory.Functor.whiskerRight
    let transformation ← mkAppM operation
      (arguments (← cell.transformation.source.inContext context))
    let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
    unless ← isDefEq (← inferType transformation) expected do
      throwError "whiskering has different complete native functor endpoints"
    match cell.isomorphism with
    | none => return #[transformation, left, right]
    | some original =>
      let operation := match side with
        | .left => ``CategoryTheory.Functor.isoWhiskerLeft
        | .right => ``CategoryTheory.Functor.isoWhiskerRight
      let isomorphism ← mkAppM operation (arguments (← original.source.inContext context))
      let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
      unless ← isDefEq (← inferType isomorphism) expected <&&>
          isDefEq (← mkAppM ``CategoryTheory.Iso.hom #[isomorphism]) transformation do
        throwError "the whiskered isomorphism does not witness its complete directed transformation"
      return #[transformation, left, right, isomorphism]
  match terms with
  | #[transformation, left, right] =>
    return ⟨.whisker side functor cell.derivation, source, target,
      transformation, left, right, none⟩
  | #[transformation, left, right, isomorphism] =>
    return ⟨.whisker side functor cell.derivation, source, target,
      transformation, left, right, some isomorphism⟩
  | _ => throwError "whiskering returned an invalid expression family"

private def checkConstructorComparison (source target left right isomorphism : Expr) :
    MetaM Unit := do
  let (leftSource, leftTarget) ← functorCategoryBundles left
  let (rightSource, rightTarget) ← functorCategoryBundles right
  unless ← isDefEq leftSource source <&&> isDefEq leftTarget target <&&>
      isDefEq rightSource source <&&> isDefEq rightTarget target do
    throwError "the constructor action has different complete native categories"
  let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
  unless ← isDefEq (← inferType isomorphism) expected do
    throwError "the constructor comparison has different complete native functor endpoints"

/-- Apply a registered unary constructor's actual comparison action to a native isomorphism.
Reuse: ConstructorEntry.comparisonAction and the independent applyConstructorInterface contract.
Both the mapped functors and the comparison retain the actual complete category parameters. -/
opaque SourceSession.constructCell (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (cell : SourceCell) : TermElabM SourceCell := do
  let some constructor := (← semanticState).constructor? id
    | throwError "the source comparison constructor is absent"
  unless constructor.signature == #[.category] do
    throwError "the source constructor does not expose a unary category comparison interface"
  let some action := constructor.functorialAction
    | throwError "the source constructor has no declared functor action"
  let some comparison := constructor.comparisonAction
    | throwError "the source constructor has no declared comparison action"
  let some original := cell.isomorphism
    | throwError "the source constructor comparison interface requires a native isomorphism"
  discard <| checkedDeclaration constructor.semantics
  discard <| checkedDeclaration action
  discard <| checkedDeclaration comparison
  let source ← session.unaryCategory reference id cell.source
  let target ← session.unaryCategory reference id cell.target
  let #[transformation, left, right, isomorphism] ← session.elaborateMany reference
      fun context => do
    let categories := #[← cell.source.value.source.inContext context,
      ← cell.target.value.source.inContext context]
    let left ← applyConstructorInterface action categories #[← cell.left.source.inContext context]
    let right ← applyConstructorInterface action categories #[← cell.right.source.inContext context]
    let isomorphism ← applyConstructorInterface comparison categories
      #[← original.source.inContext context]
    checkConstructorComparison (← source.value.source.inContext context)
      (← target.value.source.inContext context) left right isomorphism
    return #[← mkAppM ``CategoryTheory.Iso.hom #[isomorphism], left, right, isomorphism]
    | throwError "constructor comparison returned an invalid expression family"
  return ⟨.constructed constructor cell.derivation, source, target,
    transformation, left, right, some isomorphism⟩

/-- Retain the registered constructor's actual identity/composition coherence isomorphism.
Reuse: ConstructorEntry.identityComparison/compositionComparison and validateConstructor's
complete category/explicit-input interface, with the native source functors retained intact. -/
opaque SourceSession.constructorCoherence (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (input : ConstructorCoherence) : TermElabM SourceCell := do
  let some constructor := (← semanticState).constructor? id
    | throwError "the source comparison constructor is absent"
  unless constructor.signature == #[.category] do
    throwError "the source constructor does not expose a unary category comparison interface"
  let some action := constructor.functorialAction
    | throwError "the source constructor has no declared functor action"
  let law ← match input with
    | .identity _ => match constructor.identityComparison with
      | some law => pure law
      | none => throwError "the source constructor has no declared identity comparison"
    | .composition _ _ => match constructor.compositionComparison with
      | some law => pure law
      | none => throwError "the source constructor has no declared composition comparison"
  let (domain, codomain) ← match input with
    | .identity category => pure (category, category)
    | .composition first second => do
      unless first.target.expression.syntacticEq second.source.expression do
        throwError "constructor composition has different complete symbolic middle categories"
      pure (first.source, second.target)
  discard <| checkedDeclaration constructor.semantics
  discard <| checkedDeclaration action
  discard <| checkedDeclaration law
  let source ← session.unaryCategory reference id domain
  let target ← session.unaryCategory reference id codomain
  let #[transformation, left, right, isomorphism] ← session.elaborateMany reference
      fun context => do
    let (left, right, isomorphism) ← match input with
      | .identity category => do
        let category ← category.value.source.inContext context
        let left ← applyConstructorInterface action #[category, category]
          #[← categoryIdentity category]
        let right ← categoryIdentity (← source.value.source.inContext context)
        let isomorphism ← applyConstructorInterface law #[category] #[category]
        pure (left, right, isomorphism)
      | .composition first second => do
        let C ← first.source.value.source.inContext context
        let D ← first.target.value.source.inContext context
        let E ← second.target.value.source.inContext context
        unless ← isDefEq D (← second.source.value.source.inContext context) do
          throwError "constructor composition has different complete native middle categories"
        let F ← first.functor.source.inContext context
        let G ← second.functor.source.inContext context
        let left ← applyConstructorInterface action #[C, E] #[← mkFunctorComp F G]
        let right ← mkFunctorComp (← applyConstructorInterface action #[C, D] #[F])
          (← applyConstructorInterface action #[D, E] #[G])
        let isomorphism ← applyConstructorInterface law #[C, D, E] #[F, G]
        pure (left, right, isomorphism)
    checkConstructorComparison (← source.value.source.inContext context)
      (← target.value.source.inContext context) left right isomorphism
    return #[← mkAppM ``CategoryTheory.Iso.hom #[isomorphism], left, right, isomorphism]
    | throwError "constructor coherence returned an invalid expression family"
  return ⟨.coherence constructor input, source, target,
    transformation, left, right, some isomorphism⟩

/-- A checked component retains the entire original directed source cell. -/
structure SourceCellComponent where
  private mk ::
  cell : SourceCell
  object : SourceTerm
  value : SourceTerm

/-- Apply the retained whole transformation at the exact checked native source object.
Reuse: NatTrans.app and stable-ID context transport; no declaration is reconstructed. -/
opaque SourceSession.cellComponent (session : SourceSession) (reference : Syntax)
    (cell : SourceCell) (object : SourceTerm) : TermElabM SourceCellComponent := do
  let value ← session.elaborate reference fun context => do
    let category ← cell.source.value.source.inContext context
    let object ← object.source.inContext context
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
    unless ← isDefEq (← inferType object) carrier do
      throwError "the source cell object has a different complete native category"
    let transformation ← cell.transformation.source.inContext context
    mkAppM ``CategoryTheory.NatTrans.app #[transformation, object]
  return ⟨cell, object, value⟩

end CasCompiler
