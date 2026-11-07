module

public import CasCompiler.RouteGrammar
public import CasCompiler.Surface
public import LeanCategories.Catalogue.Registry.Semantic

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

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

private def categoryIdentity (category : Expr) : MetaM Expr := do
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
  let categoryStructure ← mkAppM ``CategoryTheory.Bundled.str #[category]
  mkAppOptM ``CategoryTheory.Functor.id #[some carrier, some categoryStructure]

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

private partial def checkEdgeDeclarations (state : SemanticState) : EdgeRef → MetaM Unit
  | .functor id => do
    let some entry := state.functor? id | throwError "the source functor declaration is absent"
    discard <| checkedDeclaration entry.declaration
  | .classifierForget id => do
    let some entry := state.classifier? id
      | throwError "the source classifier declaration is absent"
    discard <| checkedDeclaration entry.declaration
  | .constructMap id inner => do
    let some entry := state.constructor? id
      | throwError "the source constructor declaration is absent"
    let some action := entry.functorialAction
      | throwError "the source constructor has no declared functorial action"
    discard <| checkedDeclaration entry.semantics
    discard <| checkedDeclaration action
    checkEdgeDeclarations state inner

/-- One explicitly selected source derivation and its actual native functor. -/
structure SourceRoute where
  private mk ::
  route : Route
  source : SourceCategory
  target : SourceCategory
  functor : SourceTerm

private def nativeRouteFunctor (state : SemanticState) (route : Route) (category : Expr) :
    MetaM (Expr × Expr) := do
  let functor ← if route.steps.isEmpty then categoryIdentity category
    else state.routeFunctor route.refs
  let (domain, target) ← functorCategoryBundles functor
  unless ← isDefEq domain category do
    throwError "the selected functor has a different complete source category"
  return (functor, target)

/-- Interpret the selected route in the complete native context, preserving both bundle fields.
Reuse: the independent routeFunctor/functorCategoryBundles/applyConstructorInterface APIs.
This operation selects no representative from a family of mathematical readings. -/
opaque SourceRoutes.prepareFunctor (routes : SourceRoutes) (session : SourceSession)
    (reference : Syntax) (trace : RouteGrammar.Word) (source : SourceCategory) :
    TermElabM SourceRoute := do
  unless routes.source.syntacticEq source.expression do
    throwError "the native source category differs from the exact symbolic route source"
  let route ← routes.reconstruct trace
  for ref in route.refs do checkEdgeDeclarations routes.state ref
  let #[functor, target] ← session.elaborateMany reference fun context => do
      let category ← source.value.source.inContext context
      let (functor, target) ← nativeRouteFunctor routes.state route category
      return #[functor, target]
    | throwError "native route formation returned an invalid number of expressions"
  return ⟨route, source, ⟨route.target, target⟩, functor⟩

/-- Apply the retained native functor to the actual checked source object.
Reuse: Functor.toPrefunctor/Prefunctor.obj and stable-ID context transport. -/
opaque SourceSession.routeImage (session : SourceSession) (reference : Syntax)
    (route : SourceRoute) (object : SourceTerm) : TermElabM SourceTerm :=
  session.elaborate reference fun context => do
    let functor ← route.functor.source.inContext context
    let object ← object.source.inContext context
    let functor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
    let image ← mkAppM ``Prefunctor.obj #[functor, object]
    let target ← route.target.value.source.inContext context
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[target]
    unless ← isDefEq (← inferType image) carrier do
      throwError "the source image does not belong to its complete target category"
    return image

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

private partial def withRigidArguments (arguments : Array Expr) (infos : Array BinderInfo)
    (start stop : Nat) (action : Array Expr → MetaM Expr) : MetaM Expr := do
  let rec visit (index : Nat) (rigid : Array Expr) : MetaM Expr := do
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
  source : SourceCategoryFamily
  route : Route
  binding : OperationEntry
  term : SourceTerm

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
  for ref in route.refs do checkEdgeDeclarations routes.state ref
  let bindings := routes.targets.filterMap fun
    | .operation category binding =>
      if category.expression.syntacticEq route.target then some binding else none
    | _ => none
  if bindings.isEmpty then throwError "the selected source target lost its operation binding"
  bindings.mapM fun binding => do
    discard <| checkedDeclaration binding.declaration
    let term ← session.elaborate reference fun context => do
      let categoryFamily ← source.family.source.inContext context
      forallTelescopeReducing (← inferType categoryFamily) fun parameters _ => do
        let category := mkAppN categoryFamily parameters
        let (functor, _) ← nativeRouteFunctor routes.state route category
        let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
        withLocalDeclD `sourceObject carrier fun object => do
          let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
          let image ← mkAppM ``Prefunctor.obj #[prefunctor, object]
          let constant ← mkConstWithFreshMVarLevels binding.declaration
          let (arguments, infos, result) ← forallMetaTelescopeReducing (← inferType constant)
          unless arguments.size > binding.numerals do
            throwError "the whole source operation has no object parameter"
          unless (← whnfR result).isAppOf ``Quiver.Hom do
            throwError "the source operation does not retain its whole morphism result"
          let objectIndex := arguments.size - 1 - binding.numerals
          unless ← isDefEq (← inferType arguments[objectIndex]!) (← inferType image) <&&>
              isDefEq arguments[objectIndex]! image do
            throwError "the source operation has a different complete routed object"
          withRigidArguments arguments infos 0 objectIndex fun prefixParameters => do
            withRigidArguments arguments infos (objectIndex + 1) arguments.size
                fun suffixParameters => do
              let body ← instantiateMVars (mkAppN constant arguments)
              mkLambdaFVars (parameters ++ prefixParameters ++ #[object] ++ suffixParameters) body
    return ⟨source, route, binding, term⟩

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

/-- An actual registered cell action, retaining its complete directed transformation. -/
structure SourceCellComponent where
  private mk ::
  entry : CellEntry
  inverse : Bool
  parameters : Array SourceTerm
  source : SourceCategory
  target : SourceCategory
  object : SourceTerm
  transformation : SourceTerm
  left : SourceTerm
  right : SourceTerm
  value : SourceTerm

/-- Form the actual directed component of a source-owned cell at a checked native object.
Reuse: CellEntry, SemanticState.cellEndpoints, Iso.hom/inv and NatTrans.app.
The source row and full native functor/category structures fix the endpoints and direction. -/
opaque SourceSession.cellComponent (session : SourceSession) (reference : Syntax)
    (id : NaturalTransformationId) (parameters : Array SourceTerm) (source : SourceCategory)
    (object : SourceTerm) (inverse : Bool := false) : TermElabM SourceCellComponent := do
  let state ← semanticState
  let #[entry] := state.cells.filter (·.id == id)
    | throwError "a source cell component requires one registered cell"
  unless source.expression.syntacticEq entry.source do
    throwError "the cell has a different complete symbolic source category"
  if inverse && !entry.invertible then
    throwError "the source cell has no registered inverse"
  discard <| checkedDeclaration entry.declaration
  for ref in entry.left ++ entry.right do checkEdgeDeclarations state ref
  let #[transformation, left, right, target, value] ← session.elaborateMany reference
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
    let object ← object.source.inContext context
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
    unless ← isDefEq (← inferType object) carrier do
      throwError "the source cell object has a different complete native category"
    let value ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, object]
    return #[transformation, left, right, leftTarget, value]
    | throwError "source cell formation returned an invalid expression family"
  return ⟨entry, inverse, parameters, source, ⟨entry.target, target⟩, object,
    transformation, left, right, value⟩

end CasCompiler
