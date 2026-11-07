module

public import CasCompiler.RouteGrammar
public import LeanCategories.Catalogue.Registry.Semantic

public section

namespace CasCompiler

open Lean CasCatalogue

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

end CasCompiler
