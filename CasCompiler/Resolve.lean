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

/-- Symbolic route family over the exact frozen registry inventory.
Native dependent operation formation and comparison evidence are separate consumers. -/
structure SourceRoutes where
  private mk ::
  private state : SemanticState
  source : CategoryExpr
  targets : Array CategoryExpr
  private symbols : Array SourceSymbol
  edges : Array StructuralEdge
  language : RouteGrammar.RouteLanguage

private def sourceRoutes (state : SemanticState) (source : CategoryExpr)
    (targets : Array CategoryExpr) : CoreM SourceRoutes := do
  let constructors := (state.constructors.filter (·.functorialAction.isSome)).map (·.id)
  let edges := state.structuralEdges
  let build : StateM (Array SourceSymbol)
      (RouteGrammar.Word × Array RouteGrammar.Word × Array RouteGrammar.PrefixRule) := do
    let initial ← encode constructors source
    let targets ← targets.mapM (encode constructors)
    let rules ← edges.mapM fun edge => do
      return { lhs := ← encode constructors edge.source,
        rhs := ← encode constructors edge.target : RouteGrammar.PrefixRule }
    return (initial, targets, rules)
  let ((initial, encodedTargets, rules), symbols) := build.run #[]
  let .ok language := RouteGrammar.compile rules initial encodedTargets
    | throwError "the source registry produced an invalid ground-prefix route system"
  return ⟨state, source, targets, symbols, edges, language⟩

/-- Project one independently supplied owner target from the current accepted source inventory.
Reuse: structuralEdges/edgesFrom and the source correspondence in #66 comment 6693871042. -/
opaque SourceRoutes.forOwner (source owner : CategoryExpr) : CoreM SourceRoutes := do
  sourceRoutes (← semanticState) source #[owner]

/-- Bind the surface operation name before any arity filtering, exactly as the source does. -/
opaque SourceRoutes.forOperation (source : CategoryExpr) (name : String) : CoreM SourceRoutes := do
  let state ← semanticState
  let targets := state.categories.filterMap fun category =>
    if (state.operationBindings category.expression name).isEmpty then none
    else some category.expression
  sourceRoutes state source targets

/-- Reconstruct a selected symbolic derivation and validate it against the frozen source.
Actual edge references and constructor actions remain attached to each source occurrence. -/
opaque SourceRoutes.reconstruct (routes : SourceRoutes) (trace : RouteGrammar.Word) : CoreM Route := do
  let .ok occurrences := routes.language.reconstruct trace
    | throwError "the selected trace is not a first-hit source derivation"
  let mut current := routes.source
  let mut refs := #[]
  for occurrence in occurrences do
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
  unless routes.targets.any (·.syntacticEq current) do
    throwError "the reconstructed source route lost its exact binding target"
  let some steps := routes.state.routeEdges? routes.source current refs
    | throwError "the reconstructed route does not belong to the retained source inventory"
  return { source := routes.source, target := current, steps }

end CasCompiler
