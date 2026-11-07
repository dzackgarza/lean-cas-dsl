module

import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects

open Lean CasCompiler CasCatalogue

run_cmd do
  let state ← liftCoreM semanticState
  let some edge := state.structuralEdges.find? fun edge =>
      match edge.ref with
      | .classifierForget _ => !edge.source.syntacticEq edge.target
      | _ => false
    | throwError "the actual source imports supply no classifier-forget control"
  let routes ← liftCoreM <| SourceRoutes.forOwner edge.source edge.target
  let some index := routes.edges.findIdx? (·.ref == edge.ref)
    | throwError "the source route inventory discarded an actual structural edge"
  unless routes.language.grammar.contains #[index] do
    throwError "the source grammar discarded a registered first-hit route"
  let route ← liftCoreM <| routes.reconstruct #[index]
  unless route.refs == #[edge.ref] && route.source.syntacticEq edge.source &&
      route.target.syntacticEq edge.target do
    throwError "source reconstruction changed an edge identity or complete endpoint"
  let some constructor := state.constructors.find? (·.functorialAction.isSome)
    | throwError "the actual source imports supply no unary structural action control"
  let source := CategoryExpr.construct constructor.id #[.category edge.source]
  let target := CategoryExpr.construct constructor.id #[.category edge.target]
  let derived ← liftCoreM <| SourceRoutes.forOwner source target
  let some index := derived.edges.findIdx? (·.ref == edge.ref)
    | throwError "the derived source inventory discarded its original edge"
  unless derived.language.grammar.contains #[index] do
    throwError "the source grammar discarded an actual constructor-image route"
  let route ← liftCoreM <| derived.reconstruct #[index]
  unless route.refs == #[.constructMap constructor.id edge.ref] &&
      route.source.syntacticEq source && route.target.syntacticEq target do
    throwError "source reconstruction lost its exact constructor action"
  let some binding := state.operations[0]?
    | throwError "the actual source imports supply no operation binding control"
  let some owner := state.categories.find? (·.id == binding.category)
    | throwError "the source operation has no registered owner"
  let bound ← liftCoreM <| SourceRoutes.forOperation owner.expression binding.name
  unless bound.language.grammar.contains #[] && bound.language.grammar.distinctWordCount == 1 do
    throwError "the source operation name did not bind at its first owner"
