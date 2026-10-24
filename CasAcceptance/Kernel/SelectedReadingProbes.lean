module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language

/- These engineering observations use complete registered declarations. They do not
compute backend answers or change the independently supplied assertions. -/

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term
      "map presentation(cyclic_quotient_residue(5)) along Aut()"
    | throwError "the complete core action did not parse"
  let unrecorded ← (eval {} term).run {}
  let trace ← Trace.new
  let recorded ← (eval {} term).run { trace := some trace }
  let (plain, _, _, plainContext, _, _) ← (morphismContext unrecorded).run {}
  let (retained, _, _, retainedContext, _, _) ← (morphismContext recorded).run {}
  unless plainContext.expression.syntacticEq retainedContext.expression &&
      (← withTransparency .all <| isDefEq plain retained) do
    throwError "requesting an execution trace changed the complete core action"
  unless !plain.hasMVar && !plain.hasLevelMVar && (← isTypeCorrect plain) do
    throwError "the trace-free core action has an incomplete type"
  let some (.constructionMap _ _ _ _ actualMap) ← trace.node? retained
    | throwError "the core action discarded its actual comparison map"
  let some (.coreIso _ _ _ forward backward) ← trace.node? actualMap
    | throwError "the core action omitted one of its accepted inverse arrows"
  unless (← isTypeCorrect forward) && (← isTypeCorrect backward) do
    throwError "the two retained comparison arrows are not complete typed maps"

run_cmd liftTermElabM <| withoutErrToSorry do
  for text in #["assert (1 = 2 in ℤ) = false", "assert (1 = 1 in ℤ) = true"] do
    withCurrHeartbeats do
      let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
        | throwError "a truth-value comparison did not parse"
      let .judged _ proposition expected _ ← (claim {} statement).run {}
        | throwError "a truth-valued element was not read as a declared decision"
      unless expected.isSome && !proposition.hasMVar && !proposition.hasLevelMVar &&
          (← isProp proposition) do
        throwError "the truth-value decision lost its actual typed proposition"
  let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt "assert (1 in ℤ) = false"
    | throwError "the unrelated-element rejection input did not parse"
  let rejected ← try
    discard <| (claim {} statement).run {}
    pure false
  catch error =>
    if Exception.interpretationKind error == .invalid then pure true else throw error
  unless rejected do throwError "an arbitrary ring point was treated as a truth value"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the generalized presentation application did not parse: {text}"
    return term
  let trace ← Trace.new
  let original ← (eval {} (← parse "F9x_constants()")).run { trace := some trace }
  let (_, originalDomain, _, _, sourceValue, _) ← (morphismContext original).run {}
  let applied ← (eval {} (← parse
    "(presentation(F9translation()))(F9x_constants())")).run { trace := some trace }
  let (result, source, target, context, retainedSource, _) ← (morphismContext applied).run {}
  unless context.expression.syntacticEq (.atom CategoryId.sets) &&
      retainedSource.sameSelection sourceValue &&
      (← withTransparency .all <| isDefEq source originalDomain) do
    throwError "a presentation changed the generalized coefficient map's original domain"
  let expected ← (eval {} (← parse "F9y_constants()")).run { trace := some trace }
  let (_, expectedSource, expectedTarget, _, _, _) ← (morphismContext expected).run {}
  unless (← withTransparency .all <| isDefEq source expectedSource <&&>
      isDefEq target expectedTarget) && !result.hasMVar && !result.hasLevelMVar &&
      (← isTypeCorrect result) do
    throwError "the whole presentation result has incorrect declared carrier endpoints"
  let some (.contextualComposition _ _ action _ _ _) ← trace.node? result
    | throwError "the generalized presentation lost its actual composition"
  let some (.contextualRoute _ _ edges applications _ true) ← trace.node? action
    | throwError "the structured presentation was not carried by its declared action"
  unless !edges.isEmpty && edges.size == applications.size do
    throwError "the presentation carrier action lost its complete ordered functor applications"
