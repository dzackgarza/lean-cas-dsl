module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Modules.IntegerResidueModules
meta import LeanCategories.Catalogue.Semantics.Modules.IntegerResidueModules
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

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

run_cmd liftTermElabM <| withoutErrToSorry do
  for text in #["assert 1 + 1 = 2 in PrimeResidues(5, proof(by decide))",
      "assert 1 * 1 = 1 in PrimeResidues(5, proof(by decide))",
      "assert 2 * generator(F9x in CommutativeRings) = 2 · generator(F9x in CommutativeRings)"] do
    withCurrHeartbeats do
      let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
        | throwError "the selected numeric operation did not parse"
      let trace ← Trace.new
      let .homs left right _ proposition _ _ ← (claim {} statement).run { trace := some trace }
        | throwError "the selected numeric operation lost its element comparison"
      unless !left.hasMVar && !right.hasMVar && (← isProp proposition) &&
          (← isTypeCorrect left) && (← isTypeCorrect right) do
        throwError "a selected numeric operation is not a complete typed question"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let mut scope : Language.Scope := {}
  for text in #["let R := ℤ in Rings",
      "let Scommutative := ZMod(5) in CommutativeRings",
      "let S := view Scommutative along «fun.commutative_rings.ring»()",
      "let q := map integerCoefficients(Scommutative) along «fun.commutative_rings.ring»()",
      "let N := RegularModule(S)", "let M := reindex(N, q)"] do
    let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "the selected module context did not parse"
    let some (name, value) ← letBinding? statement
      | throwError "the selected module context lost a binding"
    scope := scope.insert name value
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "M"
    | throwError "the selected module did not parse"
  let trace ← Trace.new
  let original ← (eval scope term).run { trace := some trace }
  let receiver ← (carrierObject original).run { trace := some trace }
  let state ← registryState
  let some action := state.operations.find? (·.name == "•")
    | throwError "the module scalar action is not registered"
  let #[application] ← (selectedOperationApplications action.declaration action.category
      receiver #[]).run { trace := some trace }
    | throwError "the retained old module competed with the selected restricted module"
  let actual := application.getAppArgs.back!
  unless ← withTransparency .all <| isDefEq actual (← (semanticObject original).run {}) do
    throwError "the scalar operation replaced the selected reindexed module"
  let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt "assert 2 • 3 = 1 in M"
    | throwError "the selected module scalar question did not parse"
  discard <| (claim scope statement).run { trace := some trace }

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "ZMod(5) in Groups"
    | throwError "the selected group did not parse"
  let trace ← Trace.new
  let receiver ← ((eval {} term) >>= carrierObject).run { trace := some trace }
  let domain ← (semanticObject receiver).run {}
  let generic ← (identityAt receiver).run { trace := some trace }
  let .element result _ ← (power {} (.element generic receiver) 2 (some receiver)).run
      { trace := some trace, stage := some receiver }
    | throwError "the literal exponent did not consume the registered power family"
  let some (source, target) := homEnds? (← inferType result)
    | throwError "the registered power lost its generalized point"
  unless (← withTransparency .all <| isDefEq source domain <&&> isDefEq target domain) &&
      !result.hasMVar && !result.hasLevelMVar && (← isTypeCorrect result) do
    throwError "the literal power replaced its original generalized domain"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some ringProduct := state.operations.find? fun row =>
      row.name == "·" && row.category == CategoryId.rings
    | throwError "the explicit ring product is not registered"
  let some monoidProduct := state.operations.find? fun row =>
      row.name == "·" && row.category == CategoryId.monoids
    | throwError "the inherited monoid product is not registered"
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "the selected ring did not parse"
  let trace ← Trace.new
  let receiver ← ((eval {} term) >>= carrierObject).run { trace := some trace }
  let ringBindings ← (selectedOperationApplications ringProduct.declaration ringProduct.category
    receiver #[] (some "·")).run { trace := some trace }
  let fartherBindings ← (selectedOperationApplications monoidProduct.declaration monoidProduct.category
    receiver #[] (some "·")).run { trace := some trace }
  unless ringBindings.size == 1 && fartherBindings.isEmpty do
    throwError "operation lookup crossed an explicit registered binding on its structural path"
  let mut selected : Array Expr := #[]
  for text in #["view (ℤ in Rings) along «fun.rings.multiplicative_monoid»()",
      "view (view (view (ℤ in Rings) along «fun.rings.additive_group»()) along «fun.additive_groups.to_groups»()) along «fun.groups.monoid»()"] do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "an independently selected operation port did not parse"
    let receiver ← ((eval {} term) >>= carrierObject).run { trace := some trace }
    let #[application] ← (selectedOperationApplications monoidProduct.declaration
      monoidProduct.category receiver #[] (some "·")).run { trace := some trace }
      | throwError "the explicit monoid port did not retain one whole operation"
    selected := selected.push application
  if ← (sameOperationApplication selected[0]! selected[1]!).run {} then
    throwError "different additive and multiplicative ports were identified by their shared carrier"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term
      "(s ↦ {rev(5)(x) | x ∈ s}) in 𝒫(Fin(5)) → 𝒫(Fin(5))"
    | throwError "the generalized direct-image map did not parse"
  let trace ← Trace.new
  let value ← (eval {} term).run { trace := some trace }
  let (arrow, source, target, context, _, _) ← (morphismContext value).run {}
  let .ok expectedTerm := Parser.runParserCategory (← getEnv) `cas_term "𝒫(Fin(5))"
    | throwError "the direct-image domain did not parse"
  let expected ← ((eval {} expectedTerm) >>= semanticObject).run {}
  unless context.expression.syntacticEq (.atom CategoryId.sets) &&
      (← withTransparency .all <| isDefEq source expected <&&> isDefEq target expected) &&
      !arrow.hasMVar && !arrow.hasLevelMVar && (← isTypeCorrect arrow) do
    throwError "the direct image lost its original full subset domain"
  let state ← registryState
  let some power := state.powerObjects.find? (·.directImage.isSome)
    | throwError "the declared direct-image role is absent"
  let some row := state.morphisms.find? (fun row => some row.declaration == power.directImage)
    | throwError "the direct-image role has no public callable signature"
  unless (← trace.get).toArray.any (fun (_, node) => match node with
      | .namedMorphism id parameters => id == row.id && parameters.size == 3
      | _ => false) do
    throwError "the direct image omitted its complete declared map parameter"
