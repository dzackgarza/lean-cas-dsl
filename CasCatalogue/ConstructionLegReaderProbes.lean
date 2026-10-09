module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Defining-leg access retains the actual construction and its typed index. -/
run_cmd liftTermElabM do
  let parse (text : String) : TermElabM Syntax := do
    let .ok syntaxValue := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "construction-leg probe did not parse: {text}"
    return syntaxValue
  let trace ← Trace.new
  let kernel ← (eval {} (← parse "kernel(sign(3))")).run { trace := some trace }
  let .object apex .. := kernel | throwError "kernel did not return its actual apex"
  let some (.limit originalId originalDiagram originalLift) ← trace.node? apex
    | throwError "the construction lost its registered request"
  for tracing in [false, true] do
    let .morphism hom source _ _ _ ← (eval {} (← parse "K.leg(0)")).run
        { trace := if tracing then some trace else none, bound := [(`K, kernel)] }
      | throwError "a defining leg did not return a typed morphism"
    unless !hom.hasMVar && !hom.hasLevelMVar && (← isTypeCorrect hom) &&
        (← isDefEq source apex) do
      throwError "a defining leg changed its actual apex"
    if tracing then
      let some (.limitProjection receiver index) ← trace.node? hom
        | throwError "the actual leg lost its construction projection"
      unless receiver == apex && !index.hasMVar && !index.hasLevelMVar do
        throwError "the exact construction index was not retained"
      let some (.limit retainedId retainedDiagram retainedLift) ← trace.node? apex
        | throwError "leg access erased the original construction provenance"
      unless retainedId == originalId && retainedDiagram == originalDiagram &&
          retainedLift == originalLift do
        throwError "leg access replaced the original construction provenance"
  let mut rejected := false
  try
    discard <| (eval {} (← parse "K.leg(2)")).run { bound := [(`K, kernel)] }
  catch error =>
    if CasCatalogue.Exception.stratum? error == some .invalid then rejected := true
    else throw error
  unless rejected do throwError "an out-of-range actual shape index was admitted"
