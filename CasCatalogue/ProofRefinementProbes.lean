module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Engineering checks of the full formal constructor and its original computational source.
They register no computation and introduce no mathematical expected answer. -/
run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
      "(Fin(2) × ℤ/3) in FiniteSets"
    | throwError "the proof-refinement input did not parse"
  let trace ← Trace.new
  let .object value category .. ← (eval {} parsed).run { trace := some trace }
    | throwError "the supplied finite object was not read"
  let some (.proofRefinement classifier sourceCategory targetCategory source action identity) ←
      trace.node? value
    | throwError "the refinement did not retain its complete formal provenance"
  let state ← registryState
  let some owner := state.classifier? classifier | throwError "classifier missing"
  let some host := state.category? owner.host | throwError "classifier host missing"
  unless sourceCategory == host.id && targetCategory == category.id do
    throwError "the refinement changed its complete categories"
  let image ← Semantic.objOf action value
  unless (← withTransparency .all <| isDefEq image source) &&
      (← Decide.kernelAccepts (← mkEq image source) identity) do
    throwError "the refinement changed the supplied full object"

run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "ℕ in FiniteSets"
    | throwError "the negative refinement input did not parse"
  let rejected ← try
    discard <| (eval {} parsed).run {}
    pure false
  catch error =>
    if (← Outcome.ofException error).kind == "invalid" then pure true else throw error
  unless rejected do throwError "a proof refinement discarded its original obligation"

/- A bound copy takes the generic path rather than a pre-registered named refinement.
The exact forgetful prefix must restore the original request without consulting a leaf. -/
run_elab do
  let .ok sourceSyntax := Parser.runParserCategory (← getEnv) `cas_term "Fin(3)"
    | throwError "the source did not parse"
  let .ok refinedSyntax := Parser.runParserCategory (← getEnv) `cas_term "X in FiniteSets"
    | throwError "the refinement did not parse"
  let trace ← Trace.new
  let original ← (eval {} sourceSyntax).run { trace := some trace }
  let .object source .. := original | throwError "the source is not an object"
  let .object value .. ← (eval {} refinedSyntax).run
      { trace := some trace, bound := [(`X, original)] }
    | throwError "the bound source did not refine"
  let some (.proofRefinement classifier sourceCategory targetCategory _ action identity) ← trace.node? value
    | throwError "the bound source bypassed the generic proof refinement"
  let harness ← Harness.empty
  let base ← realize harness trace "the original full source" source
  let refined ← realize harness trace "the generically refined source" value
  let restored ← proofRefinementBase trace refined action
  unless restored.form.id == base.form.id && restored.json == base.json &&
      (← withTransparency .all <| isDefEq restored.value base.value) do
    throwError "the exact forgetful action changed the original computational request"
  let total ← mkAppHere ``CategoryTheory.Bundled.α #[← instantiateFresh
    (← categoryNamed (← registryState) "FiniteSets").declaration]
  let wrong ← mkAppHere ``CategoryTheory.Functor.id #[total]
  let rejected ← try
    discard <| proofRefinementBase trace refined wrong
    pure false
  catch _ => pure true
  unless rejected do throwError "a different complete action unwrapped a refinement"

  let .ok otherSyntax := Parser.runParserCategory (← getEnv) `cas_term "Fin(4)"
    | throwError "the independent source did not parse"
  let .object other .. ← (eval {} otherSyntax).run { trace := some trace }
    | throwError "the independent source is not an object"
  let wrongTrace ← IO.mkRef ((← trace.get).insert value
    (.proofRefinement classifier sourceCategory targetCategory other action identity))
  let rejected ← try
    discard <| proofRefinementBase wrongTrace refined action
    pure false
  catch _ => pure true
  unless rejected do throwError "a different full source unwrapped a refinement"

/- A structure classifier cannot be populated by synthesizing chosen nonproof data from a
carrier, even if some ambient Lean instance happens to exist. -/
run_elab do
  let state ← registryState
  let some target := state.categories.find? (·.id.raw == "cat.magmas")
    | throwError "the registered structure classifier is absent"
  let .classifierTotal classifier := target.expression
    | throwError "the registered structure category is not its classifier total"
  let source ← elabTermAndSynthesize (← `((Fin 2 : Type))) none
  let rejected ← try
    discard <| ProofRefinement.construct state classifier target source
    pure false
  catch error =>
    if (← Outcome.ofException error).kind == "invalid" then pure true else throw error
  unless rejected do throwError "a bare carrier acquired unsupplied chosen structure"
