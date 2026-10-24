/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

/- Engineering checks for the independently specified universal comparison rule.
These check complete typed requests and evidence; they supply no backend answers. -/

run_cmd liftTermElabM <| withoutErrToSorry do
  for text in #["2 * generator(F9x in CommutativeRings)",
      "2 * 3 in PrimeResidues(5, proof(by decide))"] do
    withCurrHeartbeats do
      let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
        | throwError "the inherited-operation input did not parse"
      let trace ← Trace.new
      let .element result _ ← (eval {} term).run { trace := some trace }
        | throwError "the inherited operation did not form a complete point"
      let some (.operationEquivalence representative chosen candidates comparisons) ← trace.node? result
        | throwError "the inherited operation discarded its checked complete class"
      unless result != representative && candidates.size > 1 && !comparisons.isEmpty do
        throwError "the operation class lost a distinct child or comparison"
      OperationAgreement.validate representative chosen candidates comparisons
      let some comparison := comparisons[0]? | unreachable!
      let malformed := { comparison with parameters := comparison.parameters.push (mkNatLit 0) }
      let rejected ← try
        OperationAgreement.validate representative chosen candidates (comparisons.set! 0 malformed)
        pure false
      catch error =>
        if Exception.interpretationKind error == .invalid then pure true else throw error
      unless rejected do throwError "the operation class accepted an altered dependent context"

private def completeCandidate (entry : OperationEntry) (source : Value)
    (numerals : Array Nat) : TermElabM OperationCandidate := do
  let #[(application, sources)] ← (selectedOperationApplicationsWithSources
      entry.declaration entry.category source numerals (some entry.name)).run {}
    | throwError "the declared operation did not retain one complete application"
  return { operation := entry.id, application, result := application, sources }

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some power := state.operations.find? fun row =>
      row.category == CategoryId.rings && row.name == "^"
    | throwError "the declared ring power is absent"
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "the complete selected source did not parse"
  let source ← (eval {} term).run {}
  let first ← completeCandidate power source #[2]
  let second ← completeCandidate power source #[3]
  unless (← OperationAgreement.compare 0 1 first second).isNone do
    throwError "a universal family erased different selected numeral arguments"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some modules := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the complete module owner is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the declared data category is absent"
  let first ← elabTermAndSynthesize (← `(ModuleCat.of ℤ PUnit.{1})) none
  let second ← elabTermAndSynthesize (← `(ModuleCat.of ℚ PUnit.{1})) none
  let carrier ← elabTermAndSynthesize (← `(PUnit.{1})) none
  let target := retainObjectContext (.object carrier sets none none none)
    #[.object first modules none none none, .object second modules none none none]
  let rejected ← try
    discard <| (applyOperation "0" #[] target).run {}
    pure false
  catch error =>
    if Exception.isSemanticAmbiguity error then pure true else throw error
  unless rejected do
    throwError "equal constant results erased independently chosen complete module owners"
