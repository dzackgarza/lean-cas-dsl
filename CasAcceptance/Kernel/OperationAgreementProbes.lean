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

/- An immutable registry fixture adds an alias of an already accepted declaration.
The public mathematical validator accepts it; no global row or new mathematics is
registered. Both storage orders must retain the explicitly chosen address. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some original := state.operations.find? fun row =>
      row.category == CategoryId.rings && row.name == "·"
    | throwError "the accepted ring operation is absent"
  let aliasRow : OperationEntry := { original with
    id := ⟨"engineering.operation.accepted_alias"⟩, name := "accepted_alias_control" }
  validateOperation state.toSemanticState aliasRow
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "the alias control's complete source did not parse"
  let source ← (eval {} term).run {}
  let candidate ← completeCandidate original source #[]
  let augmented : RegistryState := { state with operations := state.operations.push aliasRow }
  let trace ← Trace.new
  let mut keys := #[]
  for ordered in #[augmented, { augmented with operations := augmented.operations.reverse }] do
    for binding in #[original, aliasRow] do
      let some chosen ← OperationAgreement.selectedEntry ordered original.declaration
          candidate.application 2 (some binding.id)
        | throwError "the exact accepted operation alias was lost"
      unless chosen.id == binding.id do
        throwError "operation storage order changed the selected address"
      let key ← Trace.recordOperation (some trace) candidate.application
        (.operationApply chosen.id #[] #[] candidate.application candidate.application)
      keys := keys.push (key, chosen.id)
    let rejected ← try
      discard <| OperationAgreement.selectedEntry ordered original.declaration candidate.application 2
      pure false
    catch error =>
      if Exception.isSemanticAmbiguity error then pure true else throw error
    unless rejected do throwError "an unaddressed alias was selected by declaration storage order"
  for (key, expected) in keys do
    let some (.operationApply actual ..) ← trace.node? key
      | throwError "merging operation aliases discarded their independent trace key"
    unless actual == expected do
      throwError "merging operation aliases replaced the selected accepted ID"

/-- Change only the implementation of a proof in a typed identity cast. -/
private def proofVariant (value : Expr) (expanded : Bool) : TermElabM Expr := do
  let proof ← mkEqRefl (← inferType value)
  let proof ← if expanded then mkAppM ``Eq.trans #[proof, proof] else pure proof
  mkAppM ``Eq.mp #[proof, value]

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some ringProduct := state.operations.find? fun row =>
      row.category == CategoryId.rings && row.name == "·"
    | throwError "the source-order control has no ring operation"
  let some monoidProduct := state.operations.find? fun row =>
      row.category == CategoryId.monoids && row.name == "·"
    | throwError "the source-order control has no monoid operation"
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "F9x in CommutativeRings"
    | throwError "the source-order control did not parse"
  let source ← (eval {} term).run {}
  let first ← completeCandidate ringProduct source #[]
  let second ← completeCandidate monoidProduct source #[]
  let #[a] := first.sources | throwError "the first complete route is not unique"
  let #[b] := second.sources | throwError "the second complete route is not unique"
  let a₀ := { a with receiver := ← proofVariant a.receiver false }
  let a₁ := { a with receiver := ← proofVariant a.receiver true }
  let b₀ := { b with receiver := ← proofVariant b.receiver false }
  let b₁ := { b with receiver := ← proofVariant b.receiver true }
  unless (← OperationAgreement.sameSourceData a₀ a₁) &&
      (← OperationAgreement.sameSourceData b₀ b₁) do
    throwError "proof implementation changed complete source multiplicity"
  let before ← OperationAgreement.orderSources #[a₀, b₁]
  let after ← OperationAgreement.orderSources #[b₀, a₁]
  unless (← before.mapM OperationAgreement.sourceKey) ==
      (← after.mapM OperationAgreement.sourceKey) do
    throwError "proof implementation or row order changed complete source indices"
  unless (← OperationAgreement.sourceKey a₀) != (← OperationAgreement.sourceKey b₀) do
    throwError "complete source ordering erased distinct ordered routes"
  let left := { first with sources := #[a₀], result := ← proofVariant first.result false }
  let right := { first with sources := #[a₁], result := ← proofVariant first.result true }
  unless (← OperationAgreement.candidateKey left) == (← OperationAgreement.candidateKey right) do
    throwError "proof implementation changed the complete candidate key"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some operation := state.operations.find? fun row =>
      row.category == CategoryId.rings && row.name == "·"
    | throwError "the callable-kind control has no accepted operation"
  let operationAlias : OperationEntry := { operation with
    id := ⟨"engineering.operation.callable_alias"⟩, name := "callable_alias_control" }
  validateOperation state.toSemanticState operationAlias
  let first : MorphismEntry := {
    id := ⟨"engineering.morphism.first_alias"⟩, declaration := operation.declaration
    category := CategoryId.sets, name := "first_callable_alias_control" }
  let second : MorphismEntry := { first with
    id := ⟨"engineering.morphism.second_alias"⟩, name := "second_callable_alias_control" }
  validateMorphism state.toSemanticState first
  validateMorphism state.toSemanticState second
  let augmented : RegistryState := { state with
    operations := state.operations.push operationAlias
    morphisms := state.morphisms ++ #[first, second] }
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "the exact callable's source did not parse"
  let source ← (eval {} term).run {}
  let candidate ← completeCandidate operation source #[]
  let trace ← Trace.new
  let mut keys := #[]
  for ordered in #[augmented, { augmented with
      operations := augmented.operations.reverse, morphisms := augmented.morphisms.reverse }] do
    for row in #[first, second] do
      let (operation, address) ← (familyBinding ordered row.declaration row.category
        candidate.application 2 none (some row.id.raw)).run {}
      unless operation.isNone && address == some row.id.raw do
        throwError "an exact callable was replaced by an unrelated operation or alias"
      let key ← Trace.recordCallable (some trace) candidate.application
        (.namedCallable row.id.raw row.category #[])
      keys := keys.push (key, row.id.raw)
  for (key, expected) in keys do
    let some (.namedCallable actual ..) ← trace.node? key
      | throwError "merging exact callable aliases discarded their independent trace key"
    unless actual == expected do
      throwError "merging named callable aliases changed their accepted address"
