/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.QuestionComparison
meta import CasCatalogue.QuestionComparison
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Engineering checks for complete, already accepted resolution-comparison data.
No route is selected here and no mathematical or computational answer is asserted. -/

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Realize

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some rings := state.categories.find? (·.id.raw == "cat.rings")
    | throwError "the comparison control has no registered ring category"
  let receiver ← elabTermAndSynthesize (← `(RingCat.of ℤ)) none
  let .ok resolution := state.resolveMethod rings.expression "cardinality"
    | throwError "the comparison control has no coherent method resolution"
  let expected ← Semantic.validateResolutionComparisons state resolution (some receiver)
  unless !expected.isEmpty do
    throwError "the comparison control has no accepted comparison data"
  let trace ← Trace.new
  let (value, _) ← Semantic.methodIn "cardinality" receiver rings.expression (some trace)
  let some (.method id route original retained application) ← trace.node? value
    | throwError "the method reading lost its operation record"
  unless id == resolution.method.id && route == resolution.route.refs &&
      original == receiver && retained.map (·.1) == resolution.comparisonWitnesses do
    throwError "the method changed its selected receiver, route or comparison contexts"
  unless ← QuestionIdentity.equivalentTerms (retained.map (·.2)) expected do
    throwError "the method did not retain the complete checked comparison values"
  Semantic.checkRecordedRouteComparisons resolution.comparisonWitnesses expected retained
  let node := Node.method id route original retained application
  let empty := Node.method id route original #[] application
  if ← QuestionIdentity.equivalentNode node empty then
    throwError "independent comparison erased the method's accepted comparisons"
  let encoded ← snapshot #[(value, node)]
  let snapshotOperation (serialized : String) : TermElabM (Array Json) := do
    let .ok document := Json.parse serialized
      | throwError "the counterfactual operation snapshot is not JSON"
    let .ok roots := (document.getObjVal? "roots").bind (·.getArr?)
      | throwError "the counterfactual operation snapshot has no records"
    let .ok row := roots[0]!.getArr?
      | throwError "the counterfactual operation record changed its shape"
    let .ok operation := row[1]!.getArr?
      | throwError "the counterfactual operation fields are absent"
    return operation
  -- Counterfactual records get their own complete producer keys. The actual
  -- method value and its original record above remain unchanged.
  let emptyTrace ← Trace.new
  let emptyValue ← Trace.recordProduced (some emptyTrace) (Trace.unanchor value) empty
  let emptyEncoded ← snapshot #[(emptyValue, empty)]
  if encoded == emptyEncoded then
    throwError "the operation snapshot erased the method's accepted comparisons"
  let .ok document := Json.parse encoded | throwError "the operation snapshot is not JSON"
  let .ok roots := (document.getObjVal? "roots").bind (·.getArr?)
    | throwError "the operation snapshot has no complete records"
  let .ok row := roots[0]!.getArr? | throwError "the operation record changed its shape"
  let .ok operation := row[1]!.getArr? | throwError "the operation fields are absent"
  let .ok comparisons := operation[4]!.getArr?
    | throwError "the method's comparison field is absent"
  unless comparisons.size == retained.size do
    throwError "the snapshot lost a complete accepted comparison"
  for ((context, _), record) in retained.zip comparisons do
    let .ok fields := record.getArr? | throwError "a comparison record is incomplete"
    unless fields.size == 2 && fields[0]! == OperationAgreement.encodeRouteComparison context do
      throwError "a comparison lost its constructor or whiskering context"
  -- A fresh key also embeds its node description. Inspect the serialized node
  -- field itself, so a root-key difference cannot satisfy this comparison check.
  let emptyOperation ← snapshotOperation emptyEncoded
  let .ok emptyComparisons := emptyOperation[4]!.getArr?
    | throwError "the empty comparison field is absent"
  unless emptyComparisons.isEmpty && emptyOperation != operation do
    throwError "the serialized operation did not retain its empty comparison field"
  let first := retained[0]!
  let changedContext := { first.1 with
    after := first.1.after.push (.functor ⟨"probe.changed_comparison_context"⟩) }
  let changed := retained.set! 0 (changedContext, first.2)
  let altered := Node.method id route original changed application
  if ← QuestionIdentity.equivalentNode node altered then
    throwError "independent comparison erased a changed whiskering context"
  let alteredTrace ← Trace.new
  let alteredValue ← Trace.recordProduced (some alteredTrace) (Trace.unanchor value) altered
  let alteredEncoded ← snapshot #[(alteredValue, altered)]
  if encoded == alteredEncoded then
    throwError "the snapshot erased a changed whiskering context"
  let alteredOperation ← snapshotOperation alteredEncoded
  let .ok alteredComparisons := alteredOperation[4]!.getArr?
    | throwError "the altered comparison field is absent"
  unless alteredComparisons.size == changed.size && alteredOperation != operation do
    throwError "the serialized operation erased its altered comparison field"
  for ((context, _), record) in changed.zip alteredComparisons do
    let .ok fields := record.getArr?
      | throwError "an altered comparison record is incomplete"
    unless fields.size == 2 && fields[0]! == OperationAgreement.encodeRouteComparison context do
      throwError "an altered comparison lost its exact constructor or whiskering context"
  for candidate in #[empty, altered] do
    let rejected ← try
      discard <| snapshot #[(value, candidate)]
      pure false
    catch _ => pure true
    unless rejected do
      throwError "the original producer key accepted an altered comparison record"
  for candidate in #[#[], changed, retained.set! 0 (first.1, mkNatLit 0)] do
    let rejected ← try
      Semantic.checkRecordedRouteComparisons resolution.comparisonWitnesses expected candidate
      pure false
    catch _ => pure true
    unless rejected do
      throwError "execution replaced the originally retained comparison data"
