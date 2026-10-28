/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import CasCatalogue.QuestionComparison
meta import CasCatalogue.QuestionComparison
import LeanCategories.Catalogue.Semantics
meta import LeanCategories.Catalogue.Semantics

/-! Engineering checks of preparation, explicit audit export and execution.
The refuted arithmetic statement is the existing QuestionProbes control. The
cardinality statement and wrong-answer fixture come unchanged from
RegistrationProbes. These checks compare retained requests, actual dispatches
and failure boundaries; they admit no new mathematics or acceptance assertions. -/

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

namespace CasCatalogue.PreparedQuestionProbes
meta section

private def statement (text : String) : TermElabM Syntax := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
    | throwError "the existing fixed-question control did not parse: {text}"
  return parsed

private def sameRequest (prepared : PreparedQuestion) (exported : TypedQuestion) :
    TermElabM Unit := do
  unless (← QuestionIdentity.equivalentClaim prepared.claim exported.claim) &&
      exported.claim.terms == prepared.claim.terms &&
      exported.trace.size == prepared.trace.size do
    throwError "explicit export replaced the complete prepared typed request"
  for (term, node) in prepared.trace.toArray do
    unless exported.trace[term]? == some node do
      throwError "explicit export changed an exact selected operation record"

/-- Fresh execution state, with the same admitted interfaces and actual session.
No completed result or invocation is carried between the two executions. -/
private def observedHarness (base : Harness) : IO (Harness × IO.Ref (Array Json)) := do
  let isolated ← Harness.empty
  let calls ← IO.mkRef (#[] : Array Json)
  return ({ isolated with
    admitted := base.admitted
    rejected := base.rejected
    backends := base.backends
    root := base.root
    connections := base.connections
    computationOnly := true
    dispatches := some calls }, calls)

private def undispatched (harness : Harness) (calls : IO.Ref (Array Json)) :
    TermElabM Unit := do
  unless (← calls.get).isEmpty && (← harness.replies.get).isEmpty do
    throwError "a rejected prepared question dispatched before its failure"

-- Each public request uses its ordinary command heartbeat budget. These are
-- separate calls, not an increased limit for one preparation or execution.
run_cmd withoutModifyingEnv <| liftTermElabM <| withoutErrToSorry do
  let parsed ← statement "assert 2 + 3 = 6"
  let stages ← IO.mkRef (#[] : Array (String × Nat))
  let prepared ← withCurrHeartbeats <| prepare {} parsed (some stages)
  for (stage, _) in ← stages.get do
    unless stage == "semantic_reading" || stage == "trace_instantiation" do
      throwError "ordinary request preparation constructed an audit export"
  let exported ← withCurrHeartbeats <| exportQuestion prepared (some stages)
  unless (← stages.get).any (·.1 == "question_construction") do
    throwError "explicit export did not construct the complete question identity"
  withCurrHeartbeats <| sameRequest prepared exported
  let harness ← Harness.empty
  let calls ← IO.mkRef (#[] : Array Json)
  let harness := { harness with dispatches := some calls }
  let ordinary ← withCurrHeartbeats <| evaluatePrepared harness prepared
  let audited ← withCurrHeartbeats <| evaluate harness exported
  unless ordinary.toOutcome.kind == audited.toOutcome.kind &&
      ordinary.toOutcome.kind == "wrong" do
    throwError "export changed the fixed request's execution outcome"
  undispatched harness calls
  let afterExecution ← withCurrHeartbeats <| exportQuestion prepared
  unless afterExecution.identity == exported.identity do
    throwError "execution changed the previously prepared question"
  let (direct, _) ← withCurrHeartbeats <| run harness {} parsed
  let (asking, _, identity) ← withCurrHeartbeats <| runAsking harness {} parsed
  unless direct.kind == ordinary.toOutcome.kind && asking.kind == direct.kind &&
      identity == some exported.identity do
    throwError "ordinary and audit entry points used different questions or outcomes"
  undispatched harness calls

-- Nonempty dispatch agreement uses the existing deliberately wrong port
-- specimen. Agreement tests this fixture's plumbing, not arbitrary leaf purity
-- or mathematical correctness. The two runs share no computed-result state.
run_cmd withoutModifyingEnv <| liftTermElabM <| withoutErrToSorry do
  let parsed ← statement "assert |Fin(3)| = 3"
  let prepared ← withCurrHeartbeats <| prepare {} parsed
  let exported ← withCurrHeartbeats <| exportQuestion prepared
  withCurrHeartbeats <| sameRequest prepared exported
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let base ← Harness.load (some (root / "registration_wrong.json"))
  unless base.rejected.isEmpty && base.admitted.size == 2 do
    throwError "the existing wrong-answer fixture lost its admitted interfaces"
  try
    let .ok _ ← (base.connection "probe" : IO _)
      | throwError "the existing wrong-answer fixture could not start"
    let (ordinaryHarness, ordinaryCalls) ← observedHarness base
    let (auditedHarness, auditedCalls) ← observedHarness base
    let ordinary ← withCurrHeartbeats <| evaluatePrepared ordinaryHarness prepared
    let audited ← withCurrHeartbeats <| evaluate auditedHarness exported
    let ordinaryEvents ← ordinaryCalls.get
    let auditedEvents ← auditedCalls.get
    unless ordinary.toOutcome.kind == "wrong" &&
        audited.toOutcome.kind == ordinary.toOutcome.kind &&
        ordinaryEvents.size == 1 && ordinaryEvents == auditedEvents do
      throwError "explicit export changed the fixed computation's outcome or actual dispatch"
    unless (ordinaryEvents[0]!.getObjValAs? String "operation").toOption ==
        some "meth.cardinality" do
      throwError "dispatch agreement did not exercise the existing cardinality operation"
    let (directHarness, directCalls) ← observedHarness base
    let (askingHarness, askingCalls) ← observedHarness base
    let (direct, _) ← withCurrHeartbeats <| run directHarness {} parsed
    let (asking, _, identity) ← withCurrHeartbeats <| runAsking askingHarness {} parsed
    unless direct.kind == ordinary.toOutcome.kind && asking.kind == direct.kind &&
        identity == some exported.identity &&
        (← directCalls.get) == ordinaryEvents && (← askingCalls.get) == ordinaryEvents do
      throwError "ordinary and audit entry points changed the selected dispatch or complete identity"

    -- Remove one original producer reference, without changing the assertion,
    -- its terms or any expected value. Both public evaluation boundaries must
    -- reject this damaged retained request before the real fixture is called.
    let .literal producer .. := prepared.claim
      | throwError "the fixed cardinality question lost its selected literal relation"
    let some (.method selected ..) := prepared.trace[producer]?
      | throwError "the fixed question lost its original method producer"
    unless selected.raw == "meth.cardinality" && (Trace.producerAnchor? producer).isSome do
      throwError "the missing-reference control did not select the original cardinality producer"
    let broken : PreparedQuestion := { prepared with trace := prepared.trace.erase producer }
    let brokenExported := { exported with trace := broken.trace }
    let (brokenHarness, brokenCalls) ← observedHarness base
    let ordinaryFailure ← withCurrHeartbeats <|
      tryCatchRuntimeEx (evaluatePrepared brokenHarness broken) executionFailure
    undispatched brokenHarness brokenCalls
    unless ordinaryFailure.toOutcome.kind == "internal" do
      throwError "ordinary execution did not reject the missing producer as an internal defect"
    let (brokenAuditHarness, brokenAuditCalls) ← observedHarness base
    let auditedFailure ← withCurrHeartbeats <|
      tryCatchRuntimeEx (evaluate brokenAuditHarness brokenExported) executionFailure
    undispatched brokenAuditHarness brokenAuditCalls
    unless auditedFailure.toOutcome.kind == "internal" do
      throwError "exported execution did not reject the missing producer as an internal defect"
    let exportFailure : Except Outcome TypedQuestion ← withCurrHeartbeats <|
      tryCatchRuntimeEx (Except.ok <$> exportQuestion broken)
        fun error => return .error (← Outcome.ofException error)
    let .error failure := exportFailure
      | throwError "explicit export accepted the missing original producer"
    unless failure.kind == "internal" do
      throwError "a missing producer became mathematical invalidity or a computational gap"
    withCurrHeartbeats <| sameRequest prepared exported
  finally
    base.stop

-- A manifest-read failure belongs to explicitly requested export. The existing
-- arithmetic question remains prepared and executable with export omitted.
-- Changing this process's directory touches no repository manifest; restoration
-- and temporary-directory removal run even if a control fails.
run_cmd withoutModifyingEnv <| liftTermElabM <| withoutErrToSorry do
  let parsed ← statement "assert 2 + 3 = 6"
  let prepared ← withCurrHeartbeats <| prepare {} parsed
  let exported ← withCurrHeartbeats <| exportQuestion prepared
  let harness ← Harness.empty
  let calls ← IO.mkRef (#[] : Array Json)
  let harness := { harness with dispatches := some calls }
  let originalDirectory ← IO.Process.getCurrentDir
  IO.FS.withTempDir fun temporary => do
    try
      IO.Process.setCurrentDir temporary
      let exportFailure : Except Outcome TypedQuestion ← withCurrHeartbeats <|
        tryCatchRuntimeEx (Except.ok <$> exportQuestion prepared)
          fun error => return .error (← Outcome.ofException error)
      let .error failure := exportFailure
        | throwError "the absent export manifest produced a successful audit identity"
      unless failure.kind == "internal" && !failure.detail.isEmpty do
        throwError "an explicit export failure lost its phase failure or became mathematical invalidity"
      let (ordinary, _) ← withCurrHeartbeats <| run harness {} parsed
      let retained ← withCurrHeartbeats <| evaluatePrepared harness prepared
      unless ordinary.kind == "wrong" && retained.toOutcome.kind == ordinary.kind do
        throwError "ordinary preparation or execution required the unused audit manifest"
      let (asking, _, identity) ← withCurrHeartbeats <| runAsking harness {} parsed
      unless asking.kind == "internal" && identity.isNone do
        throwError "failed requested export became a successful empty question"
      undispatched harness calls
      withCurrHeartbeats <| sameRequest prepared exported
    finally
      IO.Process.setCurrentDir originalDirectory
  let afterFailure ← withCurrHeartbeats <| exportQuestion prepared
  unless afterFailure.identity == exported.identity do
    throwError "failed export changed the retained question or later complete export"

end
end CasCatalogue.PreparedQuestionProbes
