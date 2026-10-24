module

import CasCatalogue.Language
import Lean.PrettyPrinter.Basic
meta import CasCatalogue.Language
meta import Lean.PrettyPrinter.Basic

open Lean Meta Elab Term Tactic CasCatalogue CasCatalogue.Language

/- Exception-only engineering fixtures for the generic runner. They construct no
proof, supply no mathematical procedure or answer, and register no semantic row. -/
namespace CasAcceptance.Kernel.EvidenceProcedureFailureProbes

meta section

-- This imported identifier is already initialized. Core's ordinary catch handles
-- it, and Tactic.run recognizes only abortTacticExceptionId as a tactic abort.
private def fixtureExceptionId : InternalExceptionId :=
  Lean.PrettyPrinter.backtrackExceptionId

private def transientTag : Name := `EvidenceProcedureFailureProbes.transient
private def baselineTag : Name := `EvidenceProcedureFailureProbes.baseline
private def payloadTag : Name := `EvidenceProcedureFailureProbes.payload
private def failureRef : Syntax := mkIdent `evidenceProcedureFailureOrigin

private def prepareFailure : TacticM Unit := do
  logInfo (MessageData.tagged transientTag "a transient procedure diagnostic")

private def ordinaryRejection : TacticM Unit := do
  prepareFailure
  throwError "the ordinary evidence attempt rejected its obligation"

private def internalFailure : TacticM Unit := do
  prepareFailure
  throw (Exception.internal fixtureExceptionId (({} : KVMap).setNat `sentinel 47))

private def taggedFailure (stratum : Stratum) : Exception :=
  .error failureRef (.tagged stratum.tag (.tagged payloadTag "original failure payload"))

private def invalidRejection : TacticM Unit := do
  prepareFailure
  throw (taggedFailure .invalid)

private def wrongStageFailure : TacticM Unit := do
  prepareFailure
  throw (taggedFailure .unavailable)

private def conflictingFailure : TacticM Unit := do
  prepareFailure
  throw (Exception.error failureRef (.tagged Stratum.invalid.tag
    (taggedFailure .unavailable).toMessageData))

private def legacyAmbiguity : TacticM Unit := do
  prepareFailure
  throw (Exception.error failureRef (.tagged `CasCatalogue.throwSemanticAmbiguity
    (.tagged payloadTag "original ambiguity payload")))

run_elab do
  let originalMessages := (← getThe Core.State).messages
  try
    logInfo (MessageData.tagged baselineTag "an existing caller diagnostic")
    let baseline := (← getThe Core.State).messages
    let checkMessages : TermElabM Unit := do
      let messages := (← getThe Core.State).messages
      unless messages.reported.size == baseline.reported.size &&
          messages.unreported.size == baseline.unreported.size &&
          messages.toList.any (fun message => message.data.hasTag (· == baselineTag)) &&
          !messages.toList.any (fun message => message.data.hasTag (· == transientTag)) do
        throwError "the evidence runner did not restore its caller's message state"

    let goal ← mkFreshExprMVar (mkConst ``True) .syntheticOpaque
    let .error _ ← runProcedure ``ordinaryRejection goal.mvarId!
      | throwError "an ordinary proof rejection was not returned to the caller"
    checkMessages
    let ordinary ← try
      discard <| establish ``ordinaryRejection (mkConst ``True) "ordinary rejection control"
      pure none
    catch error => pure (some error)
    let some ordinary := ordinary
      | throwError "ordinary evidence rejection unexpectedly established its obligation"
    unless Exception.stratum? ordinary == some .invalid &&
        !Exception.hasConflictingStrata ordinary do
      throwError "ordinary evidence rejection lost its invalid interpretation kind"
    checkMessages

    let checkFailure (procedure : Name) (expected : Exception → Bool) : TermElabM Unit := do
      for throughEstablish in #[false, true] do
        let failure ← try
          if throughEstablish then
            discard <| establish procedure (mkConst ``True) "failure identity control"
          else
            let goal ← mkFreshExprMVar (mkConst ``True) .syntheticOpaque
            discard <| runProcedure procedure goal.mvarId!
          pure none
        catch error => pure (some error)
        checkMessages
        let some failure := failure
          | throwError "the evidence runner converted an existing failure into ordinary rejection"
        unless expected failure do
          throwError "the evidence runner changed an existing exception, payload or failure stage"

    checkFailure ``internalFailure fun
      | .internal id extra => id == fixtureExceptionId && extra.size == 1 &&
          extra.getNat `sentinel == 47
      | _ => false
    for (procedure, stratum) in #[(``invalidRejection, Stratum.invalid),
        (``wrongStageFailure, Stratum.unavailable)] do
      checkFailure procedure fun error => match error with
        | .error ref message => ref == failureRef && message.hasTag (· == payloadTag) &&
            Exception.stratum? error == some stratum && !Exception.hasConflictingStrata error
        | _ => false
    checkFailure ``conflictingFailure fun error => match error with
      | .error ref message => ref == failureRef && message.hasTag (· == payloadTag) &&
          message.hasTag (· == Stratum.invalid.tag) &&
          message.hasTag (· == Stratum.unavailable.tag) &&
          Exception.hasConflictingStrata error && Exception.interpretationKind error == .internal
      | _ => false
    checkFailure ``legacyAmbiguity fun error => match error with
      | .error ref message => ref == failureRef && message.hasTag (· == payloadTag) &&
          (Exception.stratum? error).isNone && Exception.isSemanticAmbiguity error
      | _ => false
  finally
    modifyThe Core.State fun state => { state with messages := originalMessages }

end
end CasAcceptance.Kernel.EvidenceProcedureFailureProbes
