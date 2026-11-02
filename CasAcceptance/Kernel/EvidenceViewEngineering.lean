module

import CasCatalogue.Language
import Lean.PrettyPrinter.Basic
import Lean.Meta.Tactic.AuxLemma
meta import CasCatalogue.Language
meta import Lean.PrettyPrinter.Basic
meta import Lean.Meta.Tactic.AuxLemma

open Lean Meta Elab Term Tactic CasCatalogue CasCatalogue.Language

/- Engineering fixtures for equivalent goal presentations and procedure isolation.
They register no mathematical object or operation and use only reflexivity. -/
namespace CasAcceptance.Kernel.EvidenceViewEngineering

private def fixtureType (α : Type) : Type := α

meta section

private def target : Expr :=
  mkApp3 (Lean.mkConst ``Eq [Level.one])
    (mkApp (Lean.mkConst ``fixtureType) (Lean.mkConst ``Nat))
    (Lean.mkNatLit 0) (Lean.mkNatLit 0)

private def stateSentinel : Name := `EvidenceViewEngineering.stateSentinel
private def budgetSentinel : Name := `EvidenceViewEngineering.budgetSentinel
private def transientTag : Name := `EvidenceViewEngineering.transient

private def sentinel (name : Name) : TacticM MVarId := do
  let some id := (← getMCtx).findUserName? name
    | throwError "the evidence fixture lost its caller's sentinel"
  return id

private def closeReflexivity : TacticM Unit := do
  let goal ← getMainGoal
  let type ← getMainTarget
  unless type.isAppOfArity ``Eq 3 do
    throwError "the fixture changed its equality obligation"
  goal.assign (← mkEqRefl type.getAppArgs[1]!)
  replaceMainGoal []

private def nominalOnly : TacticM Unit := do
  unless (← getMainTarget).getAppArgs[0]!.isAppOf ``fixtureType do
    throwError "the original named type was erased before invoking its provider"
  closeReflexivity

private def exposedOnly : TacticM Unit := do
  let budget ← sentinel budgetSentinel
  let expected := (← budget.getDecl).type.getAppArgs[1]!
  unless expected == Lean.mkNatLit (← getInitHeartbeats) do
    throwError "an evidence view reset the enclosing heartbeat allowance"
  let state ← sentinel stateSentinel
  unless !(← state.isAssigned) do
    throwError "a rejected presentation changed the next attempt's proof state"
  -- The successful attempt must also export only its result term, not this assignment.
  state.assign (Lean.mkConst ``True.intro)
  logInfo (MessageData.tagged transientTag "an isolated procedure diagnostic")
  if (← getMainTarget).getAppArgs[0]!.isAppOf ``fixtureType then
    throwError "ordinary rejection of the nominal presentation"
  closeReflexivity

private def loggedFailure : TacticM Unit := do
  if (← getMainTarget).getAppArgs[0]!.isAppOf ``fixtureType then
    logError "malformed procedure diagnostic fixture"
  closeReflexivity

private def incompleteResult : TacticM Unit := do
  if (← getMainTarget).getAppArgs[0]!.isAppOf ``fixtureType then return
  closeReflexivity

private def incorrectResult : TacticM Unit := do
  if (← getMainTarget).getAppArgs[0]!.isAppOf ``fixtureType then
    (← getMainGoal).assign (← mkEqRefl (Lean.mkNatLit 1))
    replaceMainGoal []
  else closeReflexivity

private def internalFailure : TacticM Unit := do
  if (← getMainTarget).getAppArgs[0]!.isAppOf ``fixtureType then
    throw (Exception.internal Lean.PrettyPrinter.backtrackExceptionId
      (({} : KVMap).setNat `sentinel 83))
  closeReflexivity

private def auxiliarySuccess : TacticM Unit := do
  let goal ← getMainGoal
  let type ← getMainTarget
  let proof ← mkEqRefl type.getAppArgs[1]!
  let name ← mkAuxLemma [] type proof (some `evidenceView) (cache := false)
  goal.assign (Lean.mkConst name)
  replaceMainGoal []

private def rejectedAuxiliary : Name := `EvidenceViewEngineering.rejectedAuxiliary

private def auxiliaryRejection : TacticM Unit := do
  unless !(← getEnv).contains rejectedAuxiliary do
    throwError "a rejected presentation published its auxiliary declaration"
  if (← getMainTarget).getAppArgs[0]!.isAppOf ``fixtureType then
    let type ← getMainTarget
    addDecl (.thmDecl {
      name := rejectedAuxiliary, levelParams := [], type,
      value := ← mkEqRefl type.getAppArgs[1]! })
    throwError "ordinary rejection after adding an auxiliary declaration"
  closeReflexivity

private def auxiliaryHole : TacticM Unit := do
  let goal ← getMainGoal
  let type ← getMainTarget
  let name ← mkAuxLemma [] type (← mkSorry type false)
    (some `evidenceViewHole) (cache := false)
  goal.assign (Lean.mkConst name)
  replaceMainGoal []

private def unsuppliedAssumption : Name := `EvidenceViewEngineering.unsuppliedAssumption

private def auxiliaryAssumption : TacticM Unit := do
  let goal ← getMainGoal
  let type ← getMainTarget
  addDecl (.axiomDecl {
    name := unsuppliedAssumption, levelParams := [], type, isUnsafe := false })
  goal.assign (Lean.mkConst unsuppliedAssumption)
  replaceMainGoal []

private def checkOriginal (term : Expr) : TermElabM Unit := do
  unless !term.hasMVar && !term.hasLevelMVar && !term.hasSorry &&
      (← isTypeCorrect term) &&
      (← withTransparency .all <| isDefEq (← inferType term) target) do
    throwError "the evidence did not inhabit its complete original target"

run_elab do
  let state ← registryState
  let fields ← evidencePresentation state target
  unless fields == target do
    throwError "stored-field presentation erased an ordinary named mathematical type"
  let types ← closedTypePresentation fields
  unless types != target && (← isTypeCorrect types) &&
      (← withTransparency .all <| isDefEq types target) do
    throwError "the explicit type-visibility view lost the original obligation"
  checkOriginal (← establish ``nominalOnly target "nominal-first engineering control")
  let witness ← mkFreshExprMVar (Lean.mkConst ``True) .syntheticOpaque stateSentinel
  let budget := Lean.mkNatLit (← getInitHeartbeats)
  discard <| mkFreshExprMVar (← mkEq budget budget) .syntheticOpaque budgetSentinel
  let messages := (← getThe Core.State).messages
  let proof ← establish ``exposedOnly target "isolated type-visibility engineering control"
  checkOriginal proof
  unless !(← witness.mvarId!.isAssigned) do
    throwError "an evidence result published assignments outside its proof scope"
  let current := (← getThe Core.State).messages
  unless current.reported.size == messages.reported.size &&
      current.unreported.size == messages.unreported.size &&
      !current.reportedPlusUnreported.any (fun message =>
        message.data.hasTag (· == transientTag)) do
    throwError "an evidence presentation published its transient messages"

run_elab do
  let baseline ← getEnv
  let proof ← establish ``auxiliarySuccess target "auxiliary declaration success control"
  checkOriginal proof
  let some auxiliary := proof.find? (fun term => match term with
    | .const name _ => !baseline.contains name
    | _ => false)
    | throwError "the successful auxiliary declaration was not retained in its result"
  unless (← getEnv).contains auxiliary.constName! do
    throwError "the returned evidence lost its successful auxiliary declaration"
  checkOriginal (← establish ``auxiliaryRejection target "rejected auxiliary isolation control")
  unless !(← getEnv).contains rejectedAuxiliary do
    throwError "a rejected provider attempt exported an auxiliary declaration"

run_elab do
  for procedure in #[``loggedFailure, ``incompleteResult, ``incorrectResult,
      ``auxiliaryHole, ``auxiliaryAssumption] do
    let failure ← try
      discard <| establish procedure target "malformed evidence engineering control"
      pure none
    catch error => pure (some error)
    let some failure := failure
      | throwError "a malformed result was hidden by another evidence presentation"
    unless Exception.stratum? failure == some .invalid &&
        !Exception.hasConflictingStrata failure do
      throwError "a malformed evidence result lost its original failure classification"
  unless !(← getEnv).contains unsuppliedAssumption do
    throwError "rejected evidence exported an unprovided assumption"
  let failure ← try
    discard <| establish ``internalFailure target "internal evidence engineering control"
    pure none
  catch error => pure (some error)
  let some (.internal id payload) := failure
    | throwError "an internal failure was hidden by another evidence presentation"
  unless id == Lean.PrettyPrinter.backtrackExceptionId && payload.getNat `sentinel == 83 do
    throwError "the evidence presentation changed an internal failure's identity"

run_elab do
  let messages := (← getThe Core.State).messages
  try
    logError "a pre-existing caller diagnostic"
    let goal ← mkFreshExprMVar target .syntheticOpaque
    let .error (.malformed _) ← runProcedure ``loggedFailure goal.mvarId!
      | throwError "a new malformed result was hidden by the caller's existing error"
  finally
    modifyThe Core.State fun state => { state with messages }

end
end CasAcceptance.Kernel.EvidenceViewEngineering
