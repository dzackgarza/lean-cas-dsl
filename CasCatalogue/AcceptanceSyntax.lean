/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Acceptance
public meta import CasCatalogue.Acceptance
public meta import CasCatalogue.Failure
public meta import CasCatalogue.Port

public section

/-! # Syntax of permanent acceptance assertions (`CasCatalogue.Acceptance`) -/

open Lean Elab Command Term Meta

namespace CasCatalogue

open Acceptance

syntax (name := acceptCommand)
  "#accept " str " from " str (&" realized")? " : " term " := " term : command

syntax (name := acceptBackendCommand)
  "#accept_backend " str " from " str " : " "(" term ")" &" agrees " term : command

syntax (name := acceptanceGapsCommand) "#acceptance_gaps" : command

/-- Check an `#accept` command: its status, admitting it as a theorem when `admit`. -/
meta def checkAccept (stx : Syntax) (admit : Bool) : CommandElabM Status := do
  let some id := stx[1].isStrLit? | throwUnsupportedSyntax
  let realized := !stx[4].isNone
  liftTermElabM do
    try
      let type ← withoutErrToSorry <| elabType stx[6]
      synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      let proof ← withoutErrToSorry <| elabTermEnsuringType stx[8] type
      synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      if type.hasSorry || proof.hasSorry || type.hasMVar || proof.hasMVar then
        throwError "the assertion {id} is not closed"
      if admit then
        addDecl <| .thmDecl
          { name := theoremName id, levelParams := [], type, value := proof }
      pure Status.holds
    catch e =>
      match Exception.stratum? e with
      | some .noImplementation | some .ambiguousRealization =>
          if realized then throw e
          pure (.gap (← e.toMessageData.toString))
      | some .unavailable => pure (.unavailable (← e.toMessageData.toString))
      | _ => throw e

/-- Check an `#accept_backend` command. -/
meta def checkAcceptBackend (stx : Syntax) : CommandElabM Status := do
  let some id := stx[1].isStrLit? | throwUnsupportedSyntax
  let some source := stx[3].isStrLit? | throwUnsupportedSyntax
  liftTermElabM do
    let call ← withoutErrToSorry <| elabTerm stx[6] none
    synthesizeSyntheticMVarsNoPostponing
    let value ← withoutErrToSorry <| elabTerm stx[9] none
    synthesizeSyntheticMVarsNoPostponing
    let outcome ← mkAppM ``backendOutcome #[← instantiateMVars call, ← instantiateMVars value]
    let run ← evalBackendOutcome outcome
    match ← (run (← registryState) : IO BackendOutcome) with
    | .agrees => pure Status.holds
    | .disagrees got expected =>
        throwError "wrong answer to acceptance {id}: the realization answered {got}, the \
          assertion is {expected} ({source})"
    | .failed e =>
        match e.stratum with
        | .unavailable => pure (.unavailable e.render)
        | s => throwStratum s m!"acceptance {id}: {e.render}"

/-- The record of an assertion elaborated here. -/
meta def recordOf (stx : Syntax) (status : Status) : CommandElabM Record := do
  let some id := stx[1].isStrLit? | throwUnsupportedSyntax
  let some source := stx[3].isStrLit? | throwUnsupportedSyntax
  return { id, source, status, command := stx, «namespace» := ← getCurrNamespace
           openDecls := ← getOpenDecls }

@[command_elab acceptCommand] meta def elabAccept : CommandElab := fun stx => do
  let status ← checkAccept stx (admit := true)
  let record ← recordOf stx status
  let id := record.id
  addRecord record
  match status with
  | .holds => pure ()
  | .gap reason => logInfo m!"acceptance gap {id}: {reason}"
  | .unavailable reason => logInfo m!"acceptance {id} not exercised: {reason}"

@[command_elab acceptBackendCommand] meta def elabAcceptBackend : CommandElab := fun stx => do
  let status ← checkAcceptBackend stx
  let record ← recordOf stx status
  addRecord record
  if let .unavailable reason := status then
    logInfo m!"acceptance {record.id} not exercised: {reason}"

/-- `#acceptance_rerun`, optionally `expecting "id"…`: the listed assertions must hold here. -/
syntax (name := acceptanceRerunCommand) "#acceptance_rerun" (&" expecting" (ppSpace str)+)? : command

/-- Rerun every admitted assertion of the imported modules here, in the namespace and `open`s it
was written in. A wrong or malformed answer fails; the statuses are reported. -/
@[command_elab acceptanceRerunCommand] meta def elabAcceptanceRerun : CommandElab := fun stx => do
  let expected : Array String := if stx[1].isNone then #[]
    else stx[1][1].getArgs.filterMap (·.isStrLit?)
  let mut holding : Array String := #[]
  let mut passing : Nat := 0
  let mut lines : Array String := #[]
  for record in records (← getEnv) do
    let rerun : CommandElabM Status := withoutModifyingEnv do
      -- The scoped notations of the namespaces the assertion was written in, and of its opens.
      let mut namespaces := record.namespace.components.foldl
        (fun acc c => acc.push (acc.back?.getD .anonymous ++ c)) #[]
      for decl in record.openDecls do
        if let .simple ns _ := decl then namespaces := namespaces.push ns
      for ns in namespaces do activateScoped ns
      withScope (fun scope => { scope with currNamespace := record.namespace
                                           openDecls := record.openDecls }) do
        if record.command.getKind == ``acceptCommand then checkAccept record.command false
        else checkAcceptBackend record.command
    let status ← try rerun catch e =>
      throwError "acceptance {record.id} ({record.source}) fails here: {e.toMessageData}"
    if status matches .holds then holding := holding.push record.id
    match record.status, status with
    | .holds, .holds => passing := passing + 1
    | _, .holds =>
        passing := passing + 1
        lines := lines.push s!"  {record.id}: now holds"
    | _, .gap reason => lines := lines.push s!"  {record.id}: gap: {reason}"
    | _, .unavailable reason => lines := lines.push s!"  {record.id}: not exercised: {reason}"
  for id in expected do
    unless holding.contains id do
      throwError "acceptance {id} does not hold here"
  logInfo m!"acceptance rerun: {passing} of {(records (← getEnv)).size} hold\n{"\n".intercalate lines.toList}"

@[command_elab acceptanceGapsCommand] meta def elabAcceptanceGaps : CommandElab := fun _ => do
  let lines := (records (← getEnv)).toList.filterMap fun r => match r.status with
    | .gap reason => some s!"  {r.id} ({r.source}): {reason}"
    | .unavailable reason => some s!"  {r.id} ({r.source}): not exercised: {reason}"
    | .holds => none
  logInfo m!"acceptance assertions no realization computes here:\n{"\n".intercalate lines}"

end CasCatalogue
