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

@[command_elab acceptCommand] meta def elabAccept : CommandElab := fun stx => do
  let some id := stx[1].isStrLit? | throwUnsupportedSyntax
  let some source := stx[3].isStrLit? | throwUnsupportedSyntax
  let realized := !stx[4].isNone
  let status ← liftTermElabM do
    try
      let type ← withoutErrToSorry <| elabType stx[6]
      synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      let proof ← withoutErrToSorry <| elabTermEnsuringType stx[8] type
      synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      if type.hasSorry || proof.hasSorry || type.hasMVar || proof.hasMVar then
        throwError "the assertion {id} is not closed"
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
  addRecord { id, source, status }
  match status with
  | .holds => pure ()
  | .gap reason => logInfo m!"acceptance gap {id}: {reason}"
  | .unavailable reason => logInfo m!"acceptance {id} not exercised: {reason}"

@[command_elab acceptBackendCommand] meta def elabAcceptBackend : CommandElab := fun stx => do
  let some id := stx[1].isStrLit? | throwUnsupportedSyntax
  let some source := stx[3].isStrLit? | throwUnsupportedSyntax
  let status ← liftTermElabM do
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
  addRecord { id, source, status }
  if let .unavailable reason := status then
    logInfo m!"acceptance {id} not exercised: {reason}"

@[command_elab acceptanceGapsCommand] meta def elabAcceptanceGaps : CommandElab := fun _ => do
  let lines := (records (← getEnv)).toList.filterMap fun r => match r.status with
    | .gap reason => some s!"  {r.id} ({r.source}): {reason}"
    | .unavailable reason => some s!"  {r.id} ({r.source}): not exercised: {reason}"
    | .holds => none
  logInfo m!"acceptance assertions no realization computes here:\n{"\n".intercalate lines}"

end CasCatalogue
