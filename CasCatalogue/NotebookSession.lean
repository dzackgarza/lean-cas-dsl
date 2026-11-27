/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import CasCatalogue.TestSuite
import CasRuntime.ExecutionContext
import CasRuntime.Inspect
import Worker.Cell
meta import CasCatalogue.TestSuite
meta import CasRuntime.ExecutionContext
meta import CasRuntime.Inspect
meta import Worker.Cell

namespace CasCatalogue.NotebookSession

open Lean Elab Command CasRuntime CasCompiler

meta section

private def identity {kind : IdentityKind} (id : RuntimeId kind) : String :=
  s!"{id.worker}:{id.serial}"

private def startup : CommandElabM (Worker.Cell.Profile × String) := do
  let session ← liftTermElabM <| KernelSession.start
  liftCoreM (KernelSession.install session)
  let profile := session.kernel.profile
  return (⟨profile.id, profile.sha256⟩, session.kernel.ledger.owners.worker)

private def beginCell : CommandElabM Worker.Cell.Active := do
  let some parent ← liftCoreM KernelSession.current?
    | throwError "the notebook has no initialized CAS session"
  -- The parent is a committed Environment. Copy its retained closure/code
  -- tables before any staging; the connection/occurrence supervisor is shared.
  let session ← parent.fork
  liftCoreM (KernelSession.install session)
  let transaction ← liftCoreM (CellTransaction.begin session.kernel.ledger)
  liftCoreM (KernelSession.setActive (some transaction))
  return {
    prepare := fun outputs => do
      let some session ← liftCoreM KernelSession.current?
        | throwError "the candidate lost its CAS source session"
      let descriptors ← liftTermElabM (CasRuntime.Inspect.prepare session transaction)
      liftCoreM (Worker.Cell.setObservations (descriptors.map fun d => {
        name := d.name
        type := d.type
        details := d.details
        members := d.members }))
      for output in outputs do transaction.emit output.toJson
    commit := do
      let snapshot ← try
          liftTermElabM do
            match ← transaction.commit with
            | .ok snapshot => pure snapshot
            | .error failure => transactionFailure failure
        catch error =>
          let outcome ← liftTermElabM (Outcome.ofException error)
          if let some stratum := outcome.stratum? then
            Worker.Cell.reportFailure { stratum := some stratum, reason := outcome.detail }
          throw error
      let some batch := snapshot.outputBatches.back?
        | throwError "the committed notebook cell has no output batch"
      liftCoreM (KernelSession.setActive none)
      return ⟨identity batch.transaction, identity batch.id,
        (batch.roots.map identity).toList.eraseDups.toArray⟩
    cancel := do discard <| (transaction.abort : BaseIO Bool)
    force := do
      return (← transaction.force).map fun owner => s!"{owner.worker}:{owner.serial}"
    draining := transaction.draining
  }

private def closeSession : CommandElabM Unit := do
  if let some session ← liftCoreM KernelSession.current? then
    session.close

initialize Worker.Cell.register {
  startup := startup, begin := beginCell, close := closeSession }

end

end CasCatalogue.NotebookSession
