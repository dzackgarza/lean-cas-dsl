module

import CasRuntime.Occurrence
public meta import Lean.Elab.Command
meta import CasRuntime.Occurrence

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let role ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
  liftM (m := IO) do
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    let graph := ValueGraph.empty owners.identities
    let first ← ledger.allocate
    let firstTransaction ← owners.identities.fresh .transaction
    let secondTransaction ← owners.identities.fresh .transaction
    let child ← owners.spawn { cmd := "/bin/cat" }
    try
      let choice : DispatchIdentity := {
        manifestDigest := "resource-test-manifest"
        registration := { operation := "resource-test", input := "resource-test", backend := "cat" }
        profileDigest := "resource-test-profile" }
      let tasks ← (Array.range 32).mapM fun index => IO.asTask do
        let transaction := if index % 2 == 0 then firstTransaction else secondTransaction
        ledger.reserve first transaction choice child graph #[]
      let results ← tasks.mapM fun task => IO.ofExcept task.get
      let winners := results.filterMap (·.toOption)
      unless winners.size == 1 do
        throw <| IO.userError "an occurrence reservation did not have exactly one winner"
      let some winner := winners[0]?
        | throw <| IO.userError "the successful reservation is missing"
      unless decide (winner.selected = choice) && winner.connection == child.generation do
        throw <| IO.userError "reservation changed the selected realization or connection"
      unless (← ledger.pendingFor first winner.transaction).isSome do
        throw <| IO.userError "the owning transaction lost its pending occurrence"
      let unrelated ← owners.identities.fresh .transaction
      if (← ledger.pendingFor first unrelated).isSome then
        throw <| IO.userError "another transaction acquired the pending occurrence"
      unless ← ledger.retire winner do
        throw <| IO.userError "the pending occurrence did not retire"
      if (← ledger.pendingFor first winner.transaction).isSome then
        throw <| IO.userError "a consumed occurrence remains pending"
      match ← ledger.reserve first unrelated choice child graph #[] with
      | .error .consumed => pure ()
      | _ => throw <| IO.userError "a consumed occurrence acquired another dispatch right"
      let second ← ledger.allocate
      unless second.serial > first.serial do
        throw <| IO.userError "a new invocation reused an occurrence identity"
      let captureOwner ← owners.spawn { cmd := "/bin/cat" }
      try
        captureOwner.child.stdin.putStr "captured token\n"
        captureOwner.child.stdin.flush
        let token := (← captureOwner.child.stdout.getLine).trimAscii.toString
        let program ← owners.identities.fresh .program
        let (capturedGraph, captured) ← graph.stage owners.identities
          { program, occurrence := second, role } (.ownedExport captureOwner token #[])
        owners.close captureOwner.generation
        match ← ledger.reserve second unrelated choice child capturedGraph #[captured] with
        | .error .staleOwner => pure ()
        | _ => throw <| IO.userError "reservation accepted a known-dead captured owner"
        unless ← owners.isLive child.generation do
          throw <| IO.userError "capture invalidation closed the supplying connection"
      finally owners.close captureOwner.generation
      owners.close child.generation
      let third ← ledger.allocate
      match ← ledger.reserve third unrelated choice child graph #[] with
      | .error .staleOwner => pure ()
      | _ => throw <| IO.userError "reservation accepted a known-dead supplying connection"
    finally owners.close child.generation
