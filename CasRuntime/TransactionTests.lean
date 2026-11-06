module

import CasRuntime.Transaction
public meta import Lean.Elab.Command
meta import CasRuntime.Transaction

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let role ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let parent ← getEnv
    let transaction ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) ledger.allocate
    let value ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role } (.portable "cell payload".toUTF8)
    liftM (m := IO) <| transaction.emit (.str "cell output")
    let staged ← liftM (m := IO) transaction.view
    unless (staged.find value.value).isSome do
      throwError "a later cell expression cannot see its staged value"
    if ((← SessionSnapshot.current).graph.find value.value).isSome then
      throwError "an Environment query exposed a staged value"
    let .ok published ← transaction.commit
      | throwError "the cell could not publish its complete delta"
    unless (published.graph.find value.value).isSome &&
        published.outputBatches.size == 1 do
      throwError "commit did not publish values and output together"
    let some batch := published.outputBatches[0]?
      | throwError "the committed output batch is missing"
    unless batch.transaction == transaction.id && batch.events == #[.str "cell output"] do
      throwError "commit changed the staged output or its transaction association"
    match ← transaction.commit with
    | .error .settled => pure ()
    | _ => throwError "a settled cell committed again"
    if ← liftM (m := BaseIO) transaction.abort then
      throwError "abort replaced a successful commit"
    let aborted ← CellTransaction.begin ledger
    let pending ← liftM (m := BaseIO) ledger.allocate
    let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
    try
      let selected : DispatchIdentity := {
        manifestDigest := "resource-test-manifest"
        registration := { operation := "resource-test", input := "resource-test", backend := "cat" }
        profileDigest := "resource-test-profile" }
      let .ok _ ← liftM (m := BaseIO) <| aborted.reserve pending selected child #[]
        | throwError "the transaction could not reserve its invocation"
      let discarded ← liftM (m := IO) <| aborted.stage
        { program, occurrence := pending, role } (.portable "discarded payload".toUTF8)
      liftM (m := IO) <| aborted.emit (.str "discarded output")
      match ← aborted.commit with
      | .error .pendingCalls => pure ()
      | _ => throwError "an in-flight call allowed whole-cell publication"
      unless ← liftM (m := BaseIO) aborted.abort do
        throwError "the active transaction could not abort"
      let current ← SessionSnapshot.current
      if (current.graph.find discarded.value).isSome then
        throwError "an aborted value became visible in the Environment"
      unless current.outputBatches.size == published.outputBatches.size do
        throwError "abort published a staged output batch"
      let unpublished ← liftM (m := IO) do
        try
          discard <| aborted.view
          pure false
        catch _ => pure true
      unless unpublished do throwError "the settled transaction retained a staged graph"
      setEnv parent
      let other ← CellTransaction.begin ledger
      match ← liftM (m := BaseIO) <| other.reserve pending selected child #[] with
      | .error (.reservation .consumed) => pure ()
      | _ => throwError "restoring an old Environment replenished a dispatch right"
      discard <| liftM (m := BaseIO) other.abort
      if ((← SessionSnapshot.current).graph.find value.value).isSome then
        throwError "an old Environment recovered a newer committed payload"
    finally liftM (m := IO) <| owners.close child.generation
  finally setEnv original

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let role ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let first ← CellTransaction.begin ledger
    let second ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let firstOccurrence ← liftM (m := BaseIO) ledger.allocate
    let firstValue ← liftM (m := IO) <| first.stage
      { program, occurrence := firstOccurrence, role } (.portable "first cell".toUTF8)
    let secondOccurrence ← liftM (m := BaseIO) ledger.allocate
    let secondValue ← liftM (m := IO) <| second.stage
      { program, occurrence := secondOccurrence, role } (.portable "second cell".toUTF8)
    let .ok _ ← first.commit | throwError "the first cell could not commit"
    match ← second.commit with
    | .error .staleSnapshot => pure ()
    | _ => throwError "a stale cell replaced a newer committed snapshot"
    discard <| liftM (m := BaseIO) second.abort
    let visible ← SessionSnapshot.current
    unless (visible.graph.find firstValue.value).isSome &&
        (visible.graph.find secondValue.value).isNone do
      throwError "stale publication changed the visible value graph"
    let owned ← CellTransaction.begin ledger
    let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
    try
      let token ← liftM (m := IO) do
        child.child.stdin.putStr "owned token\n"
        child.child.stdin.flush
        return (← child.child.stdout.getLine).trimAscii.toString
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let value ← liftM (m := IO) <| owned.stage
        { program, occurrence, role } (.ownedExport child token #[])
      liftM (m := IO) <| owners.close child.generation
      match ← owned.commit with
      | .error .staleOwner => pure ()
      | _ => throwError "commit accepted a known-dead result owner"
      if ((← SessionSnapshot.current).graph.find value.value).isSome then
        throwError "owner loss published a staged result"
      let cleared ← liftM (m := IO) do
        try
          discard <| owned.view
          pure false
        catch _ => pure true
      unless cleared do throwError "owner-loss settlement retained a staged graph"
    finally liftM (m := IO) <| owners.close child.generation
  finally setEnv original
