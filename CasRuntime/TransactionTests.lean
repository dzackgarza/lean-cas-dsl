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
    let transaction ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) ledger.allocate
    let origin : ValueOrigin := { program, occurrence, role }
    let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
    try
      let token ← liftM (m := IO) do
        child.child.stdin.putStr "joint reply resource\n"
        child.child.stdin.flush
        return (← child.child.stdout.getLine).trimAscii.toString
      let draft ← liftM (m := IO) transaction.draft
      let (draft, portable) ← liftM (m := IO) <|
        draft.stage origin (.portable "joint portable field".toUTF8)
      let (draft, native) ← liftM (m := IO) <|
        draft.stage origin (.ownedExport child token #[portable])
      let current ← liftM (m := IO) transaction.view
      unless (current.find portable.value).isNone && (current.find native.value).isNone do
        throwError "an isolated reply draft exposed a prefix to the active transaction"
      liftM (m := IO) <| owners.close child.generation
      match ← liftM (m := BaseIO) (transaction.installDraft draft) with
      | .error .staleOwner => pure ()
      | _ => throwError "a joint reply installed a field whose required owner had died"
      let unchanged ← liftM (m := IO) transaction.view
      unless (unchanged.find portable.value).isNone && (unchanged.find native.value).isNone do
        throwError "failed joint installation left a visible reply prefix"
      let clean ← liftM (m := IO) transaction.draft
      let (clean, first) ← liftM (m := IO) <|
        clean.stage origin (.portable "first admitted field".toUTF8)
      let (clean, second) ← liftM (m := IO) <|
        clean.stage origin (.product #[first])
      let .ok () ← liftM (m := BaseIO) (transaction.installDraft clean)
        | throwError "the complete portable reply could not enter the active graph"
      let admitted ← liftM (m := IO) transaction.view
      unless (admitted.find first.value).isSome && (admitted.find second.value).isSome do
        throwError "joint installation lost an admitted field"
      let .ok selected := admitted.project second 0
        | throwError "the admitted record lost its actual preceding field"
      unless selected.value == first.value do
        throwError "joint installation replaced a preceding field's identity"
      if ((← SessionSnapshot.current).graph.find first.value).isSome then
        throwError "draft installation published before whole-cell commit"
      match ← liftM (m := BaseIO) (transaction.installDraft clean) with
      | .error .staleDraft => pure ()
      | _ => throwError "an already installed reply draft was installed twice"
      let stale ← liftM (m := IO) transaction.draft
      let (stale, lost) ← liftM (m := IO) <|
        stale.stage origin (.portable "stale reply field".toUTF8)
      let intervening ← liftM (m := IO) <|
        transaction.stage origin (.portable "intervening field".toUTF8)
      match ← liftM (m := BaseIO) (transaction.installDraft stale) with
      | .error .staleDraft => pure ()
      | _ => throwError "reply installation replaced a newer active graph"
      let latest ← liftM (m := IO) transaction.view
      unless (latest.find lost.value).isNone && (latest.find intervening.value).isSome do
        throwError "stale reply installation changed the active graph"
      let other ← CellTransaction.begin ledger
      match ← liftM (m := BaseIO) (other.installDraft clean) with
      | .error .staleDraft => pure ()
      | _ => throwError "a reply draft crossed its owning transaction"
      discard <| liftM (m := BaseIO) other.abort
      let .ok committed ← transaction.commit
        | throwError "the cell could not publish its admitted joint reply"
      unless (committed.graph.find first.value).isSome &&
          (committed.graph.find second.value).isSome &&
          (committed.graph.find intervening.value).isSome &&
          (committed.graph.find portable.value).isNone do
        throwError "whole-cell commit changed the admitted reply set"
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
    let producer ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) ledger.allocate
    let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
    try
      let token ← liftM (m := IO) do
        child.child.stdin.putStr "reused owner token\n"
        child.child.stdin.flush
        return (← child.child.stdout.getLine).trimAscii.toString
      let value ← liftM (m := IO) <| producer.stage
        { program, occurrence, role } (.ownedExport child token #[])
      let .ok _ ← producer.commit | throwError "the original owned value could not commit"
      let consumer ← CellTransaction.begin ledger
      liftM (m := IO) <| consumer.retain value
      liftM (m := IO) <| consumer.emit (.str "reused result")
      liftM (m := IO) <| owners.close child.generation
      match ← consumer.commit with
      | .error .staleOwner => pure ()
      | _ => throwError "commit lost the owner dependency of a reused result"
      let visible ← SessionSnapshot.current
      unless visible.outputBatches.size == 1 && (visible.graph.find value.value).isSome do
        throwError "failed reuse publication changed the prior snapshot"
      let independent ← CellTransaction.begin ledger
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let portable ← liftM (m := IO) <| independent.stage
        { program, occurrence, role } (.portable "independent result".toUTF8)
      let .ok published ← independent.commit
        | throwError "a dead prior owner blocked an independent portable result"
      unless (published.graph.find portable.value).isSome do
        throwError "the independent portable result was not published"
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
