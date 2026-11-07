module

import CasRuntime.Materialize
import CasRuntime.Transport
public meta import Lean.Elab.Command
meta import CasRuntime.Materialize
meta import CasRuntime.Transport

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

-- Actual SDK frames enter admission, same-cell reuse and whole-cell publication.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    let initial ← SessionSnapshot.initialize owners
    let prefixEnvironment ← getEnv
    let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "completion-peer" {
        cmd := (contract / ".venv/bin/python").toString
        args := #[(root / "scripts/probes/protocol_v2_peer.py").toString]
        env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
      | throwError "the completion peer did not negotiate"
    try
      let context ← ContextTelescope.capture #[]
      let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
      let selected : DispatchIdentity := {
        manifestDigest := "completion-manifest", profileDigest := "completion-profile"
        registration := { operation := "echo", input := "completion#input", backend := wire.backend } }
      let perform (transaction : CellTransaction) : MetaM CompletionAssociation := do
        let occurrence ← liftM (m := BaseIO) ledger.allocate
        let scalar ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
        let value ← liftM (m := IO) <| transaction.stage
          { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
        let identity ← mkAppOptM ``id #[some (mkConst ``Nat)]
        let function ← SourceLayout.ofTerm (← context.close identity)
        let callable ← liftM (m := IO) <| transaction.stage
          { program, occurrence, role := function, parameters := #[] } (.closure program #[])
        let graph ← liftM (m := IO) transaction.view
        let .ok actual := RuntimeArgument.ofValue graph 0 value
          | throwError "the completion input is absent"
        let request ← PreparedRequest.forApplication program occurrence context callable
          #[scalar.source] #[actual] #[]
        discard <| request.admitInputs graph
        let .ok reservation ← liftM (m := BaseIO) <|
          transaction.reserve occurrence selected wire.connection #[value]
          | throwError "the completion invocation could not reserve"
        let scope ← liftM (m := IO) <| RequestScope.issue ledger reservation graph #[value] #[] #[]
        let .ok reply ← liftM (m := IO) <| wire.invokeBefore ledger transaction reservation scope
          (ScopedReference.scope 0).encode 5000
          | throwError "the completion invocation did not return"
        let .ok completion ← reply.stageCompletion request transaction scope wire.connection
          | throwError "the admitted reply did not stage its completion"
        return completion
      let transaction ← CellTransaction.begin ledger
      let first ← perform transaction
      let second ← perform transaction
      let some firstRole := first.request.roles.results[0]?
        | throwError "the completed result has no root role"
      match ← liftM (m := BaseIO) <| transaction.reuse first.request.occurrence firstRole.role.id with
      | .ok (.ready binding) =>
        unless binding.value == first.response.root.value do
          throwError "same-cell reuse replaced its completed value"
      | _ => throwError "same-cell reuse did not find its staged completion"
      if (← SessionSnapshot.current).receipt first.request.occurrence |>.isSome then
        throwError "an uncommitted completion entered an Environment query"
      transaction.emit (.str "completed output")
      let .ok published ← transaction.commit
        | throwError "admitted SDK completions could not commit"
      let some receipt := published.receipt first.request.occurrence
        | throwError "whole-cell commit omitted its receipt"
      let some other := published.receipt second.request.occurrence
        | throwError "whole-cell commit omitted a joint completion"
      let some batch := published.outputBatches.back?
        | throwError "whole-cell commit omitted its output batch"
      unless receipt.snapshot == published.id && receipt.commit == batch.commit &&
          receipt.outputBatch == batch.id && other.outputBatch == batch.id &&
          receipt.association.response.root.value == first.response.root.value do
        throwError "receipt promotion changed its actual result or publication identities"
      let .ok (some reused) ← liftM (m := BaseIO) <|
        published.reuse owners first.request.occurrence firstRole.role.id
        | throwError "the visible committed receipt could not supply its result"
      unless reused.value == first.response.root.value do
        throwError "committed reuse replaced its actual value"
      let committedEnvironment ← getEnv
      setEnv prefixEnvironment
      unless (← SessionSnapshot.current).id == initial.id &&
          ((← SessionSnapshot.current).receipt first.request.occurrence).isNone do
        throwError "restoring an old snapshot recovered a newer receipt"
      let restored ← CellTransaction.begin ledger
      match ← liftM (m := BaseIO) <| restored.reuse first.request.occurrence firstRole.role.id with
      | .ok .unavailable => pure ()
      | _ => throwError "a consumed ledger entry supplied an invisible completion"
      match ← liftM (m := BaseIO) <|
          restored.reserve first.request.occurrence selected wire.connection #[] with
      | .error (.reservation .consumed) => pure ()
      | _ => throwError "snapshot restoration granted another dispatch"
      discard <| liftM (m := BaseIO) restored.abort
      setEnv committedEnvironment
      let aborted ← CellTransaction.begin ledger
      let tentative ← perform aborted
      discard <| liftM (m := BaseIO) aborted.abort
      if (← SessionSnapshot.current).receipt tentative.request.occurrence |>.isSome then
        throwError "abort published a staged completion"
      match ← liftM (m := BaseIO) <| ledger.pendingFor tentative.request.occurrence aborted.id with
      | none => pure ()
      | some _ => throwError "a settled completion remained pending in the ledger"
      liftM (m := IO) wire.close
      let .ok (some portable) ← liftM (m := BaseIO) <|
        published.reuse owners first.request.occurrence firstRole.role.id
        | throwError "an independent portable completion acquired its former provider's owner"
      unless portable.value == first.response.root.value do
        throwError "provider loss reconstructed the committed portable result"
    finally liftM (m := IO) wire.close
  finally setEnv original
