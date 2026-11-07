module

import CasRuntime.Execute
import CasRuntime.Transport
public meta import Lean.Elab.Command
meta import CasRuntime.Execute
meta import CasRuntime.Transport

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "failure-peer" {
        cmd := (contract / ".venv/bin/python").toString
        args := #[(root / "scripts/probes/protocol_v2_peer.py").toString]
        env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
      | throwError "the producer failure peer did not negotiate"
    try
      let context ← ContextTelescope.capture #[]
      let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
      let producing ← liftM (m := BaseIO) ledger.allocate
      let producer ← CellTransaction.begin ledger
      let scalar ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
      let input ← liftM (m := IO) <| producer.stage
        { program, occurrence := producing, role := scalar, parameters := #[] } (.portable "7".toUTF8)
      let identity ← mkAppOptM ``id #[some (mkConst ``Nat)]
      let function ← SourceLayout.ofTerm (← context.close identity)
      let callable ← liftM (m := IO) <| producer.stage
        { program, occurrence := producing, role := function, parameters := #[] } (.closure program #[])
      let .ok before ← producer.commit | throwError "the failure control inputs could not commit"
      let failedCell ← CellTransaction.begin ledger
      let failedOccurrence ← liftM (m := BaseIO) ledger.allocate
      let .ok actual := RuntimeArgument.ofValue before.graph 0 input
        | throwError "the failure control input is absent"
      let request ← PreparedRequest.forApplication owners.identities program failedOccurrence
        context callable #[scalar.source] #[actual] #[]
      let selected : DispatchIdentity := {
        manifestDigest := "failure-manifest", profileDigest := "failure-profile"
        registration := {
          operation := "missing-waiter-operation", input := "failure#input", backend := wire.backend } }
      let observer : IO.Ref (Option CompletionWaiter) ← liftM (m := IO) <| IO.mkRef none
      let missing : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
        fun (demand : PreparedRequest) (active : CellTransaction) => do
          let some role := demand.roles.results[0]?
            | throwError "the failed producer lost its result role"
          let .ok waiter ← liftM (m := BaseIO) <| active.watch demand.occurrence role.role.id
            | throwError "the failed producer's observer could not attach"
          liftM (m := BaseIO) <| observer.set (some waiter)
          let .ok reserved ← liftM (m := BaseIO) <|
            active.reserve demand.occurrence selected wire.connection #[input]
            | throwError "the unsupported invocation could not reserve"
          let graph ← liftM (m := IO) active.view
          let scope ← liftM (m := IO) <| RequestScope.issue ledger reserved graph #[input] #[] #[]
          match ← liftM (m := IO) <| wire.invokeBefore ledger active reserved scope (toJson (7 : Nat)) 5000 with
          | .error error => CasCatalogue.throwStratum (m := MetaM) error.stratum error.render
          | .ok _ => throwError "the SDK accepted an unimplemented diagnostic operation"
      let failure : Option Exception ← try
        discard <| Execute.run missing (PFunctor.FreeM.lift (P := OperationalSignature) request) failedCell
        pure none
      catch error => pure (some error)
      let some failure := failure | throwError "the unsupported producer returned a value"
      unless failure.toMessageData.hasTag (· == CasCatalogue.Stratum.noImplementation.tag) do throw failure
      let some failedWaiter ← liftM (m := IO) observer.get
        | throwError "the failed producer lost its observer"
      match ← liftM (m := IO) failedWaiter.wait with
      | .error .settled => throwError "a producer failure was reported to its waiter as cancellation"
      | .error _ => pure ()
      | .ok _ => throwError "a failed producer supplied a mathematical result"
      unless (← SessionSnapshot.current).id == before.id do
        throwError "a failed producer changed the committed Environment"
    finally liftM (m := IO) wire.close
  finally setEnv original
