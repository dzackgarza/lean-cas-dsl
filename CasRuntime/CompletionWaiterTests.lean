module

import CasRuntime.Execute
import CasRuntime.Materialize
import CasRuntime.Transport
public meta import Lean.Elab.Command
meta import CasRuntime.Execute
meta import CasRuntime.Materialize
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
    let prefixEnvironment ← getEnv
    let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "waiter-peer" {
        cmd := (contract / ".venv/bin/python").toString
        args := #[(root / "scripts/probes/protocol_v2_peer.py").toString]
        env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
      | throwError "the completion waiter peer did not negotiate"
    try
      let context ← ContextTelescope.capture #[]
      let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let transaction ← CellTransaction.begin ledger
      let scalar ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
      let input ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
      let identity ← mkAppOptM ``id #[some (mkConst ``Nat)]
      let function ← SourceLayout.ofTerm (← context.close identity)
      let callable ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := function, parameters := #[] } (.closure program #[])
      let graph ← liftM (m := IO) transaction.view
      let .ok actual := RuntimeArgument.ofValue graph 0 input
        | throwError "the waiter input is absent"
      let request ← PreparedRequest.forApplication owners.identities program occurrence context callable
        #[scalar.source] #[actual] #[]
      let some role := request.roles.results[0]?
        | throwError "the waiter request has no result role"
      let selected : DispatchIdentity := {
        manifestDigest := "waiter-manifest", profileDigest := "waiter-profile"
        registration := { operation := "echo", input := "waiter#input", backend := wire.backend } }
      let .ok .producer ← liftM (m := BaseIO) <| transaction.claim request.roles.scope
        | throwError "the first demand did not claim its producer"
      let .ok .waiter ← liftM (m := BaseIO) <| transaction.claim request.roles.scope
        | throwError "a repeated fresh demand started another producer"
      match ← liftM (m := BaseIO) <| transaction.reuse occurrence role.role.id with
      | .ok .running => pure ()
      | _ => throwError "a claimed producer was invisible before wire reservation"
      let .ok attached ← liftM (m := BaseIO) <| transaction.watch occurrence role.role.id
        | throwError "the first waiter could not attach"
      let .ok detached ← liftM (m := BaseIO) <| transaction.watch occurrence role.role.id
        | throwError "the second waiter could not attach"
      let .ok reservation ← liftM (m := BaseIO) <|
        transaction.reserve occurrence selected wire.connection #[input]
        | throwError "the waiter invocation could not reserve"
      liftM (m := BaseIO) detached.detach
      match ← liftM (m := IO) detached.wait with
      | .error .detached => pure ()
      | _ => throwError "a detached waiter remained attached"
      unless (← liftM (m := BaseIO) transaction.activeGraph).isSome &&
          (← liftM (m := BaseIO) (ledger.pendingFor occurrence transaction.id)).isSome do
        throwError "detaching one waiter cancelled its producer"
      let waiting ← liftM (m := IO) <| IO.asTask (prio := .dedicated) attached.wait
      let scope ← liftM (m := IO) <|
        RequestScope.issue ledger reservation graph #[input] #[] #[]
      let .ok reply ← liftM (m := IO) <| wire.invokeBefore ledger transaction reservation scope
        (ScopedReference.scope 0).encode 5000
        | throwError "the waiter producer did not return"
      let .ok completion ← reply.stageCompletion request transaction scope wire.connection
        | throwError "the waiter producer did not stage its complete reply"
      let .ok joined ← liftM (m := IO) <| IO.ofExcept (← IO.wait waiting)
        | throwError "the attached waiter did not receive its completed result"
      unless joined.value == completion.response.root.value do
        throwError "a waiter received a replacement result"
      let noDispatch : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
        fun _ _ => throwError "a completed occurrence reached external execution"
      let reused ← Execute.run noDispatch
        (PFunctor.FreeM.lift (P := OperationalSignature) request) transaction
      unless reused.root.value == joined.value do
        throwError "the execution handler replaced a staged completion"
      let .ok published ← transaction.commit
        | throwError "the joined result could not commit"
      let committedEnvironment ← getEnv
      let consumer ← CellTransaction.begin ledger
      let committed ← Execute.run noDispatch
        (PFunctor.FreeM.lift (P := OperationalSignature) request) consumer
      unless committed.root.value == joined.value do
        throwError "the execution handler replaced a committed receipt"
      discard <| liftM (m := BaseIO) consumer.abort
      let cancelledCell ← CellTransaction.begin ledger
      let cancelledOccurrence ← liftM (m := BaseIO) ledger.allocate
      let cancelledRequest ← PreparedRequest.forApplication owners.identities program cancelledOccurrence
        context callable #[scalar.source] #[actual] #[]
      let some cancelledRole := cancelledRequest.roles.results[0]?
        | throwError "the cancelled waiter has no result role"
      let .ok _ ← liftM (m := BaseIO) <|
        cancelledCell.reserve cancelledOccurrence selected wire.connection #[input]
        | throwError "the cancelled producer could not reserve"
      let .ok cancelledWaiter ← liftM (m := BaseIO) <|
        cancelledCell.watch cancelledOccurrence cancelledRole.role.id
        | throwError "the cancelled producer's waiter could not attach"
      discard <| liftM (m := BaseIO) cancelledCell.abort
      match ← liftM (m := IO) cancelledWaiter.wait with
      | .error .settled => pure ()
      | _ => throwError "an aborted producer supplied a completion through its waiter"
      setEnv prefixEnvironment
      let restored ← CellTransaction.begin ledger
      let failure : Option Exception ← try
        discard <| Execute.run noDispatch
          (PFunctor.FreeM.lift (P := OperationalSignature) request) restored
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "an old snapshot recovered a consumed completion"
      unless (← failure.toMessageData.toString).endsWith "unavailable: reserved_without_receipt" do
        throw failure
      setEnv committedEnvironment
      unless (published.receipt occurrence).isSome do
        throwError "snapshot restoration changed the immutable committed receipt"
    finally liftM (m := IO) wire.close
  finally setEnv original
