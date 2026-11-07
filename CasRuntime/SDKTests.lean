module

import CasRuntime.Transport
public meta import Lean.Elab.Command
meta import CasRuntime.Transport

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

/- The actual public SDK preserves input references through the native transport.
This observes protocol/owner transitions, not a mathematical computation.
Reuse: the pinned SDK project, OwnerRegistry, FramedConnection and RequestScope. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let prepared ← liftM (m := IO) <| IO.Process.output {
      cmd := "/home/dzack/.local/bin/uv", args := #["sync", "--frozen", "--project", contract.toString] }
    unless prepared.exitCode == 0 do
      throwError "the pinned native SDK dependencies could not be provisioned: {prepared.stderr}"
    let root ← liftM (m := IO) IO.currentDir
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "selected-backend" {
        cmd := (contract / ".venv/bin/python").toString
        args := #[(root / "scripts/probes/protocol_v2_peer.py").toString]
        env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
      | throwError "the public Python SDK did not negotiate through the native connection"
    try
      let transaction ← CellTransaction.begin ledger
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
      let context ← ContextTelescope.capture #[]
      let layout ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
      let binding ← liftM (m := IO) <| transaction.stage ⟨occurrence, program, layout⟩
        (ValuePayload.portable "retained traffic data".toUTF8)
      let selected : DispatchIdentity := {
        manifestDigest := "sdk-traffic-manifest", profileDigest := "sdk-traffic-profile"
        registration := {
          operation := "references", input := "traffic#input", backend := "selected-backend" } }
      let .ok reservation ← liftM (m := BaseIO) <|
          transaction.reserve occurrence selected wire.connection #[binding]
        | throwError "the public SDK invocation could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let scope ← liftM (m := IO) <| RequestScope.issue ledger reservation graph #[]
        #[{ path := #[.field "item"], binding }] #[]
      let .ok reply ← liftM (m := IO) <| wire.invokeBefore ledger transaction reservation scope
          (Json.mkObj [("item", .str "retained traffic data")]) 5000
        | throwError "the public SDK did not return the original complete input reference"
      unless reply.references.size == 1 && reply.exports.isEmpty do
        throwError "the SDK replaced an input reference with a new native export"
      let some reference := reply.references[0]?
        | throwError "the SDK input reference was not resolved"
      unless reference.binding.value == binding.value do
        throwError "the SDK input reference changed its actual runtime node"
      let .ok dependencies := graph.requiredOwners #[reference.binding]
        | throwError "the original input node is outside the current graph"
      unless dependencies.isEmpty do
        throwError "the returning SDK acquired ownership of an independent portable input"
      discard <| liftM (m := BaseIO) transaction.abort
      liftM (m := IO) do
        for _ in [:1000] do
          unless ← wire.isDraining do break
          IO.sleep 1
        if ← wire.isDraining then throw <| IO.userError "the SDK cleanup did not settle"
        unless (← wire.cleanupFailures).isEmpty do
          throw <| IO.userError "the native SDK rejected request-local cleanup"
      let later ← CellTransaction.begin ledger
      let next ← liftM (m := BaseIO) ledger.allocate
      let .ok reserved ← liftM (m := BaseIO) <| later.reserve next
          { selected with registration := { selected.registration with operation := "echo" } }
          wire.connection #[]
        | throwError "cleanup revoked the unrelated later SDK invocation"
      let current ← liftM (m := IO) later.view
      let nextScope ← liftM (m := IO) <| RequestScope.issue ledger reserved current #[] #[] #[]
      let .ok response ← liftM (m := IO) <|
          wire.invokeBefore ledger later reserved nextScope (.str "after cleanup") 5000
        | throwError "the same supplying SDK connection was unavailable after cleanup"
      unless response.value == .str "after cleanup" && response.requestId > reply.requestId do
        throwError "cleanup changed later traffic or reused its transport identity"
      discard <| liftM (m := BaseIO) later.abort
    finally liftM (m := IO) wire.close
  finally setEnv environment
