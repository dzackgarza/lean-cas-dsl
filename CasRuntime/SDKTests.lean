module

import CasRuntime.Transport
import CasRuntime.Encode
public meta import Lean.Elab.Command
meta import CasRuntime.Transport
meta import CasRuntime.Encode

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
      let binding ← liftM (m := IO) <| transaction.stage
        { occurrence, program, role := layout, parameters := #[] }
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
      let storedOccurrence ← liftM (m := BaseIO) ledger.allocate
      let .ok storedReservation ← liftM (m := BaseIO) <| later.reserve storedOccurrence
          { selected with registration := { selected.registration with operation := "stored" } }
          wire.connection #[]
        | throwError "the native callable producer could not reserve"
      let graph ← liftM (m := IO) later.view
      let storedScope ← liftM (m := IO) <|
        RequestScope.issue ledger storedReservation graph #[] #[] #[]
      let .ok produced ← liftM (m := IO) <| wire.invokeBefore ledger later storedReservation
          storedScope (.str "actual retained handler") 5000
        | throwError "the actual SDK did not return its stored callable"
      let some exported := produced.exports[0]?
        | throwError "the native callable has no actual SDK export declaration"
      let callableRole ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
      let callable ← liftM (m := IO) <| later.stage
        { program, occurrence := storedOccurrence, role := callableRole, parameters := #[] }
        (.ownedExport wire.connection exported.token exported.captures)
      let operand ← liftM (m := IO) <| later.stage
        { program, occurrence := storedOccurrence, role := layout, parameters := #[] }
        (.portable "7".toUTF8)
      let .ok wrapper := ValuePayload.container (.str "retained callable wrapper") #[] #[]
        (some callable)
        | throwError "the retained native callable wrapper could not form"
      let retainedCallable ← liftM (m := IO) <| later.stage
        { program, occurrence := storedOccurrence, role := callableRole, parameters := #[] } wrapper
      let nativeOccurrence ← liftM (m := BaseIO) ledger.allocate
      let graph ← liftM (m := IO) later.view
      let .ok actual := RuntimeArgument.ofValue graph 0 operand
        | throwError "the native source argument is outside its graph"
      let nativeRequest ← PreparedRequest.forApplication owners.identities program nativeOccurrence context retainedCallable
        #[← context.close (mkNatLit 7)] #[actual] #[]
      let nativeInputs ← nativeRequest.admitInputs graph
      let nativeArguments ← IO.ofExcept <| (nativeInputs.arguments graph).mapError IO.userError
      let .ok other ← liftM (m := IO) <| FramedConnection.start owners "selected-backend" {
          cmd := (contract / ".venv/bin/python").toString
          args := #[(root / "scripts/probes/protocol_v2_peer.py").toString]
          env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
        | throwError "the distinct native-owner control did not negotiate"
      try
        match ← liftM (m := BaseIO) <|
            later.reserveExport nativeOccurrence retainedCallable other.connection nativeArguments with
        | .error (.reservation .wrongConnection) => pure ()
        | _ => throwError "a matching backend name redirected a retained native export"
      finally liftM (m := IO) other.close
      let .ok native ← liftM (m := BaseIO) <|
          later.reserveExport nativeOccurrence retainedCallable wire.connection nativeArguments
        | throwError "the retained native export could not reserve on its actual owner"
      unless native.selected == .native callable.value exported.token &&
          native.connection == exported.owner do
        throwError "native reservation replaced its actual code, token or supplying owner"
      let graph ← liftM (m := IO) later.view
      let (admitted, encoded) ← nativeRequest.encodeArguments graph wire.connection.generation
        #[.field "arguments"]
      let some role := nativeRequest.roles.arguments[0]?
        | throwError "the source argument role is absent"
      let .ok bound := admitted.lookup graph role.role.id
        | throwError "the native input role lost its admitted binding"
      unless bound.value.value == operand.value && bound.source == .argument 0 do
        throwError "native argument encoding changed its source role or actual input"
      let nativeScope ← liftM (m := IO) <|
        RequestScope.issue ledger native graph encoded.slots encoded.inputs #[]
      let invocation := Json.mkObj [
        ("kind", .str "dependent"), ("prepared_role", .str "native-transport-control"),
        ("parameters", .arr #[]), ("bindings", .arr #[]),
        ("arguments", .arr encoded.values),
        ("argument_layouts", .arr #[Json.mkObj [("kind", .str "data")]]),
        ("result_layout", Json.mkObj [("kind", .str "data")])]
      let .ok invoked ← liftM (m := IO) <|
          wire.invokeBefore ledger later native nativeScope invocation 5000
        | throwError "native transport did not invoke the actual retained SDK handler"
      unless (invoked.value.getObjValAs? String "stored").toOption ==
          some "actual retained handler" do
        throwError "native invocation selected a different stored handler"
      let .ok encodedContext := invoked.value.getObjValAs? String "context"
        | throwError "the stored native handler did not receive its invocation context"
      unless (Json.parse encodedContext).toOption == some invocation do
        throwError "native transport changed the complete invocation context"
      unless encoded.values == #[toJson (7 : Nat)] &&
          invoked.references.map (·.binding.value) == #[operand.value] do
        throwError "native input encoding changed actual packet data or returned input identity"
      match ← liftM (m := BaseIO) <|
          later.reserveExport nativeOccurrence retainedCallable wire.connection #[operand] with
      | .error (.reservation .consumed) => pure ()
      | _ => throwError "a native invocation acquired a second dispatch right"
      discard <| liftM (m := BaseIO) later.abort
    finally liftM (m := IO) wire.close
  finally setEnv environment
