module

import CasRuntime.Transport
public meta import Lean.Elab.Command
meta import CasRuntime.Transport

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

/-- This peer checks framing and resource controls, not a mathematical computation.
Reuse: the public Python framing functions from CasContract.Port. -/
private def framingPeer : String := "
import sys, time
from cas_port import read_frame, write_frame
mode = sys.argv[1]
write_frame({'op': 'ready', 'protocol': 2, 'contract': 'cas-computation/2',
             'features': ['scoped-values/2', 'deferred/2', 'suspend-resume/2'],
             'backend': 'resource framing peer', 'backend_version': '0'})
hello = read_frame()
if hello != {'op': 'hello', 'protocol': 2, 'contract': 'cas-computation/2'}:
    raise ValueError('missing negotiation')
write_frame(dict(hello, status='ok'))
expected = 0
while (request := read_frame()) is not None:
    rid = request['request_id']
    if rid != expected:
        raise ValueError('request IDs were reused or reordered')
    expected += 1
    if request['op'] == '$cas.discard':
        if set(request) != {'protocol', 'request_id', 'op', 'discard_request_id'}:
            raise ValueError('invalid discard framing')
        if request['discard_request_id'] != 1:
            raise ValueError('discard changed its original request')
        write_frame({'request_id': rid, 'status': 'ok', 'disposed': True})
        continue
    if set(request) != {'protocol', 'request_id', 'op', 'input', 'args', 'scope_id'}:
        raise ValueError('invalid computational request framing')
    if request['protocol'] != 2 or request['op'] != 'resource-test':
        raise ValueError('the transport changed the selected operation')
    if request['input'] != 'resource-test-input' or not request['scope_id']:
        raise ValueError('the transport changed the selected input or scope')
    if request['args'] == 'slow':
        time.sleep(0.3)
    write_frame({'request_id': rid + (1 if mode == 'wrong_id' else 0),
                 'status': 'ok', 'value': {'ctor': 'valueData', 'args': [rid]},
                 'exports': []})
"

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let arguments : IO.Process.SpawnArgs := {
      cmd := "/usr/bin/python3", args := #["-c", framingPeer, "valid"]
      env := #[("PYTHONPATH", some (contract / "python").toString)] }
    let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "configured-backend" arguments 5000
      | throwError "the actual framing peer could not negotiate"
    try
      let selected : DispatchIdentity := {
        manifestDigest := "resource-test-manifest"
        registration := {
          operation := "resource-test", input := "resource-test-input", backend := "configured-backend" }
        profileDigest := "resource-test-profile" }
      let first ← CellTransaction.begin ledger
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let .ok reservation ← liftM (m := BaseIO) <|
        first.reserve occurrence selected wire.connection #[]
        | throwError "the framing call could not reserve"
      let graph ← liftM (m := IO) first.view
      let scope ← liftM (m := IO) <| RequestScope.issue ledger reservation graph #[] #[] #[]
      let .ok reply ← liftM (m := IO) <| wire.invoke ledger first reservation scope (.str "first")
        | throwError "the actual framed request did not return its parsed control"
      unless reply.requestId == 0 && reply.scopeId == scope.id do
        throwError "the framed reply lost its exact request and scope"
      match ← liftM (m := IO) <| wire.invoke ledger first reservation scope (.str "duplicate") with
      | .error (.unavailable _ _) => pure ()
      | _ => throwError "the transport sent a reserved occurrence again"
      let cancelled ← CellTransaction.begin ledger
      let pending ← liftM (m := BaseIO) ledger.allocate
      let .ok reserved ← liftM (m := BaseIO) <|
        cancelled.reserve pending selected wire.connection #[]
        | throwError "the cancellable framing call could not reserve"
      let graph ← liftM (m := IO) cancelled.view
      let scoped ← liftM (m := IO) <| RequestScope.issue ledger reserved graph #[] #[] #[]
      let outstanding ← liftM (m := IO) <| IO.asTask (prio := .dedicated) <|
        wire.invoke ledger cancelled reserved scoped (.str "slow")
      liftM (m := IO) do
        for _ in [:1000] do
          if ← wire.isBusy then break
          IO.sleep 1
        unless ← wire.isBusy do throw <| IO.userError "the actual frame never became outstanding"
      unless ← liftM (m := BaseIO) (wire.cancel cancelled reserved) do
        throwError "cooperative cancellation did not win the active cell"
      unless ← liftM (m := BaseIO) wire.isDraining do
        throwError "cancellation released an outstanding frame's permit"
      let later ← CellTransaction.begin ledger
      let next ← liftM (m := BaseIO) ledger.allocate
      let .ok nextReservation ← liftM (m := BaseIO) <|
        later.reserve next selected wire.connection #[]
        | throwError "the later framing call could not reserve"
      let nextGraph ← liftM (m := IO) later.view
      let nextScope ← liftM (m := IO) <|
        RequestScope.issue ledger nextReservation nextGraph #[] #[] #[]
      let queued ← liftM (m := IO) <| IO.asTask (prio := .dedicated) <|
        wire.invoke ledger later nextReservation nextScope (.str "after drain")
      let drained ← liftM (m := IO) <| IO.ofExcept (← IO.wait outstanding)
      match drained with
      | .error (.unavailable backend reason) =>
        unless backend == "configured-backend" && reason == "cancelled" do
          throwError "the drained call lost its cancellation outcome"
      | _ => throwError "a cancelled call exposed its late reply"
      let .ok after ← liftM (m := IO) <| IO.ofExcept (← IO.wait queued)
        | throwError "a later call could not use the drained connection"
      unless after.requestId == 3 do
        throwError "a call overtook the exact frame drain and fresh discard request"
      unless ← liftM (m := BaseIO) (owners.isLive wire.connection.generation) do
        throwError "cooperative cancellation closed the supplying generation"
      if (← liftM (m := BaseIO) (ledger.pendingFor pending cancelled.id)).isSome then
        throwError "cancellation retained a pending occurrence locator"
      discard <| liftM (m := BaseIO) later.abort
    finally liftM (m := IO) wire.close
  finally setEnv original
