module

import CasRuntime.Transport
public meta import Lean.Elab.Command
meta import CasRuntime.Transport

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

/-- This peer checks framing and resource controls, not a mathematical computation.
Reuse: the public Python framing functions from CasContract.Port. -/
private def framingPeer : String := "
import sys, signal
from cas_port import read_frame, write_frame
signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGUSR1})
mode = sys.argv[1]
write_frame({'op': 'ready', 'protocol': 2, 'contract': 'cas-computation/2',
             'features': ['scoped-values/2', 'deferred/2', 'suspend-resume/2', 'export-capture-frames/2'],
             'backend': 'resource framing peer', 'backend_version': '0'})
hello = read_frame()
if hello != {'op': 'hello', 'protocol': 2, 'contract': 'cas-computation/2'}:
    raise ValueError('missing negotiation')
write_frame(dict(hello, status='ok'))
last = -1
requests = []
introduced = set()
discards = []
while (request := read_frame()) is not None:
    rid = request['request_id']
    if rid <= last:
        raise ValueError('request IDs were reused or reordered')
    last = rid
    requests.append(rid)
    if request['op'] == '$cas.discard':
        if set(request) != {'protocol', 'request_id', 'op', 'discard_request_id'}:
            raise ValueError('invalid discard framing')
        if request['discard_request_id'] not in introduced or request['discard_request_id'] in discards:
            raise ValueError('discard changed its original request')
        discards.append(request['discard_request_id'])
        write_frame({'request_id': rid, 'status': 'ok', 'disposed': True})
        continue
    if set(request) != {'protocol', 'request_id', 'op', 'input', 'args', 'scope_id'}:
        raise ValueError('invalid computational request framing')
    if request['protocol'] != 2 or request['op'] != 'resource-test':
        raise ValueError('the transport changed the selected operation')
    if request['input'] != 'resource-test-input' or not request['scope_id']:
        raise ValueError('the transport changed the selected input or scope')
    introduced.add(rid)
    if request['args'] == 'slow':
        signal.sigwait({signal.SIGUSR1})
    if mode == 'error':
        write_frame({'request_id': rid, 'status': 'error', 'kind': 'ResourceFailure', 'message': 'peer error'})
        continue
    if mode == 'unsupported':
        write_frame({'request_id': rid, 'status': 'unsupported', 'op': request['op']})
        continue
    if mode == 'invalid':
        write_frame({'request_id': rid, 'status': 'invalid'})
        continue
    write_frame({'request_id': rid + (1 if mode == 'wrong_id' else 0),
                 'status': 'ok', 'value': {'ctor': 'valueData', 'args': [
                     {'requests': requests, 'discards': discards}]},
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
      let .ok reply ← liftM (m := IO) <| wire.invokeBefore ledger first reservation scope (.str "first") 5000
        | throwError "the actual framed request did not return its parsed control"
      unless reply.requestId == 0 && reply.scopeId == scope.id do
        throwError "the framed reply lost its exact request and scope"
      let unrelated ← CellTransaction.begin ledger
      match ← liftM (m := IO) <| wire.invokeBefore ledger unrelated reservation scope .null 0 with
      | .error (.unavailable _ "request_identity_mismatch") => pure ()
      | _ => throwError "a deadline accepted another transaction's invocation authority"
      unless (← liftM (m := BaseIO) unrelated.activeGraph).isSome &&
          (← liftM (m := BaseIO) first.activeGraph).isSome do
        throwError "a foreign deadline changed either transaction"
      discard <| liftM (m := IO) (scope.resolveMany reservation graph scope.wireId #[])
      discard <| liftM (m := BaseIO) unrelated.abort
      match ← liftM (m := IO) <| wire.invoke ledger first reservation scope (.str "duplicate") with
      | .error (.unavailable _ _) => pure ()
      | _ => throwError "the transport sent a reserved occurrence again"
      let cancelled ← CellTransaction.begin ledger
      let pending ← liftM (m := BaseIO) ledger.allocate
      let .ok reserved ← liftM (m := BaseIO) <|
        cancelled.reserve pending selected wire.connection #[]
        | throwError "the cancellable framing call could not reserve"
      let graph ← liftM (m := IO) cancelled.view
      let pendingScope ← liftM (m := IO) <| RequestScope.issue ledger reserved graph #[] #[] #[]
      let outstanding ← liftM (m := IO) <| IO.asTask (prio := .dedicated) <|
        wire.invoke ledger cancelled reserved pendingScope (.str "slow")
      liftM (m := IO) do
        for _ in [:1000] do
          if ← wire.hasOutstanding then break
          IO.sleep 1
        unless ← wire.hasOutstanding do throw <| IO.userError "the actual frame never became outstanding"
      unless ← liftM (m := BaseIO) (wire.cancel cancelled reserved) do
        throwError "cooperative cancellation did not win the active cell"
      unless ← liftM (m := BaseIO) wire.isDraining do
        throwError "cancellation released an outstanding frame's permit"
      let expired ← CellTransaction.begin ledger
      let waiting ← liftM (m := BaseIO) ledger.allocate
      let .ok waitingReservation ← liftM (m := BaseIO) <|
        expired.reserve waiting selected wire.connection #[]
        | throwError "the deadline-bound queued call could not reserve"
      let waitingGraph ← liftM (m := IO) expired.view
      let waitingScope ← liftM (m := IO) <|
        RequestScope.issue ledger waitingReservation waitingGraph #[] #[] #[]
      match ← liftM (m := IO) <|
          wire.invokeBefore ledger expired waitingReservation waitingScope (.str "expired queue") 20 with
      | .error (.unavailable backend reason) =>
        unless backend == "configured-backend" && reason == "busy_draining" do
          throwError "the queued deadline lost its busy-draining outcome"
      | _ => throwError "a queued call overtook the outstanding frame or ignored its deadline"
      unless (← liftM (m := BaseIO) expired.activeGraph).isNone &&
          (← liftM (m := BaseIO) (ledger.pendingFor waiting expired.id)).isNone do
        throwError "an expired queue item retained transaction or dispatch authority"
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
      let released ← liftM (m := IO) <| IO.Process.output {
        cmd := "/bin/kill", args := #["-USR1", toString wire.connection.child.pid] }
      unless released.exitCode == 0 do
        throwError "the framing peer's independent release signal failed"
      let drained ← liftM (m := IO) <| IO.ofExcept (← IO.wait outstanding)
      match drained with
      | .error (.unavailable backend reason) =>
        unless backend == "configured-backend" && reason == "cancelled" do
          throwError "the drained call lost its cancellation outcome"
      | _ => throwError "a cancelled call exposed its late reply"
      let .ok after ← liftM (m := IO) <| IO.ofExcept (← IO.wait queued)
        | throwError "a later call could not use the drained connection"
      let .ok #[traffic] := after.value.getObjValAs? (Array Json) "args"
        | throwError "the framing peer omitted its observed request traffic"
      let .ok sent := traffic.getObjValAs? (Array Nat) "requests"
        | throwError "the framing peer omitted its observed request identities"
      let .ok discarded := traffic.getObjValAs? (Array Nat) "discards"
        | throwError "the framing peer omitted its observed discard identity"
      unless sent.size == 4 && discarded.size == 1 &&
          discarded[0]? == sent[1]? && sent[3]? == some after.requestId do
        throwError "a call overtook the exact frame drain and fresh discard request"
      unless ← liftM (m := BaseIO) (owners.isLive wire.connection.generation) do
        throwError "cooperative cancellation closed the supplying generation"
      if (← liftM (m := BaseIO) (ledger.pendingFor pending cancelled.id)).isSome then
        throwError "cancellation retained a pending occurrence locator"
      discard <| liftM (m := BaseIO) first.abort
      discard <| liftM (m := BaseIO) later.abort
      liftM (m := IO) do
        for _ in [:1000] do
          unless ← wire.isDraining do break
          IO.sleep 1
        if ← wire.isDraining then
          throw <| IO.userError "received reply cleanup remained pending"
        unless (← wire.cleanupFailures).isEmpty do
          throw <| IO.userError "cleanup of received uncommitted replies failed"
    finally liftM (m := IO) wire.close
  finally setEnv original

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let contract ← liftM (m := IO) <| packageDir contractPackage
    for mode in #["wrong_id", "error", "unsupported", "invalid"] do
      let arguments : IO.Process.SpawnArgs := {
        cmd := "/usr/bin/python3", args := #["-c", framingPeer, mode]
        env := #[("PYTHONPATH", some (contract / "python").toString)] }
      let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "configured-backend" arguments 5000
        | throwError "the negative framing peer could not negotiate"
      try
        let transaction ← CellTransaction.begin ledger
        let occurrence ← liftM (m := BaseIO) ledger.allocate
        let selected : DispatchIdentity := {
          manifestDigest := "resource-test-manifest"
          registration := {
            operation := "resource-test", input := "resource-test-input", backend := "configured-backend" }
          profileDigest := "resource-test-profile" }
        let .ok reservation ← liftM (m := BaseIO) <|
          transaction.reserve occurrence selected wire.connection #[]
          | throwError "the negative framing call could not reserve"
        let graph ← liftM (m := IO) transaction.view
        let scope ← liftM (m := IO) <| RequestScope.issue ledger reservation graph #[] #[] #[]
        match ← liftM (m := IO) <| wire.invoke ledger transaction reservation scope .null with
        | .error (.protocol _) =>
          unless mode == "wrong_id" || mode == "invalid" do
            throwError "a well-framed execution failure became malformed"
        | .error (.backend kind message) =>
          unless mode == "error" && kind == "ResourceFailure" && message == "peer error" do
            throwError "the leaf execution failure lost its details"
        | .error (.unsupported operation) =>
          unless mode == "unsupported" && operation == "resource-test" do
            throwError "the unsupported outcome lost its exact consumed operation"
        | _ => throwError "the negative framing reply was admitted or misclassified"
        unless (← liftM (m := BaseIO) transaction.activeGraph).isNone &&
            (← liftM (m := BaseIO) (ledger.pendingFor occurrence transaction.id)).isNone do
          throwError "a failed framing call retained its active cell or pending locator"
        liftM (m := IO) do
          for _ in [:1000] do
            unless ← wire.isDraining do break
            IO.sleep 1
          if ← wire.isDraining then throw <| IO.userError "failure cleanup remained pending"
        let live ← liftM (m := BaseIO) <| owners.isLive wire.connection.generation
        unless live == (mode != "wrong_id") do
          throwError "forced protocol close and framed execution failure lost their distinct lifetimes"
      finally liftM (m := IO) wire.close
  finally setEnv original

run_cmd Lean.Elab.Command.liftIO do
  let owners ← OwnerRegistry.new
  for _ in [:64] do
    match ← FramedConnection.start owners "early-exit" { cmd := "/usr/bin/true" } 5000 with
    | .error (.unavailable backend reason) =>
      unless backend == "early-exit" && reason == "incompatible_protocol: no valid ready frame" do
        throw <| IO.userError "an early process exit lost its explicit startup outcome"
    | _ => throw <| IO.userError "an exited process became an executable v2 connection"
  match ← FramedConnection.start owners "silent-peer" { cmd := "/bin/cat" } 20 with
  | .error (.unavailable backend reason) =>
    unless backend == "silent-peer" && reason == "incompatible_protocol: deadline" do
      throw <| IO.userError "silent negotiation lost its explicit deadline outcome"
  | _ => throw <| IO.userError "a silent process became an executable v2 connection"
  match ← FramedConnection.start owners "failed-start" { cmd := "/dev/null/not-an-executable" } 5000 with
  | .error (.unavailable backend reason) =>
    -- Lean v4.33.0 runtime/process.cpp: exec failure exits the forked child;
    -- the parent observes EOF before ready, rather than a spawn exception.
    unless backend == "failed-start" && reason == "incompatible_protocol: no valid ready frame" do
      throw <| IO.userError "pre-ready child failure lost its unavailable outcome"
  | _ => throw <| IO.userError "a failed process start became an executable v2 connection"
