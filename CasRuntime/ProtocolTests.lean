module

import CasRuntime.Owner
import CasContract.Port
public meta import Lean.Elab.Command
meta import CasContract.Port

open Lean CasRuntime CasCatalogue.Backend

/-- A framing peer exercises negotiation only; it supplies no mathematical result.
Reuse: the public Python cas_port.read_frame/write_frame reference implementation. -/
private def negotiationPeer : String := "
import sys
from cas_port import read_frame, write_frame
mode = sys.argv[1]
ready = {'op': 'ready', 'protocol': 2, 'contract': 'cas-computation/2',
         'features': ['scoped-values/2', 'deferred/2', 'suspend-resume/2'],
         'backend': 'framing peer ℤ', 'backend_version': '0'}
if mode == 'legacy':
    ready['protocol'] = 1
elif mode == 'missing':
    ready['features'].pop()
elif mode == 'authority':
    ready['owner'] = 'claimed'
elif mode == 'extra_feature':
    ready['features'].append('diagnostic-extension/7')
write_frame(ready)
hello = read_frame()
if hello != {'op': 'hello', 'protocol': 2, 'contract': 'cas-computation/2'}:
    raise ValueError('the client sent a non-negotiation message')
ack = dict(hello, status='ok')
if mode == 'bad_ack':
    ack['contract'] = 'cas-computation/1'
elif mode == 'authority_ack':
    ack['proof'] = 'claimed'
write_frame(ack)
"

run_cmd Lean.Elab.Command.liftIO do
  let contract ← packageDir contractPackage
  let owners ← OwnerRegistry.new
  for mode in #["valid", "extra_feature", "legacy", "missing", "authority", "bad_ack", "authority_ack"] do
    let child ← owners.spawn {
      cmd := "/usr/bin/python3", args := #["-c", negotiationPeer, mode]
      env := #[("PYTHONPATH", some (contract / "python").toString)] }
    try
      match ← negotiateV2 "configured-backend" child.child.stdin child.child.stdout with
      | .ok ready =>
        unless mode == "valid" || mode == "extra_feature" do
          throw <| IO.userError "an incompatible peer passed v2 negotiation"
        unless ready.backend == "framing peer ℤ" && ready.backendVersion == "0" do
          throw <| IO.userError "v2 negotiation lost diagnostic announcement data"
      | .error (.unavailable backend reason) =>
        unless backend == "configured-backend" && reason.startsWith "incompatible_protocol" &&
            mode != "valid" && mode != "extra_feature" do
          throw <| IO.userError "v2 negotiation lost its incompatible-protocol outcome"
      | .error error => throw <| IO.userError s!"unexpected negotiation failure: {error.render}"
    finally owners.close child.generation

run_cmd Lean.Elab.Command.liftIO do
  let hello := helloV2
  let .ok () := checkHelloV2 hello
    | throw <| IO.userError "the public v2 hello failed its own parser"
  let .ok () := checkHelloV2Ack helloV2Ack
    | throw <| IO.userError "the public v2 acknowledgement failed its own parser"
  for packet in #[
      Json.mkObj [("op", .str "hello"), ("protocol", toJson (1 : Nat)),
        ("contract", .str "cas-computation/2")],
      Json.mkObj [("op", .str "hello"), ("protocol", toJson (2 : Nat)),
        ("contract", .str "cas-computation/2"), ("owner", .str "claimed")]] do
    unless (checkHelloV2 packet).isError do
      throw <| IO.userError "a malformed hello passed protocol validation"
