/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasContract.Port
meta import CasContract.Port

/-! Actual subprocess checks of transport failures. The fixture supplies no mathematics. -/

namespace CasAcceptance.Kernel.PortFailureProbes

open Lean CasCatalogue

def checkCase (fixture mode : String) (expected : Stratum) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := "python3", args := #[fixture, mode]
    stdin := .piped, stdout := .piped, stderr := .inherit }
  try
    let .ok readyJson ← Backend.readFrame child.stdout
      | throw <| IO.userError s!"{mode}: no fixture ready frame"
    let .ok ready := Backend.readyOf readyJson
      | throw <| IO.userError s!"{mode}: invalid fixture ready frame"
    if mode == "broken-pipe" then discard child.wait
    let connection : Backend.Conn := { child, ready, nextId := ← IO.mkRef 0 }
    match ← Backend.call connection "probe" Json.null with
    | .ok _ => throw <| IO.userError s!"{mode}: expected a failure"
    | .error error =>
      unless error.stratum == expected do
        throw <| IO.userError s!"{mode}: wrong stratum: {error.render}"
      IO.println s!"{mode}: {reprStr error.stratum}"
  finally Backend.abort child

run_elab do
  let fixture := "CasAcceptance/Kernel/port_failure_fixture.py"
  for mode in #["closed", "broken-pipe", "header-eof", "payload-eof", "engine-error"] do
    checkCase fixture mode .unavailable
  for mode in #["bad-header", "bad-json", "bad-utf8", "wrong-id", "bad-status"] do
    checkCase fixture mode .malformed
  checkCase fixture "unsupported" .noImplementation

end CasAcceptance.Kernel.PortFailureProbes
