/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Realize
meta import CasCatalogue.Realize

@[expose] public section

open Lean Meta Elab Term CasCatalogue CasCatalogue.Realize

namespace CasAcceptance.Kernel.ProtocolFixtureData

/-- Receive the fixture's original arbitrary packet through the existing fault
injection port, retaining its real supplying session throughout the check.
This supplies engineering data only; it establishes no mathematical answer. -/
def withData (backend operation : String) (expected : Json)
    (action : Harness → DataOwnership.Data → (String × Nat) → TermElabM Unit)
    (registrations : Array Registration := #[]) : TermElabM Unit := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let root ← IO.FS.realPath root
  let runtime ← IO.FS.createTempDir
  let runtime ← IO.FS.realPath runtime
  let configuration := runtime / "original-fixture-data.json"
  IO.FS.writeFile configuration ((Json.mkObj [
    ("mode", toJson "replace"), ("operation", toJson operation),
    ("value", Backend.ComputationalValue.encode (.inline expected))]).compress ++ "\n")
  let harness ← Harness.ofManifest root {
    backends := #[{
      name := backend, command := "python3"
      args := #["probe_reply_conditions.py", configuration.toString] }]
    registrations }
  try
    let .ok session ← harness.connection backend
      | throwError "the original-data fixture's protocol session did not start"
    let .ok answer ← Backend.call session.connection operation Json.null
      | throwError "the original-data fixture did not receive its supplied packet"
    let received ← receiveComputationalData harness backend operation answer
    let data ← match received with
      | .inline value => pure ({ json := value } : DataOwnership.Data)
      | .scoped data => pure data
      | _ => throwError "the original-data fixture lost its received supplier scope"
    unless data.json == expected do
      throwError "the fixture protocol changed the independently supplied original packet"
    checkDataOwners harness data
    action harness data (backend, session.identity)
  finally
    harness.stop
    IO.FS.removeDirAll runtime

end CasAcceptance.Kernel.ProtocolFixtureData
