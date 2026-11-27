module

public import CasRuntime.Connection
public import CasContract.Registration
public import CasContract.Failure
public import Lean.Meta

public section

namespace CasRuntime

open Lean Meta CasCatalogue CasCatalogue.Backend

/-- Negotiated backend processes for one loaded manifest. -/
structure BackendConnections where
  private mk ::
  private owners : OwnerRegistry
  private root : System.FilePath
  private programs : Array BackendProgram
  private timeoutMs : UInt32
  private active : IO.Ref (Std.HashMap String FramedConnection)

def BackendConnections.new (owners : OwnerRegistry) (root : System.FilePath)
    (programs : Array BackendProgram) (timeoutMs : UInt32) : IO BackendConnections :=
  return ⟨owners, root, programs, timeoutMs, ← IO.mkRef {}⟩

opaque BackendConnections.close (connections : BackendConnections) : IO Unit := do
  for (_, wire) in (← connections.active.get).toList do wire.close
  connections.active.set {}

/-- Start and negotiate a declared backend at its first use. A closed process is not restarted. -/
def BackendConnections.get (connections : BackendConnections) (backend : String) :
    MetaM FramedConnection := do
  if let some wire := (← connections.active.get)[backend]? then return wire
  let some program := connections.programs.find? (·.name == backend)
    | do
      let error := PortError.unavailable backend "not declared in the manifest"
      throwStratum error.stratum error.render
  let portPython ← IO.FS.realPath ((← packageDir contractPackage) / "python")
  let path := match ← IO.getEnv "PYTHONPATH" with
    | some inherited => s!"{portPython}:{inherited}"
    | none => portPython.toString
  let started ← FramedConnection.start connections.owners backend {
    cmd := program.command, args := program.args, cwd := some connections.root
    env := #[("PYTHONPATH", some path)] } connections.timeoutMs
  match started with
  | .error error => throwStratum error.stratum error.render
  | .ok wire =>
    connections.active.modify (·.insert backend wire)
    return wire

/-- Resolve the original supplying generation of a retained export. -/
def BackendConnections.ofOwner (connections : BackendConnections) (owner : ConnectionGeneration) :
    MetaM FramedConnection := do
  for (_, wire) in (← connections.active.get).toList do
    if wire.connection.generation == owner then return wire
  throwStratum .unavailable "stale_owner"

end CasRuntime
