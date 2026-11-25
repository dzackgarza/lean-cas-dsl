module

public import CasRuntime.Connection
public import CasRuntime.Transaction
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
  private starting : IO.Ref (Std.HashMap String (RuntimeId .transaction × Connection))

def BackendConnections.new (owners : OwnerRegistry) (root : System.FilePath)
    (programs : Array BackendProgram) (timeoutMs : UInt32) : IO BackendConnections :=
  return ⟨owners, root, programs, timeoutMs, ← IO.mkRef {}, ← IO.mkRef {}⟩

opaque BackendConnections.close (connections : BackendConnections) : IO Unit := do
  for (_, wire) in (← connections.active.get).toList do wire.close
  connections.active.set {}
  for (_, (_, connection)) in (← connections.starting.get).toList do
    connections.owners.close connection.generation
  connections.starting.set {}

/-- Observe exact surviving leases without retaining staging or a reply payload. -/
opaque BackendConnections.transactionBusy (connections : BackendConnections)
    (transaction : RuntimeId .transaction) : BaseIO Bool := do
  if (← connections.starting.get).any (fun _ entry => entry.1 == transaction) then return true
  for (_, wire) in (← connections.active.get).toList do
    if ← wire.transactionBusy transaction then return true
  return false

/-- Explicit force invalidates precisely the generations with unfinished target leases.
Other generations remain installed; a closed supplying generation is never restarted. -/
opaque BackendConnections.forceTransaction (connections : BackendConnections)
    (transaction : RuntimeId .transaction) : IO (Array ConnectionGeneration) := do
  let mut invalidated := #[]
  for (_, (target, connection)) in (← connections.starting.get).toList do
    if target == transaction && (← connections.owners.closeIfLive connection.generation) then
      invalidated := invalidated.push connection.generation
  for (_, wire) in (← connections.active.get).toList do
    if ← wire.forceTransaction transaction then
      unless invalidated.contains wire.connection.generation do
        invalidated := invalidated.push wire.connection.generation
  return invalidated

/-- Start and negotiate a declared backend at its first use. A closed process is not restarted. -/
def BackendConnections.get (connections : BackendConnections) (transaction : CellTransaction)
    (backend : String) : MetaM FramedConnection := do
  unless (← transaction.status) matches .active do
    throwStratum .unavailable "cancelled"
  if let some wire := (← connections.active.get)[backend]? then return wire
  let some program := connections.programs.find? (·.name == backend)
    | do
      let error := PortError.unavailable backend "not declared in the manifest"
      throwStratum error.stratum error.render
  let portPython ← IO.FS.realPath ((← packageDir contractPackage) / "python")
  let path := match ← IO.getEnv "PYTHONPATH" with
    | some inherited => s!"{portPython}:{inherited}"
    | none => portPython.toString
  try
    let started ← FramedConnection.start connections.owners backend {
      cmd := program.command, args := program.args, cwd := some connections.root
      env := #[("PYTHONPATH", some path)] } connections.timeoutMs
        (fun connection => do
          connections.starting.modify (·.insert backend (transaction.id, connection))
          return (← transaction.status) matches .active)
        (some transaction.id)
    match started with
    | .error error => throwStratum error.stratum error.render
    | .ok wire =>
      connections.active.modify (·.insert backend wire)
      unless (← transaction.status) matches .active do
        wire.close
        throwStratum .unavailable "cancelled"
      return wire
  finally connections.starting.modify (·.erase backend)

/-- Resolve the original supplying generation of a retained export. -/
def BackendConnections.ofOwner (connections : BackendConnections) (owner : ConnectionGeneration) :
    MetaM FramedConnection := do
  for (_, wire) in (← connections.active.get).toList do
    if wire.connection.generation == owner then return wire
  throwStratum .unavailable "stale_owner"

end CasRuntime
