module

public import Std.Sync.Mutex
public import Std.Data.HashMap
public import Init.System.IO

public section

namespace CasRuntime

structure ConnectionGeneration where
  private mk ::
  worker : String
  serial : Nat
  deriving BEq, Hashable, Repr

abbrev ConnectedChild := IO.Process.Child {
  stdin := .piped, stdout := .piped, stderr := .inherit }

/-- A generation and channels from the same actual process. -/
structure Connection where
  private mk ::
  generation : ConnectionGeneration
  child : ConnectedChild
  exited : Task (Except IO.Error UInt32)

private structure OwnerState where
  nextSerial : Nat := 0
  live : Std.HashMap Nat ConnectedChild := {}

/-- Live process state belongs to the worker, independently of semantic snapshots. -/
structure OwnerRegistry where
  private mk ::
  worker : String
  private state : Std.Mutex OwnerState

private def retire (owners : OwnerRegistry) (generation : ConnectionGeneration) : BaseIO Unit :=
  owners.state.atomically do
    modify fun state => { state with live := state.live.erase generation.serial }

/-- Linux supplies the fresh worker identifier; generation serials never decrease.
The UUID stream is documented in Linux Documentation/admin-guide/sysctl/kernel.rst, `random`. -/
opaque OwnerRegistry.new : IO OwnerRegistry := do
  let worker := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
  if worker.isEmpty then throw <| IO.userError "the kernel supplied an empty worker identifier"
  return ⟨worker, ← Std.Mutex.new {}⟩

/-- Stamp the supplying process before any reply can be admitted.
Uses Lean v4.33.0 `IO.Process` and `Std.Mutex`; process waits run outside the mutex. -/
opaque OwnerRegistry.spawn (owners : OwnerRegistry) (arguments : IO.Process.SpawnArgs) :
    IO Connection := do
  let child : ConnectedChild ← IO.Process.spawn {
    arguments with stdin := .piped, stdout := .piped, stderr := .inherit }
  let generation ← owners.state.atomically do
    let state ← get
    let generation : ConnectionGeneration := ⟨owners.worker, state.nextSerial⟩
    let next : OwnerState := {
      nextSerial := state.nextSerial + 1
      live := state.live.insert generation.serial child }
    set next
    return generation
  let exited ← IO.asTask (prio := .dedicated) do
    try child.wait
    finally retire owners generation
  return ⟨generation, child, exited⟩

/-- Read the supervisor's liveness state, without contacting the engine. -/
opaque OwnerRegistry.isLive (owners : OwnerRegistry) (generation : ConnectionGeneration) :
    BaseIO Bool := do
  if generation.worker != owners.worker then return false
  owners.state.atomically do
    return (← get).live.contains generation.serial

/-- Owner-free data remain available. Captured owner sets must all remain live. -/
def OwnerRegistry.allAlive (owners : OwnerRegistry) (generations : Array ConnectionGeneration) :
    BaseIO Bool :=
  generations.allM owners.isLive

/-- Revoke the generation before terminating its process. Repeated cleanup is inert. -/
opaque OwnerRegistry.close (owners : OwnerRegistry) (generation : ConnectionGeneration) : IO Unit := do
  if generation.worker != owners.worker then
    throw <| IO.userError "connection cleanup belongs to a different worker"
  let child ← owners.state.atomically do
    let state ← get
    if generation.serial ≥ state.nextSerial then
      throw <| IO.userError "connection cleanup names an unallocated generation"
    let child := state.live[generation.serial]?
    set { state with live := state.live.erase generation.serial }
    return child
  if let some child := child then child.kill

end CasRuntime
