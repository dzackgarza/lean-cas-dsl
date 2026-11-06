module

public import Std.Sync.Mutex
public import Init.System.IO

public section

namespace CasRuntime

inductive IdentityKind
  | connection | program | occurrence | value | transaction

/-- Resource kinds share a serial supply but remain distinct Lean types. -/
structure RuntimeId (kind : IdentityKind) where
  private mk ::
  worker : String
  serial : Nat
  deriving BEq, Hashable, Repr

/-- The worker retains this supply outside immutable semantic snapshots. -/
structure IdentitySupply where
  private mk ::
  worker : String
  private nextSerial : Std.Mutex Nat

/-- Linux supplies a fresh worker nonce.
Reference: Linux Documentation/admin-guide/sysctl/kernel.rst, `random`. -/
opaque IdentitySupply.new : IO IdentitySupply := do
  let worker := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
  if worker.isEmpty then throw <| IO.userError "the kernel supplied an empty worker identifier"
  return ⟨worker, ← Std.Mutex.new 0⟩

/-- Allocate before normalization or dispatch. Only the native atomic section advances the counter.
Reference: Lean v4.33.0 Std/Sync/Mutex.lean, `Mutex.atomically`. -/
opaque IdentitySupply.fresh (supply : IdentitySupply) (kind : IdentityKind) :
    BaseIO (RuntimeId kind) :=
  supply.nextSerial.atomically do
    let serial ← get
    set (serial + 1)
    return ⟨supply.worker, serial⟩

end CasRuntime
