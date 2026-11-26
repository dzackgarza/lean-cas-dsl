module

public import Lean
public import Std.Sync.Mutex
public import CasTools.JsonGraph

public section

namespace CasTools

open Lean

/-- One append-only diagnostic stream. It owns no source selection, value or execution
authority. The native mutex keeps concurrent event lines and their sequence numbers together. -/
structure ApplicationLog where
  private mk ::
  path : System.FilePath
  session : String
  private output : IO.FS.Handle
  private next : Std.Mutex Nat

/-- Flush a complete JSON event before returning. A failed log write remains an IO failure;
it is never reported as a successful recorded event. -/
def ApplicationLog.write (log : ApplicationLog) (parents : Array Nat)
    (event : String) (data : Json) : IO Nat :=
  log.next.atomically do
    let sequence ← get
    let row := Json.mkObj [
      ("schema", toJson (2 : Nat)), ("session", toJson log.session),
      ("sequence", toJson sequence), ("parents", toJson parents),
      ("monotonicMilliseconds", toJson (← IO.monoMsNow)),
      ("event", toJson event), ("data", JsonGraph.encode data)]
    log.output.putStrLn row.compress
    log.output.flush
    set (sequence + 1)
    return sequence

/-- Linux supplies an independent diagnostic nonce, so logging does not allocate or change
any semantic identity. The feedback runner places the stream inside its durable run directory. -/
def ApplicationLog.new (worker : String) (metadata : Json) : IO ApplicationLog := do
  let nonce := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
  if nonce.isEmpty then throw <| IO.userError "the kernel supplied an empty diagnostic identifier"
  let directory : System.FilePath :=
    (← IO.getEnv "CAS_APPLICATION_LOG_DIR").getD "timing/application"
  IO.FS.createDirAll directory
  let path := directory / s!"{nonce}.jsonl"
  let log : ApplicationLog := ⟨path, nonce, ← IO.FS.Handle.mk path .append,
    ← Std.Mutex.new 0⟩
  discard <| log.write #[] "session.started" <| Json.mkObj [
    ("worker", toJson worker), ("leanVersion", toJson Lean.versionString),
    ("feedbackRun", toJson (← IO.getEnv "CAS_FEEDBACK_RUN")),
    ("feedbackContext", toJson (← IO.getEnv "CAS_FEEDBACK_CONTEXT")),
    ("feedbackWorker", toJson (← IO.getEnv "CAS_FEEDBACK_WORKER")),
    ("metadata", metadata)]
  return log

/-- Decode only the event-local diagnostic transport. Public request observations and
their complete native fields retain their original expanded JSON schema. Old streams remain
readable; an unknown version or malformed graph is an error, never a partial event. -/
def ApplicationLog.decodeEvent (event : Json) : Except String Json := do
  match ← event.getObjValAs? Nat "schema" with
  | 1 => pure event
  | 2 =>
    let data ← JsonGraph.decode (← event.getObjVal? "data")
    pure (event.setObjVal! "data" data)
  | _ => throw "an application log has an unsupported stream schema"

/-- Read a durable diagnostic stream one complete line at a time, restoring shared
immutable JSON values. Independent provider traffic uses its own protocol reader. -/
def ApplicationLog.readEvents (path : System.FilePath) : IO (Array Json) :=
  IO.FS.withFile path .read fun input => do
    let mut events := #[]
    repeat
      let line ← input.getLine
      if line.isEmpty then break
      if line.trimAscii.toString.isEmpty then continue
      let event ← IO.ofExcept <| (Json.parse line).mapError IO.userError
      let event ← IO.ofExcept <| (ApplicationLog.decodeEvent event).mapError IO.userError
      events := events.push event
    return events

namespace Diagnostics

/-- Scope travels in the native elaborator environment, which already isolates concurrent
sessions and saved-state branches. The shared sink records observations only. -/
structure Scope where
  log : ApplicationLog
  parents : Array Nat := #[]

private initialize scopeExtension : EnvExtension (Option Scope) ←
  registerEnvExtension (pure none)

def current? : CoreM (Option Scope) :=
  return scopeExtension.getState (← getEnv)

/-- Restore only the diagnostic scope. Declarations and other native state produced by
the computation remain intact. -/
def withScope [Monad m] [MonadLiftT CoreM m] [MonadFinally m]
    (scope : Scope) (action : m α) : m α := do
  let previous ← liftM (m := CoreM) current?
  liftM (m := CoreM) <| modifyEnv (scopeExtension.setState · (some scope))
  try action
  finally
    liftM (m := CoreM) <| modifyEnv (scopeExtension.setState · previous)

/-- Emit structured data only into the active session's file, without a user message. -/
def emit (event : String) (data : Json) : CoreM Unit := do
  let some scope ← current? | return ()
  discard <| scope.log.write scope.parents event data

/-- Preserve existing native diagnostic details in the same ordered stream. Formatting is
performed only for an active logged session and never supplies mathematical interpretation. -/
def message (detail : MessageData) : CoreM Unit := do
  let some scope ← current? | return ()
  discard <| scope.log.write scope.parents "diagnostic"
    (Json.mkObj [("message", toJson (← detail.toString))])

end Diagnostics
end CasTools
