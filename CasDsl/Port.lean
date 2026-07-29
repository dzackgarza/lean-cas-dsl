/-
Generic framed child-process port (DESIGN.md §The port and the Sage adapter).

Mirrors the worker's framing discipline: a frame is the ASCII decimal byte
length of the payload, `\n`, then that many bytes of UTF-8 JSON. Length
prefixing (not newline-delimited JSON) means an adapter's own chatter can
never be mistaken for a frame; stderr is inherited and is the adapter's log
stream, never framed.

This module knows no backend operations — no Sage, no op ids, no value
shapes. It moves `Json` and reports `ExecError`. A single caller owns a
connection, so a reply whose `request_id` does not match the outstanding
request is a protocol error rather than a stashed stray: an adapter that
answers the wrong question must not be able to answer it quietly.
-/
import Lean
import CasDsl.Category

namespace CasDsl

open Lean (Json Name toJson)

/-- Discovery + identity of a backend process. `label` is the backend name
that appears in this port's `ExecError`s. -/
structure PortConfig where
  cmd : String
  args : Array String := #[]
  label : Name
  deriving Inhabited

/-- The child's stdio shape: framed control traffic on stdin/stdout, stderr
inherited (the adapter's logs go to the kernel's stderr). -/
abbrev PortStdio : IO.Process.StdioConfig :=
  { stdin := .piped, stdout := .piped, stderr := .inherit }

/-- What the adapter declared in its unsolicited ready frame. -/
structure PortReady where
  protocol : Nat
  backend : String
  backendVersion : String
  adapterVersion : String
  capabilities : Array String
  deriving Repr, Inhabited

structure PortConn where
  child : IO.Process.Child PortStdio
  label : Name
  ready : PortReady
  /-- Monotonic request ids; wire bookkeeping, never semantic state. -/
  nextId : IO.Ref Nat

namespace Port

/-- The protocol version this port speaks. -/
def protocolVersion : Nat := 1

def writeFrame (h : IO.FS.Handle) (j : Json) : IO Unit := do
  let bytes := j.compress.toUTF8
  h.putStr s!"{bytes.size}\n"
  h.write bytes
  h.flush

/-- A single `read` may return fewer bytes than asked for; `none` on EOF
before `n` bytes arrived. -/
private partial def readExact (h : IO.FS.Handle) (n : Nat) (acc : ByteArray) :
    IO (Option ByteArray) := do
  if acc.size ≥ n then
    return some acc
  let chunk ← h.read (USize.ofNat (n - acc.size))
  if chunk.size == 0 then
    return none
  readExact h n (acc ++ chunk)

/-- Read one frame. This port only reads when a frame is owed, so EOF at a
frame boundary is as much a protocol failure as EOF inside one. -/
def readFrame (label : Name) (h : IO.FS.Handle) : IO (Except ExecError Json) := do
  try
    let line ← h.getLine
    if line.isEmpty then
      return .error (.protocolError s!"{label}: adapter closed its output stream")
    let some n := line.trimAscii.toNat?
      | return .error (.protocolError s!"{label}: bad frame length {repr line}")
    let some bytes ← readExact h n .empty
      | return .error (.protocolError s!"{label}: EOF mid-frame (wanted {n} bytes)")
    let some payload := String.fromUTF8? bytes
      | return .error (.protocolError s!"{label}: frame is not valid UTF-8")
    match Json.parse payload with
    | .ok j => return .ok j
    | .error e => return .error (.protocolError s!"{label}: bad JSON frame: {e}")
  catch e =>
    return .error (.protocolError s!"{label}: cannot read from adapter: {e}")

private def strAt (label : Name) (j : Json) (k : String) : Except ExecError String :=
  match j.getObjVal? k >>= (·.getStr?) with
  | .ok s => .ok s
  | .error _ =>
      .error (.protocolError s!"{label}: field '{k}' missing or not a string in {j.compress}")

private def natAt (label : Name) (j : Json) (k : String) : Except ExecError Nat :=
  match j.getObjVal? k >>= (·.getNat?) with
  | .ok n => .ok n
  | .error _ =>
      .error (.protocolError s!"{label}: field '{k}' missing or not a number in {j.compress}")

private def strArrAt (label : Name) (j : Json) (k : String) :
    Except ExecError (Array String) :=
  match j.getObjVal? k >>= (·.getArr?) with
  | .ok items => items.mapM fun i =>
      match i.getStr? with
      | .ok s => .ok s
      | .error _ =>
          .error (.protocolError s!"{label}: field '{k}' must hold strings in {j.compress}")
  | .error _ =>
      .error (.protocolError s!"{label}: field '{k}' missing or not an array in {j.compress}")

private def readyOf (label : Name) (j : Json) : Except ExecError PortReady := do
  let op ← strAt label j "op"
  if op != "ready" then
    .error (.protocolError s!"{label}: expected a ready frame, got op {repr op}")
  else
    let protocol ← natAt label j "protocol"
    if protocol != protocolVersion then
      .error (.protocolError
        s!"{label}: adapter speaks protocol {protocol}, this port speaks {protocolVersion}")
    else
      return {
        protocol
        backend := ← strAt label j "backend"
        backendVersion := ← strAt label j "backend_version"
        adapterVersion := ← strAt label j "adapter_version"
        capabilities := ← strArrAt label j "capabilities"
      }

/-- Terminate a child we are abandoning; reap it so it cannot linger. -/
private def abort {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO Unit := do
  try child.kill catch _ => pure ()
  try discard child.wait catch _ => pure ()

/-- Spawn the backend and consume its ready frame. A missing binary is
`backendUnavailable` (selection already happened — this is not retried
elsewhere); a malformed or wrong-version handshake is a `protocolError` and
the child is killed rather than left half-spoken-to. -/
def start (cfg : PortConfig) : IO (Except ExecError PortConn) := do
  let spawned : Except ExecError (IO.Process.Child PortStdio) ←
    try
      let child ← IO.Process.spawn
        { toStdioConfig := PortStdio, cmd := cfg.cmd, args := cfg.args }
      pure (.ok child)
    catch e =>
      pure (.error (.backendUnavailable cfg.label s!"cannot spawn '{cfg.cmd}': {e}"))
  match spawned with
  | .error e => return .error e
  | .ok child =>
    match ← readFrame cfg.label child.stdout with
    | .error e => abort child; return .error e
    | .ok frame =>
      match readyOf cfg.label frame with
      | .error e => abort child; return .error e
      | .ok ready =>
        let nextId ← IO.mkRef 1
        return .ok { child, label := cfg.label, ready, nextId }

private def ofExcept {α : Type} (x : Except ExecError α) : ExceptT ExecError IO α :=
  ExceptT.mk (pure x)

/-- Explicit lift: inside `ExceptT ExecError IO`, `try`/`catch` handles
`ExecError`, so IO exceptions must be caught in the inner `IO` block. -/
private def liftIO {α : Type} (x : IO α) : ExceptT ExecError IO α := ExceptT.lift x

/-- Send one request and read its reply. -/
def call (c : PortConn) (op : String) (args : Json) : IO (Except ExecError Json) :=
  ExceptT.run do
    let id ← liftIO <| c.nextId.modifyGet fun n => (n, n + 1)
    let sent : Option ExecError ← liftIO do
      try
        writeFrame c.child.stdin
          (Json.mkObj [("request_id", toJson id), ("op", op), ("args", args)])
        pure none
      catch e =>
        pure (some (ExecError.protocolError s!"{c.label}: cannot send op {repr op}: {e}"))
    if let some e := sent then throw e
    let reply ← ofExcept (← liftIO (readFrame c.label c.child.stdout))
    let rid ← ofExcept (natAt c.label reply "request_id")
    if rid != id then
      throw (.protocolError
        s!"{c.label}: reply carries request_id {rid}, expected {id}")
    match ← ofExcept (strAt c.label reply "status") with
    | "ok" =>
        match reply.getObjVal? "value" with
        | .ok v => return v
        | .error _ =>
            throw (.protocolError s!"{c.label}: ok reply without a value: {reply.compress}")
    | "error" =>
        let kind ← ofExcept (strAt c.label reply "kind")
        let message ← ofExcept (strAt c.label reply "message")
        throw (.backendError c.label kind message)
    | "unsupported" =>
        throw (.backendError c.label "unsupported"
          s!"{c.ready.backend} does not implement op {repr op}")
    | other =>
        throw (.protocolError s!"{c.label}: unknown reply status {repr other}")

private partial def waitOrKill {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg) (tries : Nat) : IO Unit := do
  if tries == 0 then
    abort child
  else
    match ← child.tryWait with
    | some _ => pure ()
    | none => IO.sleep 20; waitOrKill child (tries - 1)

/-- Closing stdin is the clean-shutdown signal; the grace window then bounds
how long a wedged adapter may hold the kernel. -/
def stop (c : PortConn) : IO Unit := do
  -- The extracted handle is never used again, so the pipe closes here and
  -- the adapter reads EOF.
  let (_stdin, child) ← c.child.takeStdin
  waitOrKill child 50

end Port

end CasDsl
