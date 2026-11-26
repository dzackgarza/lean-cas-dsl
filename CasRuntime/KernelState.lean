module

public import CasRuntime.Closure
public import CasRuntime.Realization
public import CasRuntime.BackendConnections
public import CasRuntime.ManifestAdmission
public import CasRuntime.Occurrence
public import CasTools.Diagnostics

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- The worker's computational kernel: the frozen manifest and realization profile, the live
negotiated connections and the code of retained closures.
Source: execution contract v2 §1 and §2, lean-cas-dsl#69 comment 6664277464. -/
structure Kernel where
  private mk ::
  ledger : OccurrenceLedger
  manifest : Manifest
  manifestDigest : String
  profile : RealizationProfile
  timeoutMs : UInt32
  /-- Registrations of the manifest that name no published operation or declared backend. -/
  rejected : Array String
  connections : BackendConnections
  codes : IO.Ref (Std.HashMap (RuntimeId .program) ClosureCode)
  /-- The registrations actually dispatched, in order. An observation, not evidence. -/
  dispatches : IO.Ref (Array Registration)
  /-- Inert session diagnostics, separate from source and runtime authority. -/
  log : CasTools.ApplicationLog

/-- Read and freeze the manifest and profile before any invocation. No process starts here.
Without a manifest no leaf is installed. A registration is admitted when its operation is the
address of a published family and its backend is declared. Rejections are reported, and a
rejected registration is never selected. -/
opaque Kernel.load (owners : OwnerRegistry) (manifest : Option System.FilePath)
    (profile : Option Json) (timeoutMs : UInt32) : MetaM Kernel := do
  let (root, text) ← match manifest with
    | some path => pure (path.parent.getD ".", ← IO.FS.readFile path)
    | none => pure (".", "{}")
  let parsed ← IO.ofExcept <| (Json.parse text >>= Manifest.parse).mapError IO.userError
  let (installed, rejected) ← admitManifest parsed
  let digest ← sha256Hex text
  let selectedProfile ← RealizationProfile.prepare installed profile
  let log ← CasTools.ApplicationLog.new owners.identities.worker <| Json.mkObj [
    ("manifest", toJson (manifest.map (·.toString))), ("manifestDigest", toJson digest),
    ("profileDigest", toJson selectedProfile.sha256), ("rejected", toJson rejected)]
  return ⟨← OccurrenceLedger.new owners, installed, digest,
    selectedProfile, timeoutMs, rejected,
    ← BackendConnections.new owners root installed.backends timeoutMs,
    ← IO.mkRef {}, ← IO.mkRef #[], log⟩

/-- Branch preparation copies the retained code table. A committed
parent is never mutated by a child cell; occurrence/connection authority and
dispatch observations remain shared resource state. -/
def Kernel.fork (kernel : Kernel) : BaseIO Kernel := do
  return { kernel with codes := ← IO.mkRef (← kernel.codes.get) }

/-- Close every started process and invalidate its generation. -/
opaque Kernel.close (kernel : Kernel) : IO Unit := do
  try kernel.connections.close
  finally
    discard <| kernel.log.write #[] "session.resourcesClosed" (Json.mkObj [])

end CasRuntime
