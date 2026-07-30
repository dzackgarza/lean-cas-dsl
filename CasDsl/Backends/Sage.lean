/-
The direct Sage adapter, Lean side (DESIGN.md decision 2: Sage is reached by
a direct adapter and brokers nothing else).

This module owns the translation between a routed `(opId, receiver)` and the
wire ops the Python half implements. It never generates Sage source, and
a receiver whose presentation does not fit the op is a `badRequest` — routes
are supposed to prevent that, and if one does not, the caller learns so
instead of getting a silently reinterpreted request.
-/
import CasDsl.Port
import CasDsl.Codec
import CasDsl.Route

namespace CasDsl.Sage

open Lean (Json Name toJson)

/-- The live adapter process.

A NON-SEMANTIC process cache, exempt from the plugin state law exactly like
the worker's output sink: it holds a pipe, not a registration a notebook can
observe. Replays re-execute their backend calls; nothing about the session's
meaning is stored here. -/
initialize sageConnRef : IO.Ref (Option PortConn) ← IO.mkRef none

/-- Adapter discovery (DESIGN.md): `CASDSL_SAGE`, `CASDSL_ADAPTER`. The
adapter path is relative to the worker's cwd, which is the project root. -/
def config : IO PortConfig := do
  let cmd := (← IO.getEnv "CASDSL_SAGE").getD "sage"
  let adapter := (← IO.getEnv "CASDSL_ADAPTER").getD "backends/sage_adapter.py"
  return { cmd, args := #["-python", adapter], label := `sage }

/-- The cached connection, starting the adapter on first use. -/
def connect : IO (Except ExecError PortConn) := do
  match ← sageConnRef.get with
  | some c => return .ok c
  | none =>
    match ← Port.start (← config) with
    | .error e => return .error e
    | .ok c =>
      sageConnRef.set (some c)
      return .ok c

/-- `(backend version, adapter version)` of the running adapter, for
diagnostics. `none` until something has actually connected. -/
def provenance : IO (Option (String × String)) := do
  return (← sageConnRef.get).map fun c => (c.ready.backendVersion, c.ready.adapterVersion)

/-- Shut the adapter down and forget it. -/
def disconnect : IO Unit := do
  if let some c ← sageConnRef.get then
    Port.stop c
    sageConnRef.set none

/-- Rationals on the wire. An integer entry is sent as its exact image in ℚ
(the ℤ ⊆ ℚ inclusion), never rounded or reinterpreted. -/
private def ratArg (v : Value) : Except ExecError Json :=
  match v with
  | .rat q => .ok (Codec.valueToJson (.rat q))
  | .int z => .ok (Codec.valueToJson (.rat (mkRat z 1)))
  | other => .error (.badRequest s!"expected a rational, got {other.render}")

private def factorIntArgs : Obj → Except ExecError Json
  | .elem .int (.int z) => .ok (Json.mkObj [("n", toString z)])
  | o => .error (.badRequest s!"factor_int expects an integer element, got {o.presentation}")

private def factorPolyQArgs : Obj → Except ExecError Json
  | .elem (.poly .rat) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM ratArg))]
  | o => .error (.badRequest s!"factor_poly_q expects an element of ℚ[x], got {o.presentation}")

/-- Integer coefficients on the wire, exactly as carried. -/
private def intArg (v : Value) : Except ExecError Json :=
  match v with
  | .int z => .ok (Codec.valueToJson (.int z))
  | other => .error (.badRequest s!"expected an integer, got {other.render}")

private def factorPolyZArgs : Obj → Except ExecError Json
  | .elem (.poly .int) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM intArg))]
  | o => .error (.badRequest s!"factor_poly_z expects an element of ℤ[x], got {o.presentation}")

private def matQArgs (op : String) : Obj → Except ExecError Json
  | .elem (.matrix _ .rat) (.mat _ _ rows) => do
      let rs ← rows.mapM fun row => return Json.arr (← row.mapM ratArg)
      return Json.mkObj [("rows", Json.arr rs)]
  | o => .error (.badRequest s!"{op} expects a matrix over ℚ, got {o.presentation}")

/-- The decoded reply must be the kind of value the op promises; a
well-formed value of the wrong kind is an adapter defect, not a result. -/
private def expectKind (op : String) (v : Value) : Except ExecError Value :=
  match op, v with
  | "factor_int", .factorization .. => .ok v
  | "factor_poly_q", .factorization .. => .ok v
  | "factor_poly_z", .factorization .. => .ok v
  | "mat_det_q", .rat _ => .ok v
  | "mat_inv_q", .mat .. => .ok v
  | _, _ =>
      .error (.protocolError
        s!"sage: op {repr op} returned {v.render}, which is not the value kind it promises")

/-- The registered `sage` executor. -/
def executor : Executor := fun opId receiver args => do
  if !args.isEmpty then
    return .error (.badRequest s!"sage op {repr opId} takes no arguments, got {args.size}")
  let payload : Except ExecError Json :=
    match opId with
    | "factor_int" => factorIntArgs receiver
    | "factor_poly_q" => factorPolyQArgs receiver
    | "factor_poly_z" => factorPolyZArgs receiver
    | "mat_det_q" => matQArgs "mat_det_q" receiver
    | "mat_inv_q" => matQArgs "mat_inv_q" receiver
    | other => .error (.badRequest s!"the sage backend implements no op {repr other}")
  match payload with
  | .error e => return .error e
  | .ok args =>
    match ← connect with
    | .error e => return .error e
    | .ok conn =>
      match ← Port.call conn opId args with
      | .error e => return .error e
      | .ok reply =>
        match Codec.valueFromJson reply with
        | .error m => return .error (.protocolError s!"sage: {m}")
        | .ok v => return expectKind opId v

initialize registerExecutor `sage executor

end CasDsl.Sage
