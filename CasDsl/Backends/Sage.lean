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
import CasDsl.Register

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

/-- Unreachable when the op-signature invariant holds: `addRouteChecked`
refuses any route whose pattern this op's declared signature does not
accept, so an executor only ever sees receivers matching its signature.
Reaching this therefore means the SIGNATURE registration below misstates
the encoder — a defect in this module, reported as such. -/
private def offSignature (op : String) (o : Obj) : ExecError :=
  .protocolError s!"sage: op {repr op} received {o.presentation}, which its \
declared signature excludes — the signature registration is defective"

/-- Rationals on the wire. An integer entry is sent as its exact image in ℚ
(the ℤ ⊆ ℚ inclusion), never rounded or reinterpreted. -/
private def ratArg (v : Value) : Except ExecError Json :=
  match v with
  | .rat q => .ok (Codec.valueToJson (.rat q))
  | .int z => .ok (Codec.valueToJson (.rat (mkRat z 1)))
  | other => .error (.badRequest s!"expected a rational, got {other.render}")

private def factorIntArgs : Obj → Except ExecError Json
  | .elem .int (.int z) => .ok (Json.mkObj [("n", toString z)])
  | o => .error (offSignature "factor_int" o)

private def factorPolyQArgs : Obj → Except ExecError Json
  | .elem (.poly .rat) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM ratArg))]
  | o => .error (offSignature "factor_poly_q" o)

/-- Integer coefficients on the wire, exactly as carried. -/
private def intArg (v : Value) : Except ExecError Json :=
  match v with
  | .int z => .ok (Codec.valueToJson (.int z))
  | other => .error (.badRequest s!"expected an integer, got {other.render}")

private def factorPolyZArgs : Obj → Except ExecError Json
  | .elem (.poly .int) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM intArg))]
  | o => .error (offSignature "factor_poly_z" o)

private def matQArgs (op : String) : Obj → Except ExecError Json
  | .elem (.matrix _ .rat) (.mat _ _ rows) => do
      let rs ← rows.mapM fun row => return Json.arr (← row.mapM ratArg)
      return Json.mkObj [("rows", Json.arr rs)]
  | o => .error (offSignature op o)

/-- `gcd_int` is the one shipped op with an ARGUMENT, and the argument is
validated here (this slice validates arguments at execution): the receiver's
shape is the routed invariant, but neither the argument's shape nor the
COUNT is — `OpSig` constrains receivers only, so a method declared with the
wrong arity would reach an executor unchecked. -/
private def gcdIntArgs (receiver : Obj) (args : Array Obj) : Except ExecError Json :=
  match receiver, args with
  | .elem .int (.int a), #[.elem _ (.int b)] =>
      .ok (Json.mkObj [("a", toString a), ("b", toString b)])
  | .elem .int (.int _), #[o] => .error (.badRequest
      s!"sage op \"gcd_int\" expects an integer argument, got {o.presentation}")
  | .elem .int (.int _), as => .error (.badRequest
      s!"sage op \"gcd_int\" takes one argument, got {as.size}")
  | o, _ => .error (offSignature "gcd_int" o)

private def rootsPolyZArgs : Obj → Except ExecError Json
  | .elem (.poly .int) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM intArg))]
  | o => .error (offSignature "roots_poly_z" o)

private def rootsPolyQArgs : Obj → Except ExecError Json
  | .elem (.poly .rat) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM ratArg))]
  | o => .error (offSignature "roots_poly_q" o)

/-- The decoded reply must be the kind of value the op promises; a
well-formed value of the wrong kind is an adapter defect, not a result. -/
private def expectKind (op : String) (v : Value) : Except ExecError Value :=
  match op, v with
  | "factor_int", .factorization .. => .ok v
  | "factor_poly_q", .factorization .. => .ok v
  | "factor_poly_z", .factorization .. => .ok v
  | "mat_det_q", .rat _ => .ok v
  | "mat_inv_q", .mat .. => .ok v
  | "gcd_int", .int _ => .ok v
  -- the EMPTY set is the honest answer for a polynomial with no root in its
  -- own coefficient ring (x² − 2 over ℚ), so it is a result like any other
  | "roots_poly_z", .setV .. => .ok v
  | "roots_poly_q", .setV .. => .ok v
  | _, _ =>
      .error (.protocolError
        s!"sage: op {repr op} returned {v.render}, which is not the value kind it promises")

/-- The registered `sage` executor. -/
def executor : Executor := fun opId receiver args => do
  -- DEFAULT-DENY on arguments: every op takes its receiver alone unless it is
  -- named here, so an op added later rejects a stray argument instead of
  -- silently dropping it. A defective method declaration is reported.
  if !args.isEmpty && opId != "gcd_int" then
    return .error (.badRequest s!"sage op {repr opId} takes no arguments, got {args.size}")
  let payload : Except ExecError Json :=
    match opId with
    | "factor_int" => factorIntArgs receiver
    | "factor_poly_q" => factorPolyQArgs receiver
    | "factor_poly_z" => factorPolyZArgs receiver
    | "mat_det_q" => matQArgs "mat_det_q" receiver
    | "mat_inv_q" => matQArgs "mat_inv_q" receiver
    | "roots_poly_z" => rootsPolyZArgs receiver
    | "roots_poly_q" => rootsPolyQArgs receiver
    | "gcd_int" => gcdIntArgs receiver args
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

/-- The receiver signatures of the sage ops, restated from the encoders
above as checked registration data (see `OpSig`). -/
private def sageOpSigs : Array OpSig := #[
  { backend := `sage, opId := "factor_int", accepts := #[.elemOf (.exact .int)] },
  { backend := `sage, opId := "factor_poly_q",
    accepts := #[.elemOf (.polyOver (.exact .rat))] },
  { backend := `sage, opId := "factor_poly_z",
    accepts := #[.elemOf (.polyOver (.exact .int))] },
  { backend := `sage, opId := "mat_det_q",
    accepts := #[.elemOf (.matrixOver (.exact .rat))] },
  { backend := `sage, opId := "mat_inv_q",
    accepts := #[.elemOf (.matrixOver (.exact .rat))] },
  { backend := `sage, opId := "gcd_int", accepts := #[.elemOf (.exact .int)] },
  { backend := `sage, opId := "roots_poly_z",
    accepts := #[.elemOf (.polyOver (.exact .int))] },
  { backend := `sage, opId := "roots_poly_q",
    accepts := #[.elemOf (.polyOver (.exact .rat))] }
]

run_cmd sageOpSigs.forM registerOpSig!

end CasDsl.Sage
