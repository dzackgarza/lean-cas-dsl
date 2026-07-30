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

/-- A ℚ[x] receiver's coefficients — the payload every ℚ-polynomial op takes.
Three ops send it, so it is one encoder taking the op's name for the failure
rather than three copies drifting apart. -/
private def polyQArgs (op : String) : Obj → Except ExecError Json
  | .elem (.poly .rat) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM ratArg))]
  | o => .error (offSignature op o)

/-- Integer coefficients on the wire, exactly as carried. -/
private def intArg (v : Value) : Except ExecError Json :=
  match v with
  | .int z => .ok (Codec.valueToJson (.int z))
  | other => .error (.badRequest s!"expected an integer, got {other.render}")

private def factorPolyZArgs : Obj → Except ExecError Json
  | .elem (.poly .int) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM intArg))]
  | o => .error (offSignature "factor_poly_z" o)

/-- Exact algebraic coefficients on the wire. An integer or a rational rides
as itself — ℤ ⊆ ℚ ⊆ ℂ, so `map p to ℂ[x]` sends the coefficients it was
given — and a surd rides as its normal form `a + b√d`. -/
private def algArg (v : Value) : Except ExecError Json :=
  match v with
  | .int _ | .rat _ | .alg .. => .ok (Codec.valueToJson v)
  | other => .error (.badRequest s!"expected an exact number, got {other.render}")

private def polyCArgs (op : String) : Obj → Except ExecError Json
  | .elem (.poly .complex) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM algArg))]
  | o => .error (offSignature op o)

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

private def isPrimeIntArgs : Obj → Except ExecError Json
  | .elem .int (.int z) => .ok (Json.mkObj [("n", toString z)])
  | o => .error (offSignature "is_prime_int" o)

private def rootsPolyZArgs : Obj → Except ExecError Json
  | .elem (.poly .int) (.poly _ coeffs) => do
      return Json.mkObj [("coeffs", Json.arr (← coeffs.mapM intArg))]
  | o => .error (offSignature "roots_poly_z" o)

/-- The exact value to approximate, and the requested tolerance. The tolerance
is an ARGUMENT, so it is validated here (this slice validates arguments at
execution): `OpSig` constrains receivers only, exactly as it does for
`gcd_int`. -/
private def approxRealArgs (receiver : Obj) (args : Array Obj)
    : Except ExecError Json :=
  match receiver, args with
  | .elem .real v, #[.elem _ eps] => do
      return Json.mkObj [("value", ← algArg v), ("eps", ← ratArg eps)]
  -- unreachable while the surface guard holds: `Eval.approxEps?` validates the
  -- tolerance for EVERY spelling of the request, so reaching this means that
  -- guard was bypassed — a defect here, not a user error
  | .elem .real _, #[o] => .error (.protocolError
      s!"sage: approx_real received the tolerance {o.presentation}, which the \
surface guard should already have refused")
  -- unreachable for the same reason, one layer up: the method's declared
  -- arity is checked before any executor is reached
  | .elem .real _, as => .error (.protocolError
      s!"sage: approx_real received {as.size} arguments, which the arity check \
should already have refused")
  | o, _ => .error (offSignature "approx_real" o)

/-- A rational component of a reply, for the checks below. Local because the
executors' own arithmetic backend is not in this module's dependency cone —
a backend does not read another backend. -/
private def ratOf? : Value → Option Rat
  | .int z => some (Rat.ofInt z)
  | .rat q => some q
  | _ => none

/-- The characteristic polynomial of an `n × n` matrix is MONIC of degree `n`.
Checked against THIS call's receiver, like `approx_real`'s certificate: a
well-formed polynomial that is not one is a wrong answer to this call. -/
def checkCharpoly (n : Nat) (v : Value) : Except ExecError Value :=
  match v with
  | .poly _ cs =>
      if cs.size == n + 1 && (cs[n]?.bind ratOf?) == some 1 then .ok v
      else .error (.protocolError s!"sage: mat_charpoly_q returned {v.render}, \
which is not a MONIC polynomial of degree {n} — the characteristic polynomial \
of the {n}×{n} matrix it was asked about is one")
  | v => .error (.protocolError
      s!"sage: mat_charpoly_q returned {v.render}, which is not a polynomial")

/-- The companion matrix of a degree-`d` polynomial is `d × d`, its TRACE is
`−a_{d−1}/a_d` (the sum of the roots) and its DETERMINANT is `(−1)^d·a₀/a_d`
(their product). Those are invariants every one of Sage's companion LAYOUTS
shares — they are similar matrices — so checking them holds the adapter to the
mathematics without this side taking a position on a convention that is the
backend's (decision 7). Reading the whole matrix off the coefficients would be
doing the op here, and would break the moment the adapter chose a different
layout.

Both numbers are checked, because neither alone is enough: the ZERO matrix has
the right trace whenever `a_{d−1}` is 0, which SPEC.md's own cubic is. -/
def checkCompanion (coeffs : Array Value) (v : Value) : Except ExecError Value := do
  let d := coeffs.size - 1
  let .mat n _ rows := v
    | .error (.protocolError
        s!"sage: poly_companion_q returned {v.render}, which is not a matrix")
  if coeffs.size < 2 || n != d then
    .error (.protocolError s!"sage: poly_companion_q returned a {n}×{n} matrix \
for a polynomial of degree {d}: the companion matrix has the polynomial's own size")
  else
    let some rats := rows.mapM (·.mapM ratOf?)
      | .error (.protocolError
          "sage: poly_companion_q returned a matrix that is not over ℚ")
    let some lead := ratOf? coeffs[d]!
    | .error (.badRequest "the leading coefficient is not a rational")
    let some sub := ratOf? coeffs[d - 1]!
    | .error (.badRequest "the second coefficient is not a rational")
    let some const := ratOf? coeffs[0]!
    | .error (.badRequest "the constant coefficient is not a rational")
    let trace := (Array.range n).foldl (fun acc i => acc + rats[i]![i]!) 0
    let expectTrace := -(sub / lead)
    let expectDet := (if d % 2 == 0 then 1 else -1) * const / lead
    if trace != expectTrace then
      .error (.protocolError s!"sage: poly_companion_q returned a matrix of \
trace {(Value.ofRat trace).render}, but the companion matrix of this polynomial \
has trace {(Value.ofRat expectTrace).render} — the sum of its roots, which every \
companion layout shares")
    else if Value.detQ n rats != expectDet then
      .error (.protocolError s!"sage: poly_companion_q returned a matrix of \
determinant {(Value.ofRat (Value.detQ n rats)).render}, but the companion matrix \
of this polynomial has determinant {(Value.ofRat expectDet).render} — the product \
of its roots, which every companion layout shares")
    else .ok v

/-- The decoded reply must be the kind of value the op promises; a
well-formed value of the wrong kind is an adapter defect, not a result.

Public, with the two checks above, because a check nothing can call is a check
nothing can prove: `CasDslTests/Core.lean` `#guard`s this seam, so deleting
either a check or its call site here fails the build. All three are pure
functions of the request and the reply — no port, no process.

`approx_real` is checked against the RECEIVER as well: the decimal's own
certificate is verified inside the codec (`Value.mkApprox`, at decode), and
what is left to check here is that the reply approximates the value that was
actually sent — a certificate that holds for some other number is still a
wrong answer to this call. -/
def expectKind (op : String) (o : Obj) (v : Value) : Except ExecError Value :=
  match op, v with
  | "approx_real", .approx exact .. =>
      match o with
      | .elem _ recv =>
          if exact == recv then .ok v
          else .error (.protocolError s!"sage: approx_real returned an \
approximation of {exact.render}, but was asked for {recv.render}")
      | o => .error (offSignature "approx_real" o)
  | "factor_int", .factorization .. => .ok v
  | "factor_poly_q", .factorization .. => .ok v
  | "factor_poly_z", .factorization .. => .ok v
  | "factor_poly_c", .factorization .. => .ok v
  | "mat_det_q", .rat _ => .ok v
  | "mat_inv_q", .mat .. => .ok v
  -- both of these are checked against the RECEIVER, not merely for their kind
  | "mat_charpoly_q", _ =>
      match o with
      | .elem (.matrix n _) _ => checkCharpoly n v
      | o => .error (offSignature "mat_charpoly_q" o)
  | "poly_companion_q", _ =>
      match o with
      | .elem (.poly _) (.poly _ cs) => checkCompanion cs v
      | o => .error (offSignature "poly_companion_q" o)
  | "gcd_int", .int _ => .ok v
  | "is_prime_int", .bool _ => .ok v
  -- the EMPTY set is the honest answer for a polynomial with no root in its
  -- own coefficient ring (x² − 2 over ℚ), so it is a result like any other
  | "roots_poly_z", .setV .. => .ok v
  | "roots_poly_q", .setV .. => .ok v
  -- over ℂ a nonzero polynomial splits, so this set is never empty — but the
  -- kind check is the same one: a factorization here would be an adapter bug
  | "roots_poly_c", .setV .. => .ok v
  | _, _ =>
      .error (.protocolError
        s!"sage: op {repr op} returned {v.render}, which is not the value kind it promises")

/-- The registered `sage` executor. -/
def executor : Executor := fun opId receiver args => do
  -- DEFAULT-DENY on arguments: every op takes its receiver alone unless it is
  -- named here, so an op added later rejects a stray argument instead of
  -- silently dropping it. A defective method declaration is reported.
  if !args.isEmpty && !(#["gcd_int", "approx_real"].contains opId) then
    return .error (.badRequest s!"sage op {repr opId} takes no arguments, got {args.size}")
  let payload : Except ExecError Json :=
    match opId with
    | "factor_int" => factorIntArgs receiver
    | "factor_poly_q" => polyQArgs "factor_poly_q" receiver
    | "factor_poly_z" => factorPolyZArgs receiver
    | "factor_poly_c" => polyCArgs "factor_poly_c" receiver
    | "roots_poly_c" => polyCArgs "roots_poly_c" receiver
    | "mat_det_q" => matQArgs "mat_det_q" receiver
    | "mat_inv_q" => matQArgs "mat_inv_q" receiver
    | "mat_charpoly_q" => matQArgs "mat_charpoly_q" receiver
    | "poly_companion_q" => polyQArgs "poly_companion_q" receiver
    | "roots_poly_z" => rootsPolyZArgs receiver
    | "roots_poly_q" => polyQArgs "roots_poly_q" receiver
    | "gcd_int" => gcdIntArgs receiver args
    | "approx_real" => approxRealArgs receiver args
    | "is_prime_int" => isPrimeIntArgs receiver
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
        | .ok v => return expectKind opId receiver v

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
  { backend := `sage, opId := "mat_charpoly_q",
    accepts := #[.elemOf (.matrixOver (.exact .rat))] },
  { backend := `sage, opId := "poly_companion_q",
    accepts := #[.elemOf (.polyOver (.exact .rat))] },
  { backend := `sage, opId := "gcd_int", accepts := #[.elemOf (.exact .int)] },
  { backend := `sage, opId := "is_prime_int", accepts := #[.elemOf (.exact .int)] },
  { backend := `sage, opId := "roots_poly_z",
    accepts := #[.elemOf (.polyOver (.exact .int))] },
  { backend := `sage, opId := "roots_poly_q",
    accepts := #[.elemOf (.polyOver (.exact .rat))] },
  { backend := `sage, opId := "factor_poly_c",
    accepts := #[.elemOf (.polyOver (.exact .complex))] },
  { backend := `sage, opId := "roots_poly_c",
    accepts := #[.elemOf (.polyOver (.exact .complex))] },
  -- the exact REALS, and nothing else: a decimal presentation of a complex
  -- number is not something this op implements, and the route registered for
  -- `approximate` may therefore not send it one
  { backend := `sage, opId := "approx_real",
    accepts := #[.elemOf (.exact .real)] }
]

run_cmd sageOpSigs.forM registerOpSig!

end CasDsl.Sage
