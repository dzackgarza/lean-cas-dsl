/-
The `native` backend: exact, pure-Lean executors.

Everything here is exact `Int`/`Rat` arithmetic — no floats, no tolerance,
no defaulting. An operation that is not defined for the presentation it was
handed returns `ExecError.badRequest`; it never guesses a nearby meaning.
Routes are supposed to keep such presentations away from this backend, so a
`badRequest` from here is a routing bug and says so.

The whole backend is a PURE function `Native.run`; `Native.exec` only lifts
it into `IO` for the executor table. That keeps every operation
`#guard`-testable.
-/
import Lean
import CasDsl.Route
import CasDsl.Register

namespace CasDsl
namespace Native

/-! ## Elaboration-level exact arithmetic (DESIGN.md §6: coercions are
inserted by elaboration; internal distinctions stay internal). -/

def toRat? : Value → Option Rat
  | .int z => some (Rat.ofInt z)
  | .rat q => some q
  | _ => none

/-- Bring two scalars into a common domain: `ℤ ⊆ ℚ`, and an integer into
`ℤ/n` as its residue class. `none` = the kinds are incomparable. -/
def promote : Value → Value → Option (Value × Value)
  | .int a, .rat q => some (.rat (Rat.ofInt a), .rat q)
  | .rat q, .int a => some (.rat q, .rat (Rat.ofInt a))
  | .int a, .mod n v => if n == 0 then none else some (Value.mkMod n a, .mod n v)
  | .mod n v, .int a => if n == 0 then none else some (.mod n v, Value.mkMod n a)
  | a@(.int _), b@(.int _) => some (a, b)
  | a@(.rat _), b@(.rat _) => some (a, b)
  | a@(.mod n _), b@(.mod n' _) => if n == n' then some (a, b) else none
  | a@(.poly ..), b@(.poly ..) => some (a, b)
  | a@(.mat ..), b@(.mat ..) => some (a, b)
  | a@(.factorization ..), b@(.factorization ..) => some (a, b)
  | a@(.idealV ..), b@(.idealV ..) => some (a, b)
  | a@(.cardinal _), b@(.cardinal _) => some (a, b)
  | a@(.bool _), b@(.bool _) => some (a, b)
  | _, _ => none

/-- Equality after promotion; `none` = incomparable kinds (never `false`,
which would claim a mathematical judgment we did not make). -/
def valueEq (a b : Value) : Option Bool :=
  (promote a b).map fun (x, y) => x == y

private def ratCmp (x y : Rat) : Ordering :=
  if x.blt y then .lt else if y.blt x then .gt else .eq

/-- Order on scalars. On `ℤ/n` this orders by the normalized representative:
a canonicalization key for element lists, not a claim that `ℤ/n` is ordered. -/
def scalarCmp (a b : Value) : Option Ordering :=
  match promote a b with
  | some (.int x, .int y) => some (compare x y)
  | some (.rat x, .rat y) => some (ratCmp x y)
  | some (.mod _ x, .mod _ y) => some (compare x y)
  | _ => none

private def binOp (op : String) (fi : Int → Int → Int) (fr : Rat → Rat → Rat)
    (a b : Value) : Except String Value :=
  match promote a b with
  | some (.int x, .int y) => .ok (.int (fi x y))
  | some (.rat x, .rat y) => .ok (.rat (fr x y))
  | some (.mod n x, .mod _ y) => .ok (Value.mkMod n (fi (Int.ofNat x) (Int.ofNat y)))
  | _ => .error s!"{op} is not defined on {a.render} and {b.render}"

def scalarAdd : Value → Value → Except String Value :=
  binOp "addition" (· + ·) (· + ·)

def scalarSub : Value → Value → Except String Value :=
  binOp "subtraction" (· - ·) (· - ·)

def scalarMul : Value → Value → Except String Value :=
  binOp "multiplication" (· * ·) (· * ·)

/-- Unary; the arity of negation is one, so this deviates from the sibling
binary signatures on purpose. -/
def scalarNeg : Value → Except String Value
  | .int z => .ok (.int (-z))
  | .rat q => .ok (.rat (-q))
  | .mod n v => .ok (Value.mkMod n (-(Int.ofNat v)))
  | v => .error s!"negation is not defined on {v.render}"

private def exponent? : Value → Option Nat
  | .int z => if z < 0 then none else some z.toNat
  | .rat q => if q.den == 1 && q.num ≥ 0 then some q.num.toNat else none
  | _ => none

/-- Exponent must be a nonnegative integer: no rational powers, no inverses
by negative exponent. -/
def scalarPow (a e : Value) : Except String Value :=
  match exponent? e with
  | none => .error s!"exponentiation needs a nonnegative integer exponent, got {e.render}"
  | some k =>
      let one : Value := match a with
        | .rat _ => .rat 1
        | .mod n _ => Value.mkMod n 1
        | _ => .int 1
      (List.range k).foldlM (fun acc _ => scalarMul acc a) one

/-- Exact division in ℚ. Integer operands are promoted along `ℤ ⊆ ℚ`, so the
result is a `.rat` even when it is integral. Division in `ℤ/n` is not
provided (that ring is a field only for prime `n`) and fails loudly. -/
def scalarDiv (a b : Value) : Except String Value :=
  match toRat? a, toRat? b with
  | some x, some y =>
      if y == 0 then .error "division by zero"
      else .ok (.rat (x / y))
  | _, _ => .error s!"division is not defined on {a.render} and {b.render}"

/-! ## Presentation helpers -/

private def zeroOf : Domain → Value
  | .rat => .rat 0
  | .mod n => Value.mkMod n 0
  | _ => .int 0

/-- Horner evaluation. Mixed `ℤ`/`ℚ` coefficients and argument promote along
`ℤ ⊆ ℚ`; a `ℤ/n` coefficient domain evaluates in `ℤ/n`. -/
def polyEval (coeff : Domain) (coeffs : Array Value) (x : Value)
    : Except String Value :=
  coeffs.reverse.foldlM (init := zeroOf coeff) fun acc c => do
    scalarAdd (← scalarMul acc x) c

/-- The registered enumeration convention for `ℤ` (DESIGN.md open
questions): `0, 1, −1, 2, −2, …`, zero-based. A registered CHOICE, not a
mathematical fact — it is revisitable and nothing else may assume it. -/
def intEnum (k : Nat) : Int :=
  if k == 0 then 0
  else if k % 2 == 1 then Int.ofNat ((k + 1) / 2)
  else -(Int.ofNat (k / 2))

/-- Cardinality of a domain used as a set. `ℤ/0 ≅ ℤ` is infinite. -/
def domainCard : Domain → Cardinality
  | .nat | .int | .rat => .countablyInfinite
  | .mod 0 => .countablyInfinite
  | .mod n => .finite n
  | .poly c =>
      match domainCard c with
      | .finite k => if k ≤ 1 then .finite 1 else .countablyInfinite
      | .countablyInfinite => .countablyInfinite
  | .matrix n e =>
      match domainCard e with
      | .finite k => .finite (k ^ (n * n))
      | .countablyInfinite => if n == 0 then .finite 1 else .countablyInfinite

/-- Quadratic dedupe, used only on hand-written finite set literals. -/
private def dedupValues (vs : Array Value) : Array Value :=
  vs.foldl (init := #[]) fun acc v =>
    if acc.any (fun w => valueEq w v == some true) then acc else acc.push v

private def dedupSorted (vs : Array Value) : Array Value :=
  vs.foldl (init := #[]) fun acc v =>
    match acc.back? with
    | some w => if valueEq w v == some true then acc else acc.push v
    | none => acc.push v

/-- Number of elements of `first, first + step, …` bounded by `last?`;
`none` = infinite. A zero step is degenerate, not "one element". -/
private def progCount (first step : Value) (last? : Option Value)
    : Except ExecError (Option Nat) := do
  let some s := toRat? step
    | .error (.badRequest s!"progression step {step.render} is not a rational number")
  if s == 0 then
    .error (.badRequest "a progression with zero step is degenerate")
  match last? with
  | none => return none
  | some l =>
      let some f := toRat? first
        | .error (.badRequest s!"progression start {first.render} is not a rational number")
      let some lv := toRat? l
        | .error (.badRequest s!"progression bound {l.render} is not a rational number")
      let q := (lv - f) / s
      if q.blt 0 then return some 0
      -- `den > 0`, so Euclidean division on the numerator is the floor.
      else return some ((Int.ediv q.num (Int.ofNat q.den)).toNat + 1)

private def progNth (first step : Value) (last? : Option Value) (k : Nat)
    : Except ExecError Value := do
  let v ← Except.mapError ExecError.badRequest do
    scalarAdd first (← scalarMul (.int (Int.ofNat k)) step)
  match ← progCount first step last? with
  | none => return v
  | some n =>
      if k < n then return v
      else .error (.badRequest
        s!"index {k} is out of range: the progression has {n} elements")

private def isIntegral : Value → Bool
  | .int _ => true
  | .rat q => q.den == 1
  | _ => false

private def domainContains (d : Domain) (x : Value) : Except ExecError Value :=
  match d with
  | .nat =>
      match x with
      | .int z => .ok (.bool (z ≥ 0))
      | .rat q => .ok (.bool (q.den == 1 && q.num ≥ 0))
      | _ => .ok (.bool false)
  | .int => .ok (.bool (isIntegral x))
  | .rat => .ok (.bool (match x with | .int _ | .rat _ => true | _ => false))
  | .mod n =>
      match x with
      | .mod m _ => .ok (.bool (m == n))
      -- an integer names its residue class
      | .int _ => .ok (.bool true)
      | _ => .ok (.bool false)
  | d => .error (.badRequest
      s!"the native backend has no membership test for {d.render}")

private def progContains (first step : Value) (last? : Option Value) (x : Value)
    : Except ExecError Value := do
  let some f := toRat? first
    | .error (.badRequest s!"progression start {first.render} is not a rational number")
  let some s := toRat? step
    | .error (.badRequest s!"progression step {step.render} is not a rational number")
  let some xv := toRat? x
    | .error (.badRequest s!"{x.render} is not comparable with a rational progression")
  if s == 0 then
    return .bool (f == xv)
  -- membership ⇔ (x − first)/step is a nonnegative integer within the bound
  let t := (xv - f) / s
  if t.den != 1 || t.num < 0 then
    return .bool false
  match last? with
  | none => return .bool true
  | some l =>
      let some lv := toRat? l
        | .error (.badRequest s!"progression bound {l.render} is not a rational number")
      -- dividing by a negative step flips the inequality on both sides, so
      -- `t ≤ (last − first)/step` is the bound in either direction
      return .bool (!((lv - f) / s).blt t)

/-! ## Set equality by presentation normalization

The documented ceiling (DESIGN.md): canonical forms compare ELEMENT SETS,
not ambient domain tags — so `{0, 1, 2, ...}` presented over `ℤ` normalizes
to `ℕ`, because that set *is* ℕ. Bounded progressions and finite domains are
compared by expansion, capped; past the cap the operation fails honestly
rather than guessing. -/

private def expansionCap : Nat := 10000

private inductive SetNormal where
  | fin (elems : Array Value)
  | prog (first step : Rat)
  | dom (d : Domain)

private def scalarSortable (vs : Array Value) : Bool :=
  vs.all (fun v => match v with | .int _ | .rat _ => true | _ => false)
  || (match (vs[0]? : Option Value) with
      | some (.mod n _) => vs.all fun v => match v with | .mod m _ => m == n | _ => false
      | _ => false)

private def sortDedup (vs : Array Value) : Array Value :=
  dedupSorted (vs.qsort fun a b => scalarCmp a b == some .lt)

private def normalizeDomain (d : Domain) : Except ExecError SetNormal :=
  match domainCard d with
  | .countablyInfinite => .ok (.dom d)
  | .finite n =>
      match d with
      | .mod m =>
          if m ≤ expansionCap then
            .ok (.fin ((Array.range m).map fun i => Value.mkMod m (Int.ofNat i)))
          else
            .error (.badRequest
              s!"ℤ/{m} has too many elements to compare by expansion (cap {expansionCap})")
      | d => .error (.badRequest
          s!"the native backend cannot expand {d.render} ({n} elements) for comparison")

private def normalizeProg (first step : Value) (last? : Option Value)
    : Except ExecError SetNormal := do
  let some f := toRat? first
    | .error (.badRequest s!"progression start {first.render} is not a rational number")
  let some s := toRat? step
    | .error (.badRequest s!"progression step {step.render} is not a rational number")
  match ← progCount first step last? with
  | none =>
      if f == 0 && s == 1 then return .dom .nat else return .prog f s
  | some n =>
      if n > expansionCap then
        .error (.badRequest
          s!"the progression has {n} elements; the native backend expands at most \
{expansionCap} for comparison")
      else
        return .fin <| sortDedup <| (Array.range n).map fun i =>
          let q := f + Rat.ofInt (Int.ofNat i) * s
          if q.den == 1 then Value.int q.num else Value.rat q

private def normalizeSet : Obj → Except ExecError SetNormal
  | .setObj (.finite _ elems) =>
      if scalarSortable elems then .ok (.fin (sortDedup elems))
      else .error (.badRequest
        "set equality compares scalar elements only (documented ceiling)")
  | .setObj (.domainSet d) | .domainObj d => normalizeDomain d
  | .setObj (.arithProg _ first step last?) => normalizeProg first step last?
  | o => .error (.badRequest s!"{o.presentation} is not a set")

private def setNormalEq : SetNormal → SetNormal → Bool
  | .fin a, .fin b =>
      a.size == b.size && (a.zip b).all fun (x, y) => valueEq x y == some true
  | .prog f1 s1, .prog f2 s2 => f1 == f2 && s1 == s2
  | .dom d1, .dom d2 => d1 == d2
  | _, _ => false

/-! ## Operations -/

private def scalarArg (op : String) (args : Array Obj) : Except ExecError Value :=
  match (args[0]? : Option Obj) with
  | some (.elem _ v) => .ok v
  | some o => .error (.badRequest s!"{op} expects a scalar argument, got {o.presentation}")
  | none => .error (.badRequest s!"{op} expects one argument")

private def natIndex (args : Array Obj) : Except ExecError Nat :=
  match (args[0]? : Option Obj) with
  | some (.elem _ (.int k)) =>
      if k < 0 then .error (.badRequest s!"index {k} is negative")
      else .ok k.toNat
  | some o => .error (.badRequest s!"nth expects an integer index, got {o.presentation}")
  | none => .error (.badRequest "nth expects one index argument")

/-- The native backend, as a pure function. -/
def run (opId : String) (o : Obj) (args : Array Obj) : Except ExecError Value :=
  match opId with
  | "poly_eval" =>
      match o with
      | .elem (.poly c) (.poly _ coeffs) => do
          let x ← scalarArg "poly_eval" args
          Except.mapError ExecError.badRequest (polyEval c coeffs x)
      | o => .error (.badRequest
          s!"poly_eval expects a polynomial receiver, got {o.presentation}")
  | "nth" => do
      let k ← natIndex args
      match o with
      | .setObj (.domainSet .nat) | .domainObj .nat => return .int (Int.ofNat k)
      | .setObj (.domainSet .int) | .domainObj .int => return .int (intEnum k)
      | .setObj (.finite _ elems) =>
          match elems[k]? with
          | some v => return v
          | none => .error (.badRequest
              s!"index {k} is out of range for a set of {elems.size} elements")
      | .setObj (.arithProg _ first step last?) => progNth first step last? k
      | o => .error (.badRequest
          s!"the native backend cannot enumerate {o.presentation}")
  | "cardinality" =>
      match o with
      | .setObj (.finite _ elems) => .ok (.cardinal (.finite (dedupValues elems).size))
      | .setObj (.domainSet d) | .domainObj d => .ok (.cardinal (domainCard d))
      | .setObj (.arithProg _ first step last?) => do
          match ← progCount first step last? with
          | none => return .cardinal .countablyInfinite
          | some n => return .cardinal (.finite n)
      | o => .error (.badRequest s!"the native backend cannot count {o.presentation}")
  | "contains" => do
      let x ← scalarArg "contains" args
      match o with
      | .setObj (.finite _ elems) =>
          return .bool (elems.any fun e => valueEq e x == some true)
      | .setObj (.arithProg _ first step last?) => progContains first step last? x
      | .setObj (.domainSet d) | .domainObj d => domainContains d x
      | o => .error (.badRequest s!"{o.presentation} is not a set")
  | "set_eq" => do
      let some rhs := args[0]?
        | .error (.badRequest "set_eq expects one set argument")
      let a ← normalizeSet o
      let b ← normalizeSet rhs
      return .bool (setNormalEq a b)
  | "annihilator_cyclic" =>
      match o with
      | .cyclicModule n => .ok (.idealV #[.int (Int.ofNat n)] .int)
      | o => .error (.badRequest
          s!"annihilator_cyclic expects a cyclic module, got {o.presentation}")
  | other => .error (.badRequest s!"the native backend has no operation '{other}'")

def exec : Executor := fun opId o args => return run opId o args

end Native

initialize registerExecutor `native Native.exec

/-- The receiver signatures of the native ops, restated from `Native.run`'s
matches as checked registration data: `addRouteChecked` refuses any route
that would send this backend a receiver shape outside these patterns. -/
private def nativeOpSigs : Array OpSig := #[
  { backend := `native, opId := "poly_eval",
    accepts := #[.elemOf (.polyOver .anyDom)] },
  { backend := `native, opId := "nth",
    accepts := #[.domainIs (.exact .nat), .domainSetOf (.exact .nat),
                 .domainIs (.exact .int), .domainSetOf (.exact .int),
                 .finiteSet, .progression .anyDom] },
  { backend := `native, opId := "cardinality", accepts := #[.anySet] },
  { backend := `native, opId := "contains", accepts := #[.anySet] },
  { backend := `native, opId := "set_eq", accepts := #[.anySet] },
  { backend := `native, opId := "annihilator_cyclic", accepts := #[.cyclicMod] }
]

run_cmd nativeOpSigs.forM registerOpSig!

end CasDsl
