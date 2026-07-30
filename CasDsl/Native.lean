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

/-! ### Exact algebraic arithmetic (`a + b√d`)

Closed inside ONE quadratic field over ℚ: two operands must name the same
square-free radicand, and `√2 + √5` — which leaves this presentation — is a
loud refusal rather than a value silently reinterpreted or approximated.
Everything is exact `Rat` arithmetic; there is no float anywhere near it. -/

/-- The radicand an operand names, if it is a surd at all. -/
private def radicand? : Value → Option Int
  | .alg _ _ d => some d
  | _ => none

/-- `(a, b)` with `v = a + b√d`. A rational rides in every quadratic field, so
it reads as `a + 0√d` for whichever one the other operand named. -/
private def surdParts? (d : Int) : Value → Option (Rat × Rat)
  | .int z => some (Rat.ofInt z, 0)
  | .rat q => some (q, 0)
  | .alg a b d' => if d' == d then some (a, b) else none
  | _ => none

/-- Both operands, read in the quadratic field one of them names. -/
private def surdPair (x y : Value) : Option ((Rat × Rat) × (Rat × Rat) × Int) := do
  let d ← radicand? x <|> radicand? y
  let px ← surdParts? d x
  let py ← surdParts? d y
  return (px, py, d)

/-- Run `f` on both operands in the quadratic field they share.

`none` = NEITHER operand is a surd, so the caller's ordinary scalar path
applies; `some (.error …)` = one of them is and they do not share a field, or
the other operand is not a number here. -/
private def onSurds (what : String) (x y : Value)
    (f : Rat × Rat → Rat × Rat → Int → Except String Value)
    : Option (Except String Value) :=
  match radicand? x, radicand? y with
  | none, none => none
  | _, _ =>
    match surdPair x y with
    | some (px, py, d) => some (f px py d)
    | none => some (.error s!"{what} of {x.render} and {y.render} leaves the \
exact form a + b√d this slice presents (one square root over ℚ, and both \
operands in it): that is a gap, not an approximation")

/-- A cardinal against an integer. SPEC.md writes `|A| = 3` and `|E| = ℵ₀`,
so a FINITE cardinal answers to the natural number counting it; ℵ₀ answers
to no integer, and a negative integer counts nothing — both are `false`, not
"unknown", because the comparison is perfectly decided. -/
private def cardEqInt : Cardinality → Int → Bool
  | .finite n, z => Int.ofNat n == z
  | .countablyInfinite, _ => false

/-- Equality after promotion; `none` = incomparable kinds (never `false`,
which would claim a mathematical judgment we did not make).

Two functions are equal when they are declared over the same domains and
their bodies agree — the binder is a BOUND NAME, so `t ↦ t² + 1` and
`s ↦ s² + 1` are the same function, and SPEC.md's `assert h = hp` compares
the two spellings of one body through the polynomial normal form. -/
def valueEq (a b : Value) : Option Bool :=
  match a, b with
  -- An exact algebraic value equals only the same normal form. Both `false`s
  -- are theorems about that form rather than a comparison this slice ducked:
  -- `b ≠ 0` with a square-free `d ∉ {0, 1}` keeps a surd out of ℚ, and two
  -- different square-free radicands generate different quadratic fields.
  | .alg a b d, .alg a' b' d' => some (a == a' && b == b' && d == d')
  | .alg .., .int _ | .alg .., .rat _
  | .int _, .alg .. | .rat _, .alg .. => some false
  | .func s t _ fb, .func s' t' _ gb =>
      if s != s' || t != t' then some false
      else (promote fb gb).map fun (x, y) => x == y
  | .cardinal c, .int z | .int z, .cardinal c => some (cardEqInt c z)
  | _, _ => (promote a b).map fun (x, y) => x == y

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

def scalarAdd (a b : Value) : Except String Value :=
  (onSurds "the sum" a b fun (xa, xb) (ya, yb) d =>
    Value.mkAlg (xa + ya) (xb + yb) d).getD
    (binOp "addition" (· + ·) (· + ·) a b)

def scalarSub (a b : Value) : Except String Value :=
  (onSurds "the difference" a b fun (xa, xb) (ya, yb) d =>
    Value.mkAlg (xa - ya) (xb - yb) d).getD
    (binOp "subtraction" (· - ·) (· - ·) a b)

/-- `(xa + xb√d)(ya + yb√d) = (xa·ya + xb·yb·d) + (xa·yb + xb·ya)√d`. -/
def scalarMul (a b : Value) : Except String Value :=
  (onSurds "the product" a b fun (xa, xb) (ya, yb) d =>
    Value.mkAlg (xa * ya + xb * yb * Rat.ofInt d) (xa * yb + xb * ya) d).getD
    (binOp "multiplication" (· * ·) (· * ·) a b)

/-- Unary; the arity of negation is one, so this deviates from the sibling
binary signatures on purpose. -/
def scalarNeg : Value → Except String Value
  | .int z => .ok (.int (-z))
  | .rat q => .ok (.rat (-q))
  | .mod n v => .ok (Value.mkMod n (-(Int.ofNat v)))
  | .alg a b d => Value.mkAlg (-a) (-b) d
  | v => .error s!"negation is not defined on {v.render}"

private def exponent? : Value → Option Nat
  | .int z => if z < 0 then none else some z.toNat
  | .rat q => if q.den == 1 && q.num ≥ 0 then some q.num.toNat else none
  -- SPEC.md's `|𝒫(A)| = 2^|A|`: a FINITE cardinal is the number it counts.
  -- `2^ℵ₀` has no exponent here and fails loudly — this slice's `Cardinality`
  -- has no uncountable constructor, so the honest outcome is the refusal
  | .cardinal (.finite n) => some n
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
  -- in a quadratic field, division is multiplication by the conjugate over
  -- the NORM `ya² − yb²d`, which vanishes only for the zero divisor (`d` is
  -- not a square, so `ya² = yb²d` forces both to be zero)
  match onSurds "the quotient" a b fun (xa, xb) (ya, yb) d =>
      let n := ya * ya - yb * yb * Rat.ofInt d
      if n == 0 then .error "division by zero"
      else Value.mkAlg ((xa * ya - xb * yb * Rat.ofInt d) / n)
        ((xb * ya - xa * yb) / n) d with
  | some r => r
  | none =>
    match toRat? a, toRat? b with
    | some x, some y =>
        if y == 0 then .error "division by zero"
        else .ok (.rat (x / y))
    | _, _ => .error s!"division is not defined on {a.render} and {b.render}"

/-! ## Presentation helpers -/

/-- The zero of a domain — the constant term of a degree-≤0 polynomial
wherever one is read out, so `ℤ/5`'s zero is `.mod 5 0` and not `.int 0`. -/
def zeroOf : Domain → Value
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

/-- The `k`-th positive rational of the Cantor zigzag: diagonals
`num + den = 2, 3, …`, numerator ascending within a diagonal, non-reduced
fractions skipped — `1, 1/2, 2, 1/3, 3, 1/4, 2/3, 3/2, 4, …`. -/
def ratPosEnum (k : Nat) : Rat := Id.run do
  let mut cnt := 0
  -- diagonal d always contributes at least 1/(d−1), so k+3 diagonals suffice
  for d in [2 : k + 3] do
    for num in [1 : d] do
      if Nat.gcd num (d - num) == 1 then
        if cnt == k then return mkRat (Int.ofNat num) (d - num)
        cnt := cnt + 1
  panic! s!"ratPosEnum: exhausted {k + 3} diagonals before index {k} (unreachable)"

/-- The registered enumeration convention for `ℚ` (design review 2026-07-30,
issue #17): the Cantor zigzag — `0`, then positives and negatives
interleaved exactly like `intEnum`: `0, 1, −1, 1/2, −1/2, 2, −2, 1/3, …`.
A registered CHOICE like ℤ's, never a claim that ℚ is intrinsically
ordered this way. -/
def ratEnum (k : Nat) : Rat :=
  if k == 0 then 0
  else if k % 2 == 1 then ratPosEnum ((k - 1) / 2)
  else -(ratPosEnum (k / 2 - 1))

/-- Cardinality of a domain used as a set. `ℤ/0 ≅ ℤ` is infinite.

`none` = this slice's `Cardinality` cannot state it: ℝ and ℂ are uncountable
and a function domain is a set of maps nothing here enumerates. Reporting
that absence is the honest answer; inventing `ℵ₀` for either would be a wrong
mathematical claim — and giving ℝ and ℂ INHABITANTS does not change it. -/
def domainCard : Domain → Option Cardinality
  | .nat | .int | .rat => some .countablyInfinite
  | .real | .complex | .funcs .. => none
  | .mod 0 => some .countablyInfinite
  | .mod n => some (.finite n)
  | .poly c =>
      match domainCard c with
      | some (.finite k) => some (if k ≤ 1 then .finite 1 else .countablyInfinite)
      | some .countablyInfinite => some .countablyInfinite
      | none => none
  | .matrix n e =>
      match domainCard e with
      | some (.finite k) => some (.finite (k ^ (n * n)))
      | some .countablyInfinite => some (if n == 0 then .finite 1 else .countablyInfinite)
      | none => none

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

/-- Is `x` an element of `d`? `none` = this backend has no membership test
for that domain, which is a loud error at the call site and never `false`.

`c[x]` recurses on the COEFFICIENTS, so `x ∈ ℤ[x]` and `p ∈ ℤ[x]` are settled
by the same judgment that settles `-3 ∈ ℤ` — and a polynomial over ℤ is an
element of ℚ[x] for the reason it always was, coefficient by coefficient. A
scalar is its own constant polynomial. -/
private partial def inDomain? (d : Domain) (x : Value) : Option Bool :=
  match d, x with
  | .nat, .int z => some (z ≥ 0)
  | .nat, .rat q => some (q.den == 1 && q.num ≥ 0)
  | .nat, _ => some false
  | .int, v => some (isIntegral v)
  | .rat, .int _ => some true
  | .rat, .rat _ => some true
  | .rat, _ => some false
  | .mod n, .mod m _ => some (m == n)
  -- an integer names its residue class
  | .mod _, .int _ => some true
  | .mod _, _ => some false
  -- ℝ and ℂ: every rational is one, and the exact algebraic values are the
  -- others — a NEGATIVE radicand is not real (DESIGN.md §Exact number
  -- systems). Deciding membership does not claim the domain is enumerated:
  -- the reals this slice cannot present are still elements of ℝ, and a value
  -- it CAN present is placed exactly
  | .real, .alg _ _ d => some (d > 0)
  | .real, .int _ | .real, .rat _ => some true
  | .real, _ => some false
  | .complex, .int _ | .complex, .rat _ | .complex, .alg .. => some true
  | .complex, _ => some false
  | .poly c, .poly _ cs => cs.foldlM (init := true) fun acc v =>
      (inDomain? c v).map (acc && ·)
  | .poly c, v => inDomain? c v
  | _, _ => none

/-- `x ∈ d`, or the loud refusal that this backend has no test for `d` — the
one place that judgment is made, so a difference set cannot decide membership
differently from the domain it was built from. -/
private def domainMember (d : Domain) (x : Value) : Except ExecError Bool :=
  match inDomain? d x with
  | some b => .ok b
  | none => .error (.badRequest
      s!"the native backend has no membership test for {d.render}")

private def domainContains (d : Domain) (x : Value) : Except ExecError Value := do
  return .bool (← domainMember d x)

/-- `x ∈ a - b`: in the first domain and not in the second. The ONE decision
behind a difference set, so `x ∈ ℂ - ℚ` and `S ⊆ ℂ - ℚ` cannot disagree —
they are two spellings of this, not two implementations of it. -/
private def diffMember (a b : Domain) (x : Value) : Except ExecError Bool := do
  return (← domainMember a x) && !(← domainMember b x)

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

/-! ## Cardinality of a presentation

`|A|` reads every presentation, including the two that are DENOTED rather
than listed: the product and the powerset multiply and exponentiate
cardinals exactly. `𝒫` of a countably infinite set is uncountable, which
this slice's `Cardinality` deliberately cannot state — so it fails loudly
instead of inventing ℵ₀. -/

private def cardMul : Cardinality → Cardinality → Cardinality
  -- the empty factor wins: |∅ × ℕ| = 0, not ℵ₀
  | .finite 0, _ | _, .finite 0 => .finite 0
  | .finite m, .finite n => .finite (m * n)
  | _, _ => .countablyInfinite

/-- Exponent past which `2^n` stops being a number worth materializing.
A loud ceiling, not a fallback: `𝒫(ℤ/100000)` says so rather than hanging. -/
private def powersetExpCap : Nat := 4096

partial def presCard : SetPresentation → Except ExecError Cardinality
  | .finite _ elems => .ok (.finite (dedupValues elems).size)
  | .domainSet d =>
      match domainCard d with
      | some c => .ok c
      | none => .error (.badRequest
          s!"the native backend cannot express the cardinality of {d.render}")
  | .arithProg _ first step last? => do
      match ← progCount first step last? with
      | none => return .countablyInfinite
      | some n => return .finite n
  | .product a b => do return cardMul (← presCard a) (← presCard b)
  -- `|ℂ - ℚ|` is not a cardinal this slice can state, and neither is the
  -- general shape: an honest refusal, never a subtraction of cardinals
  | .domainDiff a b => .error (.badRequest
      s!"the native backend cannot state the cardinality of {a.render} - {b.render}: \
this presentation decides membership, not size")
  | .powerset s => do
      match ← presCard s with
      | .finite n =>
          if n ≤ powersetExpCap then return .finite (2 ^ n)
          else .error (.badRequest
            s!"2^{n} is too large to present as a cardinal here (cap {powersetExpCap})")
      | .countablyInfinite =>
          .error (.badRequest
            "the powerset of a countably infinite set is uncountable, which this \
slice's Cardinality cannot state")

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
  | none =>
      .error (.badRequest
        s!"the native backend cannot compare {d.render} as a set: its cardinality \
is not expressible here")
  | some .countablyInfinite => .ok (.dom d)
  | some (.finite n) =>
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
          Value.ofRat (f + Rat.ofInt (Int.ofNat i) * s)

private def normalizeSet : Obj → Except ExecError SetNormal
  -- Scalars sort, which is the cheap dedupe; anything else — an exact
  -- algebraic value, where ORDER would be a claim ℂ does not support —
  -- dedupes by comparison instead. Equality below is order-free either way.
  | .setObj (.finite _ elems) =>
      .ok (.fin (if scalarSortable elems then sortDedup elems else dedupValues elems))
  | .setObj (.domainSet d) | .domainObj d => normalizeDomain d
  | .setObj (.arithProg _ first step last?) => normalizeProg first step last?
  -- a denoted set has no canonical form here: comparing `A × B`, `𝒫(A)` or
  -- `ℂ - ℚ` with anything would need element lists this ontology does not
  -- present. (`ℂ - ℚ` is decided as the RIGHT side of an inclusion, below,
  -- where pointwise membership settles it without a canonical form.)
  | o@(.setObj (.product ..)) | o@(.setObj (.powerset _))
  | o@(.setObj (.domainDiff ..)) =>
      .error (.badRequest s!"the native backend cannot normalize {o.presentation} \
for comparison: a denoted set has no element list here")
  | o => .error (.badRequest s!"{o.presentation} is not a set")

private def setNormalEq : SetNormal → SetNormal → Bool
  -- both sides are deduped, so equal sizes plus one-way membership IS
  -- equality — and it does not depend on an order the elements of ℂ have no
  -- honest one of
  | .fin a, .fin b =>
      a.size == b.size && a.all fun x => b.any fun y => valueEq x y == some true
  | .prog f1 s1, .prog f2 s2 => f1 == f2 && s1 == s2
  | .dom d1, .dom d2 => d1 == d2
  | _, _ => false

/-! ## Inclusion by presentation normalization

`A ⊆ B` is decided from the same canonical forms as equality, and refuses
loudly wherever the presentations do not settle it. Only two things are ever
answered `false` without a decision procedure, and both are theorems about
the forms themselves: a `dom` normal form is countably infinite here (finite
domains expand to `fin`), and a `prog` normal form is unbounded — neither
fits inside a finite list.

The deliberate hole: `dom ⊆ dom` between DIFFERENT domains. `ℕ ⊆ ℤ ⊆ ℚ` is
the preferred-canonical-map registry's claim (DESIGN.md §Coercions), not a
fact this backend may restate — so it is refused here rather than answered
twice. -/

private def normalSubset : SetNormal → SetNormal → Except ExecError Bool
  | .fin a, .fin b =>
      .ok (a.all fun x => b.any fun y => valueEq x y == some true)
  | .fin a, .dom d =>
      a.foldlM (init := true) fun acc x =>
        match inDomain? d x with
        | some m => .ok (acc && m)
        | none => .error (.badRequest
            s!"the native backend has no membership test for {d.render}")
  | .fin a, .prog f s =>
      a.foldlM (init := true) fun acc x => do
        match ← progContains (Value.ofRat f) (Value.ofRat s) none x with
        | .bool m => return acc && m
        | v => .error (.badRequest s!"membership returned {v.render}")
  -- {f + k·s : k ≥ 0} ⊆ d, decided from the two rationals presenting it
  | .prog f s, .dom d =>
      match d with
      | .rat => .ok true
      | .int | .mod _ => .ok (f.den == 1 && s.den == 1)
      | .nat => .ok (f.den == 1 && s.den == 1 && !f.blt 0 && !s.blt 0)
      | d => .error (.badRequest
          s!"the native backend cannot decide inclusion of a progression in {d.render}")
  | .dom d1, .dom d2 =>
      if d1 == d2 then .ok true
      else .error (.badRequest
        s!"whether {d1.render} ⊆ {d2.render} is the preferred-canonical-map \
registry's claim, not one presentation normalization decides")
  -- an infinite normal form (a countably infinite domain, an unbounded
  -- progression) is not contained in a finite list
  | .dom _, .fin _ | .prog .., .fin _ => .ok false
  | .prog f1 s1, .prog f2 s2 =>
      if f1 == f2 && s1 == s2 then .ok true
      else .error (.badRequest
        "the native backend decides inclusion between two progressions only when \
they are the same progression")
  | .dom d, .prog f s =>
      .error (.badRequest
        s!"the native backend cannot decide whether {d.render} lies inside the \
progression starting {(Value.ofRat f).render} with step {(Value.ofRat s).render}")

/-! ## Operations -/

private def scalarArg (op : String) (args : Array Obj) : Except ExecError Value :=
  match (args[0]? : Option Obj) with
  | some (.elem _ v) => .ok v
  | some o => .error (.badRequest s!"{op} expects a scalar argument, got {o.presentation}")
  | none => .error (.badRequest s!"{op} expects one argument")

/-- The explicit element list of a finite set. The binary set operations are
routed for `finiteSet` receivers only, so this is the receiver's routed
shape; the ARGUMENT is validated here (this slice validates arguments at
execution). -/
private def finiteElems (op : String) (o : Obj) : Except ExecError (Domain × Array Value) :=
  match o with
  | .setObj (.finite d es) => .ok (d, es)
  | o => .error (.badRequest
      s!"{op} needs an explicit finite set, got {o.presentation}")

private def setArg (op : String) (args : Array Obj) : Except ExecError Obj :=
  match (args[0]? : Option Obj) with
  | some o => .ok o
  | none => .error (.badRequest s!"{op} expects one set argument")

private def memOf (elems : Array Value) (x : Value) : Bool :=
  elems.any fun e => valueEq e x == some true

/-- A binary operation on two explicit finite sets over ONE element domain.
CEILING: mixing element domains is refused rather than joined — the
preferred-canonical-map registry the surface joins literals with is not
readable from this pure backend. -/
private def binarySetOp (op : String) (o : Obj) (args : Array Obj)
    (combine : Array Value → Array Value → Array Value) : Except ExecError Value := do
  let (d, a) ← finiteElems op o
  let (d', b) ← finiteElems op (← setArg op args)
  if d != d' then
    .error (.badRequest s!"{op} needs both sets over one element domain, got \
{d.render} and {d'.render}")
  else
    return .setV (dedupValues (combine a b)) d

/-- The receiver of a complex-plane method: an element carrying an exact
number. Anything else inside the routed shape (a matrix entry domain that is
ℝ, say) is the loud runtime error partiality always gets here. -/
private def algElem (op : String) : Obj → Except ExecError Value
  | .elem _ v@(.int _) | .elem _ v@(.rat _) | .elem _ v@(.alg ..) => .ok v
  | .elem _ v => .error (.badRequest
      s!"{op} expects an exact number, got {v.render}")
  | o => .error (.badRequest
      s!"{op} expects an element receiver, got {o.presentation}")

/-- Normalization can refuse (a radicand whose square-free part is out of
reach), and that refusal is this backend's own loud failure. -/
private def algValue (r : Except String Value) : Except ExecError Value :=
  Except.mapError ExecError.badRequest r

/-- Is the REAL surd `a + b√d` (`d > 0`) nonnegative? Exact: with `a` and `b`
of opposite signs the comparison squares to `a² ⋛ b²d`, and the two cannot be
equal (`d` is not a square). -/
private def nonNegSurd (a b : Rat) (d : Int) : Bool :=
  let n := a * a - b * b * Rat.ofInt d
  if !a.blt 0 && !b.blt 0 then true
  else if a.blt 0 && b.blt 0 then false
  else if !a.blt 0 then !n.blt 0        -- a ≥ 0 > b: positive iff a² ≥ b²d
  else !Rat.blt 0 n                     -- b > 0 > a: positive iff a² ≤ b²d

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
  | "poly_deg" =>
      match o with
      -- coefficients are stored ascending with no trailing zeros, so the
      -- degree is the last index. The ZERO polynomial has no degree in ℕ —
      -- a partiality within the accepted shape, and a loud error rather than
      -- a conventional −1 or −∞ this slice cannot present
      | .elem (.poly _) (.poly _ coeffs) =>
          if coeffs.isEmpty then
            .error (.badRequest "the zero polynomial has no degree")
          else .ok (.int (Int.ofNat (coeffs.size - 1)))
      | o => .error (.badRequest
          s!"poly_deg expects a polynomial receiver, got {o.presentation}")
  | "nth" => do
      let k ← natIndex args
      match o with
      | .setObj (.domainSet .nat) | .domainObj .nat => return .int (Int.ofNat k)
      | .setObj (.domainSet .int) | .domainObj .int => return .int (intEnum k)
      | .setObj (.domainSet .rat) | .domainObj .rat => return .rat (ratEnum k)
      | .setObj (.finite _ elems) =>
          match elems[k]? with
          | some v => return v
          | none => .error (.badRequest
              s!"index {k} is out of range for a set of {elems.size} elements")
      | .setObj (.arithProg _ first step last?) => progNth first step last? k
      | o => .error (.badRequest
          s!"the native backend cannot enumerate {o.presentation}")
  | "cardinality" => do
      match o with
      | .setObj s => return .cardinal (← presCard s)
      | .domainObj d => return .cardinal (← presCard (.domainSet d))
      | o => .error (.badRequest s!"the native backend cannot count {o.presentation}")
  | "contains" => do
      match o with
      -- membership in a powerset IS the inclusion judgment, so `X ∈ 𝒫(A)`
      -- and `X ⊆ A` are one decision procedure with two spellings
      | .setObj (.powerset s) =>
          let x ← setArg "contains" args
          return .bool (← normalSubset (← normalizeSet x) (← normalizeSet (.setObj s)))
      | .setObj (.product ..) =>
          .error (.badRequest s!"{o.presentation} has pairs for elements, which \
this slice presents no value for")
      -- `x ∈ ℂ - ℚ` is decided POINTWISE, which is the whole content of this
      -- presentation: in the first domain and not in the second, both by the
      -- membership test the domains already have
      | .setObj (.domainDiff p m) => do
          let x ← scalarArg "contains" args
          return .bool (← diffMember p m x)
      | o =>
        let x ← scalarArg "contains" args
        match o with
        | .setObj (.finite _ elems) => return .bool (memOf elems x)
        | .setObj (.arithProg _ first step last?) => progContains first step last? x
        | .setObj (.domainSet d) | .domainObj d => domainContains d x
        | o => .error (.badRequest s!"{o.presentation} is not a set")
  | "set_eq" => do
      let rhs ← setArg "set_eq" args
      let a ← normalizeSet o
      let b ← normalizeSet rhs
      return .bool (setNormalEq a b)
  | "subset" => do
      let rhs ← setArg "subset" args
      match rhs with
      -- SPEC.md's `q.roots() ⊆ ℂ - ℚ`: a difference of domains has no
      -- canonical form to normalize, and needs none — inclusion in it is the
      -- pointwise membership above, taken over an EXPLICIT element list. Any
      -- other receiver refuses rather than guessing at one.
      | .setObj (.domainDiff p m) =>
          match o with
          | .setObj (.finite _ elems) =>
              return .bool (← elems.foldlM (init := true) fun acc x => do
                return acc && (← diffMember p m x))
          | o => .error (.badRequest
              s!"the native backend decides inclusion in {rhs.presentation} for an \
explicit finite set only, and {o.presentation} is not one")
      | rhs => return .bool (← normalSubset (← normalizeSet o) (← normalizeSet rhs))
  | "set_union" => binarySetOp "set_union" o args (· ++ ·)
  | "set_intersect" =>
      binarySetOp "set_intersect" o args fun a b => a.filter (memOf b)
  | "set_diff" =>
      binarySetOp "set_diff" o args fun a b => a.filter (!memOf b ·)
  | "set_symdiff" =>
      binarySetOp "set_symdiff" o args fun a b =>
        a.filter (!memOf b ·) ++ b.filter (!memOf a ·)
  | "func_image" =>
      match o with
      | .elem (.funcs src tgt) (.func _ _ _ body) =>
          -- the body is the exact polynomial the binder generates, so the
          -- image of ℕ under a LINEAR one is exactly an arithmetic
          -- progression — the presentation `{0, 2, 4, ...}` already has
          let cs := match body with
            | .poly _ coeffs => coeffs
            | v => #[v]
          if cs.size ≤ 1 then
            .ok (.setV #[cs[0]?.getD (zeroOf tgt)] tgt)
          else if src == .nat && cs.size == 2 then
            .ok (.progV tgt cs[0]! cs[1]! none)
          else
            .error (.badRequest
              s!"the native backend presents the image of a constant map, and of a \
linear map on ℕ (an arithmetic progression). The image of {body.render} on \
{src.render} is neither, so it is a gap rather than a guess")
      | o => .error (.badRequest
          s!"func_image expects a function receiver, got {o.presentation}")
  -- SPEC.md §Exact number systems: `z.re()`, `z.im()`, `z.bar()`, `|z|`.
  -- All four are structural reads of the exact form `a + b√d` — the engine
  -- genuinely decides them, so they are native and no backend is asked.
  -- A REAL receiver (`d > 0`, or a rational) is its own real part, has no
  -- imaginary part, and is its own conjugate: ℝ ⊆ ℂ, spelled out.
  | "alg_re" => do
      match ← algElem "alg_re" o with
      | v@(.alg a _ d) => return if d < 0 then Value.ofRat a else v
      | v => return v
  | "alg_im" => do
      match ← algElem "alg_im" o with
      -- `√d = i√(-d)` for `d < 0`, so the imaginary part is `b√(-d)` — `b`
      -- itself only when `d = -1`, which `mkAlg` normalizes to the rational
      | .alg _ b d => if d < 0 then algValue (Value.mkAlg 0 b (-d)) else return .int 0
      | _ => return .int 0
  | "alg_conj" => do
      match ← algElem "alg_conj" o with
      | v@(.alg a b d) => if d < 0 then algValue (Value.mkAlg a (-b) d) else return v
      | v => return v
  | "alg_abs" => do
      match ← algElem "alg_abs" o with
      | v@(.alg a b d) =>
          if d < 0 then
            -- |a + b√d|² = a² − b²d is rational, and its square root is the
            -- exact `2√2` SPEC.md writes for |2 + 2i| — never a decimal
            algValue (Value.sqrtOfRat (a * a - b * b * Rat.ofInt d))
          else if nonNegSurd a b d then return v
          else algValue (Value.mkAlg (-a) (-b) d)
      | v =>
          let some q := toRat? v
            | .error (.badRequest s!"{v.render} has no modulus here")
          return Value.ofRat (if q.blt 0 then -q else q)
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
  { backend := `native, opId := "poly_deg",
    accepts := #[.elemOf (.polyOver .anyDom)] },
  { backend := `native, opId := "nth",
    accepts := #[.domainIs (.exact .nat), .domainSetOf (.exact .nat),
                 .domainIs (.exact .int), .domainSetOf (.exact .int),
                 .domainIs (.exact .rat), .domainSetOf (.exact .rat),
                 .finiteSet, .progression .anyDom] },
  { backend := `native, opId := "cardinality", accepts := #[.anySet] },
  { backend := `native, opId := "contains", accepts := #[.anySet] },
  { backend := `native, opId := "set_eq", accepts := #[.anySet] },
  { backend := `native, opId := "subset", accepts := #[.anySet] },
  -- the binary set operations build an explicit element list, so they accept
  -- explicit finite receivers ONLY: `ℤ ∪ A` is the honest capability gap
  { backend := `native, opId := "set_union", accepts := #[.finiteSet] },
  { backend := `native, opId := "set_intersect", accepts := #[.finiteSet] },
  { backend := `native, opId := "set_diff", accepts := #[.finiteSet] },
  { backend := `native, opId := "set_symdiff", accepts := #[.finiteSet] },
  { backend := `native, opId := "annihilator_cyclic", accepts := #[.cyclicMod] },
  -- the complex plane, on the two domains whose elements are exact numbers
  { backend := `native, opId := "alg_re",
    accepts := #[.elemOf (.exact .complex), .elemOf (.exact .real)] },
  { backend := `native, opId := "alg_im",
    accepts := #[.elemOf (.exact .complex), .elemOf (.exact .real)] },
  { backend := `native, opId := "alg_conj",
    accepts := #[.elemOf (.exact .complex), .elemOf (.exact .real)] },
  { backend := `native, opId := "alg_abs",
    accepts := #[.elemOf (.exact .complex), .elemOf (.exact .real)] },
  { backend := `native, opId := "func_image", accepts := #[.elemOf .anyFuncs] }
]

run_cmd nativeOpSigs.forM registerOpSig!

end CasDsl
