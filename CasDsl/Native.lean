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

/-- Two operands in the kind they SHARE — the result of `promote`.

TAGGED rather than a pair of `Value`s, and that is the load-bearing part: the
surd kind is not a pair of values at all (it is two `(a, b)` coefficient pairs
in one named field), and a tag makes every caller STATE what it does with each
kind. `scalarCmp` refuses to order surds in its own match rather than
inheriting an order from whatever shape a pair happened to have. -/
inductive Common where
  | int (x y : Int)
  | rat (x y : Rat)
  /-- Residue classes of one modulus, as their normalized representatives. -/
  | mod (n : Nat) (x y : Nat)
  /-- Both operands read in ONE quadratic field `ℚ(√d)`, as `(a, b)` with
  `v = a + b√d`. -/
  | alg (x y : Rat × Rat) (d : Int)
  /-- A matrix and a VECTOR — the one operand pair that is not two elements of
  a shared kind, because a matrix ACTS on a vector rather than combining with
  it (SPEC.md's `M*v` and `M v`).

  It is a `Common` constructor rather than a layer in front of `promote` so
  that every operation must STATE what it does with the pair: multiplication
  applies, addition says why it has no meaning, and `scalarCmp` refuses in an
  arm of its own instead of inheriting an order from a shape. -/
  | matVec (n : Nat) (entry : Domain) (rows : Array (Array Value))
      (vecEntry : Domain) (comps : Array Value)
  /-- One shape, no scalar arithmetic here: two polynomials, two matrices, … -/
  | same (x y : Value)
  deriving BEq, Repr

/-- Equality inside one kind. Two operands of a quadratic field are equal iff
both coefficient pairs are — `d` is shared by construction. -/
def Common.eq : Common → Bool
  | .int x y | .mod _ x y => x == y
  | .rat x y => x == y
  | .alg x y _ => x == y
  -- a matrix is not a vector: FALSE is a theorem about the two presentations,
  -- the same answer `valueEq` states directly for both orders of the pair
  | .matVec .. => false
  | .same x y => x == y

/-- Bring two operands into the kind they share: `ℤ ⊆ ℚ`, an integer into
`ℤ/n` as its residue class, and — since round four — two operands of a surd
operation read in the ONE quadratic field they name. `none` = the kinds are
incomparable, which is never `false` and never an approximation.

The surd arms come FIRST because a rational against a surd belongs in the
surd's field (`a + 0√d`) rather than promoted along `ℤ ⊆ ℚ`. A value with no
arithmetic here reaches no arm at all, and is then refused by every caller —
an APPROXIMATION above all (DESIGN.md §Numerical approximation): it carries a
requested tolerance, not an error term to propagate, so there is no arithmetic
to give it that would not be invented. -/
def promote : Value → Value → Option Common
  | x@(.alg ..), y | x, y@(.alg ..) => do
      let (px, py, d) ← surdPair x y
      return .alg px py d
  -- a matrix ACTS on a vector; the reverse juxtaposition is a different
  -- operation on a row vector, which this slice does not present, so it
  -- reaches no arm at all rather than being read as this one
  | .mat n e rows, .vec _ ve comps => some (.matVec n e rows ve comps)
  | .int a, .int b => some (.int a b)
  | .int a, .rat q => some (.rat (Rat.ofInt a) q)
  | .rat q, .int a => some (.rat q (Rat.ofInt a))
  | .rat x, .rat y => some (.rat x y)
  | .int a, .mod n v => if n == 0 then none else some (.mod n (a.emod n).toNat v)
  | .mod n v, .int a => if n == 0 then none else some (.mod n v (a.emod n).toNat)
  | .mod n x, .mod n' y => if n == n' then some (.mod n x y) else none
  | a@(.poly ..), b@(.poly ..) => some (.same a b)
  | a@(.mat ..), b@(.mat ..) => some (.same a b)
  | a@(.factorization ..), b@(.factorization ..) => some (.same a b)
  | a@(.idealV ..), b@(.idealV ..) => some (.same a b)
  | a@(.cardinal _), b@(.cardinal _) => some (.same a b)
  | a@(.bool _), b@(.bool _) => some (.same a b)
  | _, _ => none

/-- Does this value have SCALAR arithmetic — one of the kinds `binOp` actually
computes with? `Common.same` is NOT one: two polynomials (or two truth values)
share a shape, not an operation, and a fold that starts from `1` would report
the accumulator rather than the refusal. Named because more than one caller
asks it (the power path here; products over a range next). -/
def hasScalarArithmetic (v : Value) : Bool :=
  match promote v v with
  | some (.int ..) | some (.rat ..) | some (.mod ..) | some (.alg ..) => true
  -- a matrix against itself never reaches `matVec` (that pair is a matrix and
  -- a VECTOR), and the arm is stated rather than folded into a wildcard so a
  -- kind added later has to answer this question too
  | some (.matVec ..) | some (.same ..) | none => false

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
  -- a matrix is not a vector, in EITHER order: `promote` reaches `matVec` for
  -- one of them only (a matrix acts on a vector, not the reverse), and an
  -- equality must not depend on which side it was written
  | .mat .., .vec .. | .vec .., .mat .. => some false
  -- An exact algebraic value equals only the same normal form. Both `false`s
  -- are theorems about that form rather than a comparison this slice ducked:
  -- `b ≠ 0` with a square-free `d ∉ {0, 1}` keeps a surd out of ℚ, and two
  -- different square-free radicands generate different quadratic fields.
  | .alg a b d, .alg a' b' d' => some (a == a' && b == b' && d == d')
  | .alg .., .int _ | .alg .., .rat _
  | .int _, .alg .. | .rat _, .alg .. => some false
  -- Two 1-forms agree when their COEFFICIENTS do; the coefficient domain is a
  -- presentation tag and does not decide, exactly as a vector's entry domain
  -- does not. `Ω¹_{k[x]/k} ≅ k[x] dx` is free of rank one, so this really is
  -- the whole comparison.
  | .diff1 _ p, .diff1 _ q => valueEq p q
  -- …and a 1-form is not a polynomial, in either order: `d(f) = 6x + 1` is
  -- FALSE rather than incomparable, which is the theorem about the two
  -- presentations that the `matVec` arm above states for a matrix and a vector
  | .diff1 .., _ | _, .diff1 .. => some false
  -- Two vectors agree when they have the same LENGTH and their components do.
  -- The entry domain is a presentation tag and does not decide: `(1, 2)` of ℤ²
  -- and of ℚ² are the same vector, exactly as `1` and `1/1` are one number.
  -- CEILING: the components are compared as SCALARS (`promote`), so a vector
  -- whose components are themselves vectors is INCOMPARABLE here rather than
  -- being given an answer no shipped surface line asks for.
  | .vec _ _ xs, .vec _ _ ys =>
      if xs.size != ys.size then some false
      else (xs.zip ys).foldlM (init := true) fun acc (x, y) => do
        return acc && (← (promote x y).map Common.eq)
  | .func s t _ fb, .func s' t' _ gb =>
      if s != s' || t != t' then some false
      else (promote fb gb).map Common.eq
  | .cardinal c, .int z | .int z, .cardinal c => some (cardEqInt c z)
  | _, _ => (promote a b).map Common.eq

private def ratCmp (x y : Rat) : Ordering :=
  if x.blt y then .lt else if y.blt x then .gt else .eq

/-- Order on scalars. On `ℤ/n` this orders by the normalized representative:
a canonicalization key for element lists, not a claim that `ℤ/n` is ordered.

The `alg` kind is refused HERE, one arm above the answer it could give:
exact algebraic values are UNORDERED at the surface (DESIGN.md §Ceilings), so
`√2 ≤ 2` is the honest refusal even though the squaring comparison that would
decide it already exists (`nonNegSurd`). Stating the refusal as its own arm is
what keeps a later kind from inheriting an order nobody declared. -/
def scalarCmp (a b : Value) : Option Ordering :=
  match promote a b with
  | some (.int x y) => some (compare x y)
  | some (.rat x y) => some (ratCmp x y)
  | some (.mod _ x y) => some (compare x y)
  -- `matVec` is refused in its own arm for the reason `alg` is: a matrix and
  -- a vector are not two points of an order at all, and folding them into a
  -- wildcard would let a later kind inherit an order nobody declared
  | some (.matVec ..) | some (.alg ..) | some (.same ..) | none => none

/-- Why ONE value has no arithmetic at all. The unary reading, so that every
path reaches the same words: negation, the base of a power (whose fold would
otherwise report the accumulator it multiplies from), and `noCommonKind`'s
approximation branch below. -/
private def noArithmetic (op : String) (v : Value) : String :=
  match v with
  | .approx .. =>
      s!"{op} is not defined on an approximation ({v.render}): the value carries \
a REQUESTED tolerance, not an error term, and this slice does not invent an \
error calculus to propagate one — compute exactly, then ask for a decimal \
presentation of the result"
  -- a symbolic expression refuses for the neighbouring reason: it is a
  -- PRESENTATION a backend computes limits and expansions from, not a number,
  -- and there is no arithmetic on it here that would not be invented
  | .sym _ =>
      s!"{op} is not defined on the symbolic expression {v.render}: this slice \
presents such an expression so a limit, a definite integral or a Taylor \
expansion can be taken of it, and does no arithmetic with one"
  | v => s!"{op} is not defined on {v.render}"

/-- Why two operands have no common kind — with `noArithmetic`, the ONE place
the reasons are worded, so they cannot drift apart. An approximation refuses
first and in its own words: it is not a number that failed to meet another one,
it is a value that deliberately has no arithmetic. Then a surd that left its
quadratic field, which is a gap in the exact presentation. Then operands that
were never numbers together. -/
private def noCommonKind (op what : String) (a b : Value) : String :=
  let noneAtAll : Value → Bool := fun | .approx .. | .sym _ => true | _ => false
  if noneAtAll a then noArithmetic op a
  else if noneAtAll b then noArithmetic op b
  else if (radicand? a).isSome || (radicand? b).isSome then
    s!"{what} of {a.render} and {b.render} leaves the exact form a + b√d this \
slice presents (one square root over ℚ, and both operands in it): that is a \
gap, not an approximation"
  else s!"{op} is not defined on {a.render} and {b.render}"

/-- The zero of a domain — the constant term of a degree-≤0 polynomial
wherever one is read out, so `ℤ/5`'s zero is `.mod 5 0` and not `.int 0`, and
the accumulator a matrix action folds from is the zero of its entry domain. -/
partial def zeroOf : Domain → Value
  | .rat => .rat 0
  | .mod n => Value.mkMod n 0
  -- the zero of `Eⁿ` is the zero VECTOR: a scalar `0` is not an element of it,
  -- and giving one here would put a scalar where a vector is expected
  | .vector n e => .vec n e (Array.replicate n (zeroOf e))
  | _ => .int 0

/-- The matrix/vector arm of an operation that does not have one: only
multiplication is the ACTION, and the refusal says which operation the
mathematician wanted rather than reporting a missing common kind. -/
private def noLinearArm (op : String) (n : Nat) (e : Domain)
    : Array (Array Value) → Domain → Array Value → Except String Value :=
  fun _ _ _ =>
    .error s!"{op} is not defined between {(Domain.matrix n e).render} and a \
vector: a matrix ACTS on a vector, and the action is the product `M * v`"

/-- A binary operation, one arm per common kind. `fa` is the quadratic
field's and `fmv` the matrix/vector one, which is why neither the surd
arithmetic nor the linear action is a fallback layer in front of this
function — every caller states what it does with every kind. -/
private def binOp (op what : String) (fi : Int → Int → Int) (fr : Rat → Rat → Rat)
    (fa : Rat × Rat → Rat × Rat → Int → Except String Value)
    (fmv : Nat → Domain → Array (Array Value) → Domain → Array Value →
      Except String Value)
    (a b : Value) : Except String Value :=
  match promote a b with
  | some (.int x y) => .ok (.int (fi x y))
  | some (.rat x y) => .ok (.rat (fr x y))
  | some (.mod n x y) => .ok (Value.mkMod n (fi (Int.ofNat x) (Int.ofNat y)))
  | some (.alg x y d) => fa x y d
  | some (.matVec n e rows ve comps) => fmv n e rows ve comps
  | some (.same ..) | none => .error (noCommonKind op what a b)

def scalarAdd (a b : Value) : Except String Value :=
  binOp "addition" "the sum" (· + ·) (· + ·)
    (fun (xa, xb) (ya, yb) d => Value.mkAlg (xa + ya) (xb + yb) d)
    (noLinearArm "addition") a b

def scalarSub (a b : Value) : Except String Value :=
  binOp "subtraction" "the difference" (· - ·) (· - ·)
    (fun (xa, xb) (ya, yb) d => Value.mkAlg (xa - ya) (xb - yb) d)
    (noLinearArm "subtraction") a b

mutual

/-- `(xa + xb√d)(ya + yb√d) = (xa·ya + xb·yb·d) + (xa·yb + xb·ya)√d`; on a
matrix and a vector, the linear ACTION below. -/
partial def scalarMul (a b : Value) : Except String Value :=
  binOp "multiplication" "the product" (· * ·) (· * ·)
    (fun (xa, xb) (ya, yb) d =>
      Value.mkAlg (xa * ya + xb * yb * Rat.ofInt d) (xa * yb + xb * ya) d)
    matApply a b

/-- `M v` — SPEC.md's `M*v`, and the same operation its juxtaposition spells.
Mutually recursive with the product above because the ENTRIES multiply by the
same operation the whole action is one arm of, and a matrix of matrices is a
presentation this data model admits.

Two things are CHECKED and neither is joined quietly:

- the SHAPE. `Matₙ` applies to a vector of length `n` and to no other, which
  is the whole reason a vector is not presented as a one-column matrix;
- the entry domain. Like the binary set operations, this backend REFUSES to
  join two element domains rather than guessing — the preferred-canonical-map
  registry the surface joins literals with is not readable from here — so the
  refusal names the ascription that fixes it. CEILING, documented: SPEC.md
  ascribes both operands (`Mat₂(ℚ)`, `ℚ²`), and a mixed pair says so. -/
partial def matApply (n : Nat) (e : Domain) (rows : Array (Array Value))
    (ve : Domain) (comps : Array Value) : Except String Value := do
  if comps.size != n then
    .error s!"{(Domain.matrix n e).render} does not apply to a vector of length \
{comps.size}: a matrix applies to vectors of its own size, and these shapes do \
not meet"
  else if e != ve then
    .error s!"{(Domain.matrix n e).render} and {(Domain.vector comps.size ve).render} \
are over different domains: this backend applies a matrix to a vector over ONE \
domain and does not join them — ascribe the operands to the domain you mean"
  else
    return .vec n e (← rows.mapM fun row =>
      (row.zip comps).foldlM (init := zeroOf e) fun acc (a, x) => do
        scalarAdd acc (← scalarMul a x))

end

/-- Unary; the arity of negation is one, so this deviates from the sibling
binary signatures on purpose. -/
def scalarNeg : Value → Except String Value
  | .int z => .ok (.int (-z))
  | .rat q => .ok (.rat (-q))
  | .mod n v => .ok (Value.mkMod n (-(Int.ofNat v)))
  | .alg a b d => Value.mkAlg (-a) (-b) d
  | v => .error (noArithmetic "negation" v)

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
      -- the fold multiplies up from 1, so a base without scalar arithmetic
      -- would otherwise be reported as a multiplication by a `1` nobody wrote
      -- — or, at exponent 0, answer with that `1`
      if !hasScalarArithmetic a then .error (noArithmetic "exponentiation" a) else
      let one : Value := match a with
        | .rat _ => .rat 1
        | .mod n _ => Value.mkMod n 1
        | _ => .int 1
      (List.range k).foldlM (fun acc _ => scalarMul acc a) one

/-- Exact division in ℚ. Integer operands are promoted along `ℤ ⊆ ℚ`, so the
result is a `.rat` even when it is integral. Division in `ℤ/n` is not
provided (that ring is a field only for prime `n`) and fails loudly. -/
def scalarDiv (a b : Value) : Except String Value :=
  match promote a b with
  -- in a quadratic field, division is multiplication by the conjugate over
  -- the NORM `ya² − yb²d`, which vanishes only for the zero divisor (`d` is
  -- not a square, so `ya² = yb²d` forces both to be zero)
  | some (.alg (xa, xb) (ya, yb) d) =>
      let n := ya * ya - yb * yb * Rat.ofInt d
      if n == 0 then .error "division by zero"
      else Value.mkAlg ((xa * ya - xb * yb * Rat.ofInt d) / n)
        ((xb * ya - xa * yb) / n) d
  | some (.int x y) => ratDiv (Rat.ofInt x) (Rat.ofInt y)
  | some (.rat x y) => ratDiv x y
  -- `ℤ/n` is a field only for prime `n`, so division there is not provided,
  -- and a matrix does not DIVIDE a vector — the inverse is a method (`M⁻¹`),
  -- which is a different operation with a different failure
  | some (.matVec n e ..) =>
      .error s!"division is not defined between {(Domain.matrix n e).render} and \
a vector: the matrix that undoes an action is its INVERSE, `M⁻¹ b`"
  | some (.mod ..) | some (.same ..) | none =>
      .error (noCommonKind "division" "the quotient" a b)
where
  ratDiv (x y : Rat) : Except String Value :=
    if y == 0 then .error "division by zero" else .ok (.rat (x / y))

/-! ## Presentation helpers -/

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
  -- a formal power series over a countable coefficient domain is a sequence
  -- of them, which is UNCOUNTABLE — `Cardinality` deliberately cannot state
  -- that, so it is reported as unstatable rather than given ℵ₀
  | .series _ => none
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
  | .vector n e =>
      match domainCard e with
      | some (.finite k) => some (.finite (k ^ n))
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

/-- Is `x` an element of `d`? TOTAL over `Domain` — every domain decides, so
a domain added later fails this match instead of reaching a "no membership
test" path that no longer exists.

`c[x]` recurses on the COEFFICIENTS, so `x ∈ ℤ[x]` and `p ∈ ℤ[x]` are settled
by the same judgment that settles `-3 ∈ ℤ` — and a polynomial over ℤ is an
element of ℚ[x] for the reason it always was, coefficient by coefficient. A
scalar is its own constant polynomial. -/
private partial def inDomain? (d : Domain) (x : Value) : Bool :=
  match d, x with
  | .nat, .int z => z ≥ 0
  | .nat, .rat q => q.den == 1 && q.num ≥ 0
  | .nat, _ => false
  | .int, v => isIntegral v
  | .rat, .int _ => true
  | .rat, .rat _ => true
  | .rat, _ => false
  | .mod n, .mod m _ => m == n
  -- an integer names its residue class
  | .mod _, .int _ => true
  | .mod _, _ => false
  -- ℝ and ℂ: every rational is one, and the exact algebraic values are the
  -- others — a NEGATIVE radicand is not real (DESIGN.md §Exact number
  -- systems). Deciding membership does not claim the domain is enumerated:
  -- the reals this slice cannot present are still elements of ℝ, and a value
  -- it CAN present is placed exactly
  | .real, .alg _ _ d => d > 0
  | .real, .int _ | .real, .rat _ => true
  | .real, _ => false
  | .complex, .int _ | .complex, .rat _ | .complex, .alg .. => true
  | .complex, _ => false
  | .poly c, .poly _ cs => cs.all (inDomain? c)
  | .poly c, v => inDomain? c v
  -- SPEC.md's `assert Tf ∈ ℝ[[t]]`: a series is one of `E[[t]]` when its
  -- coefficient domain IS `E`, and that is the whole judgment made here.
  -- The tag is a NORMAL FORM rather than a guess — `coerceValue`'s structural
  -- congruence maintains it at every boundary a series crosses (the
  -- ascription, the wire decode) — so the ascription this answers for always
  -- meets a matching tag. A MISMATCH is not answered at all: `ℚ[[t]] ⊆ ℝ[[t]]`
  -- is the canonical-map registry's claim and this backend may not restate it
  -- (`normalSubset` refuses `dom ⊆ dom` for exactly that reason), so the
  -- executor refuses there rather than returning a `false` that would be a
  -- wrong answer. `anything else` is a theorem: no other value is a series.
  | .series e, .seriesV c _ => e == c
  | .series _, _ => false
  -- a matrix is one of Matₙ(e) when its size agrees and every entry is in e;
  -- a function's domain is the arrow it was declared over
  | .matrix n e, .mat m _ rows => n == m && rows.all (·.all (inDomain? e))
  | .matrix .., _ => false
  -- …and a vector is one of `Eⁿ` when its LENGTH agrees and every component
  -- is in `E`, the same judgment one level down
  | .vector n e, .vec m _ comps => n == m && comps.all (inDomain? e)
  | .vector .., _ => false
  | .funcs s t, .func s' t' _ _ => s == s' && t == t'
  | .funcs .., _ => false

private def domainContains (d : Domain) (x : Value) : Value := .bool (inDomain? d x)

/-- `x ∈ a - b`: in the first domain and not in the second. The ONE decision
behind a difference set, so `x ∈ ℂ - ℚ` and `S ⊆ ℂ - ℚ` cannot disagree —
they are two spellings of this, not two implementations of it. -/
private def diffMember (a b : Domain) (x : Value) : Bool :=
  inDomain? a x && !inDomain? b x

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
  -- a subspace of ℚⁿ is countable, and the TRIVIAL one is the single-element
  -- set {0}: the basis size decides which, exactly as it decides the dimension
  | .span _ basis =>
      .ok (if basis.isEmpty then .finite 1 else .countablyInfinite)
  -- a coset is in bijection with its KERNEL — translation is a bijection —
  -- so its size is the kernel's, and nothing about the offset enters
  | .coset _ kernel =>
      match domainCard kernel with
      | some c => .ok c
      | none => .error (.badRequest
          s!"the native backend cannot express the cardinality of a coset of \
{kernel.render}")
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
  /-- A subspace of ℚⁿ, by its REDUCED basis — which is canonical, so this
  normal form compares as data exactly like the two above. -/
  | span (n : Nat) (basis : Array Value)
  /-- A coset by its CANONICAL representative (constant term zero) and its
  kernel — canonical for the same reason, so it compares as data too. -/
  | coset (offset : Value) (kernel : Domain)

private def scalarSortable (vs : Array Value) : Bool :=
  vs.all (fun v => match v with | .int _ | .rat _ => true | _ => false)
  || (match (vs[0]? : Option Value) with
      | some (.mod n _) => vs.all fun v => match v with | .mod m _ => m == n | _ => false
      | _ => false)

private def sortDedup (vs : Array Value) : Array Value :=
  dedupSorted (vs.qsort fun a b => scalarCmp a b == some .lt)

private def normalizeDomain (d : Domain) : Except ExecError SetNormal :=
  match domainCard d with
  -- A domain whose SIZE this slice cannot state is still a set with a
  -- membership test and an identity, and that is all this normal form is for:
  -- `S ⊆ ℂ` and `S ∈ 𝒫(ℂ)` are decided element by element, and `ℝ = ℂ` by the
  -- two domains themselves. Only the FINITE case needs a cardinality, because
  -- only it expands to an element list. (`ℂ.cardinality()` still reports that
  -- it cannot be stated — that is `presCard`'s question, not this one.)
  | none | some .countablyInfinite => .ok (.dom d)
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
  -- the basis arrives reduced (`Value.mkSpanBasis` is the only constructor),
  -- so the presentation IS the normal form
  | .setObj (.span n basis) => .ok (.span n basis)
  -- the offset arrives canonical (`Value.mkCoset` is the only constructor),
  -- so the presentation IS the normal form — the span's discipline exactly
  | .setObj (.coset offset kernel) => .ok (.coset offset kernel)
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
      -- both sides are deduped, so equal sizes plus one-way membership IS
      -- equality. The zip settles two SORTED sides in one pass; the quadratic
      -- fallback runs only for elements that have no order here (exact
      -- algebraic values), where the answer cannot be read off a sequence
      a.size == b.size &&
        ((a.zip b).all (fun (x, y) => valueEq x y == some true)
          || a.all fun x => b.any fun y => valueEq x y == some true)
  | .prog f1 s1, .prog f2 s2 => f1 == f2 && s1 == s2
  | .dom d1, .dom d2 => d1 == d2
  -- the reduced echelon basis is a FUNCTION of the subspace, so two spans are
  -- equal exactly when their bases are — no search, no double inclusion
  | .span n a, .span m b => n == m && a == b
  -- SPEC.md's `assert M.ker() = {0}`. A span is finite only when it is the
  -- TRIVIAL subspace, and then it is the one-element set {0} — where `0` is
  -- the mathematician's own spelling of the zero of the ambient space, the
  -- one element every additive group shares (`Value.isSpanZero`, which reads
  -- a scalar zero and nothing else across that boundary). A span with a
  -- nonempty basis is infinite and is inside no finite list.
  | .span n a, .fin es | .fin es, .span n a =>
      a.isEmpty && es.size == 1 && Value.isSpanZero n es[0]!
  -- two cosets are equal exactly when their canonical representatives and
  -- their kernels are: no subtraction, no search
  | .coset o1 k1, .coset o2 k2 => k1 == k2 && o1 == o2
  | _, _ => false

/-! ## Inclusion by presentation normalization

`A ⊆ B` is decided from the same canonical forms as equality, and refuses
loudly wherever the presentations do not settle it. Only two things are ever
answered `false` without a decision procedure, and both are theorems about
the forms themselves: a `dom` normal form is INFINITE — finite domains are
the ones that expand to `fin`, and the rest reach this form whether their
size is countable or, since ℝ and ℂ normalize for comparison, not statable at
all — and a `prog` normal form is unbounded. Neither fits inside a finite
list.

The deliberate hole: `dom ⊆ dom` between DIFFERENT domains. `ℕ ⊆ ℤ ⊆ ℚ` is
the preferred-canonical-map registry's claim (DESIGN.md §Coercions), not a
fact this backend may restate — so it is refused here rather than answered
twice. -/

private def normalSubset : SetNormal → SetNormal → Except ExecError Bool
  | .fin a, .fin b =>
      .ok (a.all fun x => b.any fun y => valueEq x y == some true)
  | .fin a, .dom d => .ok (a.all (inDomain? d))
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
  -- one subspace lies in another exactly when each of its basis vectors does,
  -- which is the same solved reduction membership is
  | .span n a, .span m b =>
      if n != m then .ok false
      else Except.mapError ExecError.badRequest <|
        a.foldlM (init := true) fun acc v => do return acc && (← Value.spanContains m b v)
  | .fin es, .span n b =>
      Except.mapError ExecError.badRequest <|
        es.foldlM (init := true) fun acc v => do return acc && (← Value.spanContains n b v)
  -- a span is inside a finite list only when it IS finite — the trivial
  -- subspace {0}, the same theorem the two arms above it use for a countably
  -- infinite domain and an unbounded progression
  | .span n a, .fin es =>
      .ok (a.isEmpty && es.any (Value.isSpanZero n))
  -- a coset of the constants is INFINITE (the kernel is), so it is inside no
  -- finite list — the theorem the `dom` and `prog` arms above already use.
  -- Everything else about it refuses: an inclusion between two cosets is a
  -- claim this presentation does not decide
  | .coset .., .fin _ => .ok false
  | .fin es, .coset o _ => .ok (es.all (Value.cosetContains o))
  | .coset .., rhs | rhs, .coset .. =>
      let what := match rhs with
        | .dom d => d.render
        | .coset o k => s!"the coset {o.render} + {k.render}"
        | _ => "that presentation"
      .error (.badRequest
        s!"the native backend decides inclusion in a coset of the constants \
for an explicit finite set only; {what} is not one")
  | .span .., rhs | rhs, .span .. =>
      let what := match rhs with
        | .dom d => d.render
        | .prog f s => s!"the progression starting {(Value.ofRat f).render} with \
step {(Value.ofRat s).render}"
        | _ => "that presentation"
      .error (.badRequest
        s!"the native backend decides inclusion between a subspace of ℚⁿ and an \
explicit finite set or another subspace; {what} is neither")

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

/-- SPEC.md's `∑_{a ∈ roots} a` and `∏_{a ∈ roots} a`, over an explicit finite
set: the elements are DEDUPLICATED first, because a set's aggregate counts
each element once however the literal was written.

The EMPTY set answers with the identity — `0` for a sum and `1` for a product
— and those are the mathematical answers, pinned as such. Everything else
must have SCALAR ARITHMETIC first (`hasScalarArithmetic`, the predicate the
power path already uses): a fold seeded with an identity over values that have
none would otherwise report that seed, which is an answer nobody wrote. -/
private def foldSet (op what : String) (seed : Value)
    (step : Value → Value → Except String Value) (o : Obj)
    : Except ExecError Value := do
  let (_, elems) ← finiteElems op o
  let elems := dedupValues elems
  for v in elems do
    unless hasScalarArithmetic v do
      .error (.badRequest s!"{what} over this set is not defined: {v.render} has \
no arithmetic here, so the fold would report its own seed ({seed.render}) \
instead of refusing")
  Except.mapError ExecError.badRequest (elems.foldlM step seed)

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

/-- A ℚ-entry matrix receiver, as exact rationals. Partiality WITHIN the
routed shape: the routes send only `Mat(ℚ)` here, and an entry that is not a
rational inside one is the loud error a zero polynomial's degree is. -/
private def ratMatrix (op : String) : Obj → Except ExecError (Nat × Array (Array Rat))
  | .elem (.matrix n _) (.mat _ _ rows) =>
      match rows.mapM (·.mapM toRat?) with
      | some rs =>
          if rs.size == n && rs.all (·.size == n) then .ok (n, rs)
          else .error (.badRequest s!"{op}: the matrix is not {n}×{n}")
      | none => .error (.badRequest
          s!"{op} reads a matrix over ℚ, and this one has an entry that is not \
a rational")
  | o => .error (.badRequest s!"{op} expects a matrix receiver, got {o.presentation}")

/-- A generating set of `{v : M v = 0}`, read off the reduced row echelon form
of `M`: each column carrying no pivot is FREE, and setting it to 1 while the
pivot columns take the negated entries of that column is the kernel vector it
contributes. The generators go through `Value.mkSpanBasis` like every other
span, which is what reduces them to the presentation's normal form. -/
private def kernelGens (n : Nat) (rows : Array (Array Rat)) : Array Value := Id.run do
  let red := Value.rref n rows
  let pivots := red.filterMap fun row => (Array.range n).find? (fun k => row[k]! != 0)
  let mut gens : Array Value := #[]
  for free in [0:n] do
    if !pivots.contains free then
      let mut comps := (Array.replicate n (0 : Rat)).set! free 1
      for i in [0:pivots.size] do
        comps := comps.set! pivots[i]! (-(red[i]![free]!))
      gens := gens.push (.vec n .rat (comps.map Value.rat))
  return gens

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
  -- SPEC.md §Differentials' `(d/dx)(f)`. NATIVE, and deliberately: the
  -- derivative of a KNOWN polynomial is `i·c_i` shifted down by one, which is
  -- exact coefficient arithmetic this engine already owns. There is therefore
  -- no backend to ask and no certificate to check — the pre-ruling that put
  -- U8's reply checks in `Value.lean`'s arithmetic floor presumed a backend
  -- computed this, and not having one is strictly stronger than checking one.
  -- `mkPoly` drops the trailing zero, so the derivative of a CONSTANT is the
  -- zero polynomial rather than a degree-0 lie.
  | "poly_derivative" =>
      match o with
      | .elem (.poly c) (.poly _ coeffs) =>
          -- the coefficient stays in its own ring: `scalarMul` promotes the
          -- integer factor into whatever the coefficient is, so `i·c` over
          -- ℤ/n comes back reduced and over ℚ comes back rational
          Except.mapError ExecError.badRequest do
            return Value.mkPoly c (← (Array.range (coeffs.size - 1)).mapM fun i =>
              scalarMul (.int (Int.ofNat (i + 1))) coeffs[i + 1]!)
      | o => .error (.badRequest
          s!"poly_derivative expects a polynomial receiver, got {o.presentation}")
  -- SPEC.md §Indefinite integration's `∫ f dx`. NATIVE for the reason the
  -- derivative is: `cᵢ/(i+1)` shifted up by one is exact coefficient
  -- arithmetic this engine owns, so no backend is asked and none can lie.
  -- The result is a COSET of the constants — the complete set of primitives,
  -- not one of them — built through `Value.mkCoset`, which canonicalizes.
  | "poly_antiderivative" =>
      match o with
      | .elem (.poly c) (.poly _ coeffs) =>
          Except.mapError ExecError.badRequest do
            -- `scalarDiv` lands in ℚ, so ∫ over ℤ[x] is a coset of ℚ[x]:
            -- the antiderivative of an integer polynomial has rational
            -- coefficients, and saying so is the whole of it
            let kernel := if c == .int then Domain.rat else c
            let up ← (Array.range coeffs.size).mapM fun i =>
              scalarDiv coeffs[i]! (.int (Int.ofNat (i + 1)))
            let (offset, k) ← Value.mkCoset
              (Value.mkPoly kernel (#[Value.ofRat 0] ++ up)) kernel
            return .cosetV offset k
      | o => .error (.badRequest
          s!"poly_antiderivative expects a polynomial receiver, got {o.presentation}")
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
          return .bool (diffMember p m x)
      -- SPEC.md's `(1, 1, 2) ∈ W` and `(1, 1, 0) ∉ W`: the linear system is
      -- SOLVED against the reduced basis, so both DECIDE
      | .setObj (.span n basis) => do
          let x ← scalarArg "contains" args
          return .bool (← Except.mapError ExecError.badRequest
            (Value.spanContains n basis x))
      -- SPEC.md's `{h ∈ ∫ f dx | …}`: the kernel is the CONSTANTS, so
      -- membership is exactly "agrees with the offset above degree zero" —
      -- decided, with no subtraction and no search
      | .setObj (.coset offset _) => do
          let x ← scalarArg "contains" args
          return .bool (Value.cosetContains offset x)
      | o =>
        let x ← scalarArg "contains" args
        match o with
        | .setObj (.finite _ elems) => return .bool (memOf elems x)
        | .setObj (.arithProg _ first step last?) => progContains first step last? x
        -- a series against a series RING whose coefficient domains differ is
        -- the one membership this backend will not answer: the inclusion
        -- between two coefficient domains belongs to the canonical-map
        -- registry, and `false` here would be a wrong answer rather than a
        -- missing one. Ascribe the series to the ring you mean.
        | .setObj (.domainSet (.series e)) | .domainObj (.series e) =>
            match x with
            | .seriesV c _ =>
                if e == c then return .bool true
                else .error (.badRequest
                  s!"whether a series over {c.render} lies in \
{(Domain.series e).render} is the preferred-canonical-map registry's claim, \
not one this backend restates: ascribe the series to \
{(Domain.series e).render} at its binding, which is where a coefficient \
domain is carried across")
            | _ => return .bool false
        | .setObj (.domainSet d) | .domainObj d => return domainContains d x
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
              return .bool (elems.all (diffMember p m))
          | o => .error (.badRequest
              s!"the native backend decides inclusion in {rhs.presentation} for an \
explicit finite set only, and {o.presentation} is not one")
      | rhs => return .bool (← normalSubset (← normalizeSet o) (← normalizeSet rhs))
  -- SPEC.md §A composed computation: Σ and Π over a finite set
  | "set_sum" => foldSet "set_sum" "the sum" (.int 0) scalarAdd o
  | "set_prod" => foldSet "set_prod" "the product" (.int 1) scalarMul o
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
          else if Value.nonNegSurd a b d then return v
          else algValue (Value.mkAlg (-a) (-b) d)
      | v =>
          let some q := toRat? v
            | .error (.badRequest s!"{v.render} has no modulus here")
          return Value.ofRat (if q.blt 0 then -q else q)
  -- SPEC.md §Subspaces and spans: the dimension is the SIZE of the reduced
  -- basis, which is what the echelon form was computed for
  | "span_dim" =>
      match o with
      | .setObj (.span _ basis) => .ok (.int (Int.ofNat basis.size))
      | o => .error (.badRequest
          s!"span_dim expects a subspace, got {o.presentation}")
  -- SPEC.md §Vectors and matrices: `M.rank()` and `M.ker()`. Both are reads of
  -- the SAME reduced row echelon form the span presentation already owns — the
  -- rank is its row count and the kernel is its free columns — so they are
  -- exact native decisions and no backend is asked
  | "mat_rank" => do
      let (n, rows) ← ratMatrix "mat_rank" o
      return .int (Int.ofNat (Value.rref n rows).size)
  | "mat_ker" => do
      let (n, rows) ← ratMatrix "mat_ker" o
      Except.mapError ExecError.badRequest (Value.mkSpan n (kernelGens n rows))
  -- SPEC.md §A composed computation's `C.trace()`. A STRUCTURAL read of the
  -- diagonal, like `deg` — the engine genuinely decides it over every entry
  -- domain whose elements add, so it is native and no backend is asked
  | "mat_trace" =>
      match o with
      | .elem (.matrix n e) (.mat _ _ rows) =>
          Except.mapError ExecError.badRequest <|
            (Array.range n).foldlM (init := zeroOf e) fun acc i =>
              match (rows[i]?).bind (·[i]?) with
              | some v => scalarAdd acc v
              | none => .error s!"the matrix is not {n}×{n}"
      | o => .error (.badRequest
          s!"mat_trace expects a matrix receiver, got {o.presentation}")
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
  { backend := `native, opId := "poly_derivative",
    accepts := #[.elemOf (.polyOver .anyDom)] },
  -- the antiderivative divides, so it accepts the two coefficient rings whose
  -- fraction field this slice presents; over ℤ/n it is an honest capability
  -- gap rather than an arm that guesses
  { backend := `native, opId := "poly_antiderivative",
    accepts := #[.elemOf (.polyOver (.exact .int)),
                 .elemOf (.polyOver (.exact .rat))] },
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
  -- …and the two aggregations, which build no set at all but fold one
  { backend := `native, opId := "set_sum", accepts := #[.finiteSet] },
  { backend := `native, opId := "set_prod", accepts := #[.finiteSet] },
  { backend := `native, opId := "annihilator_cyclic", accepts := #[.cyclicMod] },
  -- the subspace of ℚⁿ, and the two reads of a ℚ matrix's echelon form
  { backend := `native, opId := "span_dim", accepts := #[.spanSet] },
  { backend := `native, opId := "mat_rank",
    accepts := #[.elemOf (.matrixOver (.exact .rat))] },
  { backend := `native, opId := "mat_ker",
    accepts := #[.elemOf (.matrixOver (.exact .rat))] },
  -- the trace reads the diagonal, so it is defined over every entry domain
  { backend := `native, opId := "mat_trace",
    accepts := #[.elemOf (.matrixOver .anyDom)] },
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
