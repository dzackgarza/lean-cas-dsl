/-
Core data model of the CAS: presentations and values.

Everything here is first-order, serializable data — these types are stored
in persistent env extensions (bindings, routes, representative
presentations), so they contain no closures and no host handles. An opaque
backend handle is never a semantic value (anti-drift: backend results are
reflected into these Lean values or the call fails honestly).
-/
import Lean

namespace CasDsl

/-- A presentation of a mathematical domain (a "parent" in CAS speak). -/
inductive Domain where
  | nat
  | int
  | rat
  /-- `ℝ`, spelled `ℝ`, `R` or `RR`. Its inhabitants here are the exact
  ALGEBRAIC reals `Value.alg` presents (`√2`); the reals this slice cannot
  present symbolically are still elements of ℝ, so the domain is inhabited
  without being enumerated, measured, or ordered. No analysis semantics
  (DESIGN.md §Exact number systems). -/
  | real
  /-- `ℂ`, spelled `ℂ` or `CC`. Inhabited by the same exact algebraic values,
  with a NEGATIVE radicand: `√(-1)` is `i`. -/
  | complex
  /-- `ℤ/n`. -/
  | mod (n : Nat)
  /-- Univariate polynomials `coeff[x]`. -/
  | poly (coeff : Domain)
  /-- Square `n × n` matrices over `entry` (square-only in this slice). -/
  | matrix (n : Nat) (entry : Domain)
  /-- `Eⁿ` — the vectors of length `n` over `E`, SPEC.md's `ℚ²` and `ℚ³`.

  A vector is NOT a matrix here: `matrix` is square by construction, and a
  column of length `n` is not an `n × n` object. Keeping them apart is what
  lets matrix application be SHAPE-CHECKED (`Mat₂(ℚ)` applied to a vector of
  ℚ³ is a loud refusal) instead of silently reinterpreting one as the other. -/
  | vector (n : Nat) (entry : Domain)
  /-- `src → tgt`, the domain a function binding is ascribed to. -/
  | funcs (src tgt : Domain)
  deriving BEq, Repr, Hashable, Inhabited

/-- Cardinality values the slice can express. -/
inductive Cardinality where
  | finite (n : Nat)
  | countablyInfinite
  deriving BEq, Repr, Hashable, Inhabited

/-- A trusted CAS value. Backend results reflect into these; small values
are materialized eagerly in this slice (a choice, not a permanent semantic
requirement — see DESIGN.md §Large computations). -/
inductive Value where
  | int (z : Int)
  | rat (q : Rat)
  /-- Element of `ℤ/n`; `v` is normalized `< n` on construction. -/
  | mod (n : Nat) (v : Nat)
  /-- Coefficients ascending by degree, no trailing zeros. -/
  | poly (coeff : Domain) (coeffs : Array Value)
  | mat (n : Nat) (entry : Domain) (rows : Array (Array Value))
  /-- An element of `Eⁿ`, SPEC.md's `(1, 2)`. `n` is the LENGTH — matrix
  application is shape-checked against it, and two vectors of different
  lengths are unequal rather than incomparable. -/
  | vec (n : Nat) (entry : Domain) (comps : Array Value)
  /-- Unit convention and factor order belong to the backend that produced
  it; only this neutral shape is semantic. -/
  | factorization (unit : Value) (factors : Array (Value × Nat)) (dom : Domain)
  /-- An ideal presented by generators (e.g. an annihilator in `ℤ`). -/
  | idealV (gens : Array Value) (ring : Domain)
  /-- A finite set of elements of one domain, as an executor RESULT (the roots
  of a polynomial). `Denote.ofValue` turns it into the ordinary set object
  `SetPresentation.finite`, so the set methods apply to it like any other
  set; it is a `Value` only because that is what crosses the backend wire.
  CEILING: a backend can return an explicit finite set, nothing wider. -/
  | setV (elems : Array Value) (dom : Domain)
  /-- The third set an executor may return: a SUBSPACE of `ℚⁿ`, presented by
  a basis in reduced row echelon form (`Value.mkSpanBasis`). SPEC.md's
  `span_QQ{u₁, u₂}` and `M.ker()` are both this.

  The RREF is what makes the presentation answer the three questions SPEC.md
  asks of it: `dim` is the basis SIZE, membership is the reduction of a vector
  against the basis, and equality is the basis compared as data — the reduced
  echelon form of a subspace is CANONICAL, so two spans are equal exactly when
  their normalized bases are.

  CEILING: over ℚ, which is `span_QQ`'s own base and the entry domain of every
  matrix this slice routes. -/
  | spanV (n : Nat) (basis : Array Value)
  /-- The other set an executor may return: an arithmetic progression, which
  is what the image of a linear map on ℕ is (`e.image()`). Like `setV` it is
  a `Value` only because that is what an executor returns; `Denote.ofValue`
  turns it into the ordinary `SetPresentation.arithProg` a `{0, 2, 4, ...}`
  literal produces, so there is ONE notion of set, not a second one.
  CEILING: these two shapes — an explicit finite list and a progression. -/
  | progV (dom : Domain) (first step : Value) (last? : Option Value)
  /-- An exact ALGEBRAIC number `a + b√d`: `a` and `b` rational, `d` a
  SQUARE-FREE integer other than 0 and 1, `b ≠ 0`. The sign of `d` is the
  imaginary direction — `√(-1)` is `i` — so it also decides which domain the
  value presents: ℝ when `d > 0`, ℂ when `d < 0`.

  `Value.mkAlg` is how every value the surface produces is built: it moves the
  square part of `d` into `b` and returns the RATIONAL when `b` comes out
  zero, so `√8` IS `2√2` and a surd is never a rational in disguise. (Test and
  prelude FIXTURES are written in normal form directly, stating the value they
  mean — nothing computed skips the constructor.) Everything stays exact —
  nothing here is ever a float.

  CEILING: ONE square root over ℚ. `√2 + √5` leaves this presentation and is
  a loud refusal, never an approximation and never a dropped term. -/
  | alg (a b : Rat) (d : Int)
  /-- A numerical APPROXIMATION of an exact value: SPEC.md's
  `map √2 to ℝ/O(1/10^{10})`, displayed as `1.4142135623 + O(1/10^{10})`.

  `ℝ/O(ε)` is SUGAR for a requested absolute tolerance and NOT a quotient —
  `|a − b| < ε` is not transitive, so there are no classes for this to be an
  element of. It is therefore a RESULT (`valueDom?` gives it no domain, like a
  factorization or a cardinal) rather than an element of a number system, and
  arithmetic on it is refused rather than given an invented error calculus.

  Four fields, each load-bearing: the EXACT value approximated (kept, so
  nothing is lost by asking for a decimal), the decimal presenting it — whose
  shown digits ARE the claim — the tolerance that was REQUESTED (what the
  display names), and the bound the backend certified. `Value.mkApprox` is the
  one constructor: it refuses unless the certificate holds. -/
  | approx (exact : Value) (decimal : String) (eps achieved : Rat)
  | cardinal (c : Cardinality)
  | bool (b : Bool)
  /-- `binder ↦ body` in `src → tgt`. The body is the exact polynomial the
  binder generates, so the identities SPEC.md asserts about functions
  (`h(-t) = h(t)`, `(f ∘ g)(t) = t⁶`) are decided by the polynomial engine
  rather than sampled. The binder is a BOUND NAME, not data: equality
  compares domains and bodies (`Native.valueEq`). -/
  | func (src tgt : Domain) (binder : Lean.Name) (body : Value)
  deriving BEq, Repr, Inhabited

/-- Presentation of a set object. Semantic sets are not replaced by ordered
lists merely because indexing exists; the presentation records the
registered enumeration choice implicitly (first/step order for
progressions, literal order for finite sets, a registered convention for
`domainSet`). -/
inductive SetPresentation where
  | finite (dom : Domain) (elems : Array Value)
  /-- `{a, b, ...}` / `{a, ..., z}`: first, step, optional inclusive last. -/
  | arithProg (dom : Domain) (first step : Value) (last? : Option Value)
  /-- The underlying set of a domain (`ℤ` used as a set). -/
  | domainSet (d : Domain)
  /-- `A × B`. A PRESENTATION rather than an element list because `Value` has
  no pair: the product is denoted exactly, and the operations that need its
  elements (`nth`, `contains`, set equality) fail honestly, while the one
  SPEC.md asks for — `|A × B|` — is exact cardinal arithmetic. -/
  | product (a b : SetPresentation)
  /-- `𝒫(A)`, spelled `𝒫(A)` or `2^A`. A presentation for the same reason:
  its elements are SETS, which no `Value` presents. `|𝒫(A)| = 2^|A|` is
  cardinal arithmetic, and `X ∈ 𝒫(A)` is the subset judgment. -/
  | powerset (s : SetPresentation)
  /-- `span_QQ{u₁, u₂} ≤ ℚⁿ` — a SUBSPACE of `ℚⁿ`, presented by a basis in
  reduced row echelon form. A set like any other (its elements are vectors,
  which `Value.vec` presents), so `∈`, `=` and `⊆` reach it through the
  ordinary `Sets` methods; what it adds is `dim`, and the RREF is what makes
  all four decidable. See `Value.mkSpanBasis`. -/
  | span (n : Nat) (basis : Array Value)
  /-- `ℂ - ℚ` (SPEC.md §Polynomials). A presentation again, and the minimal
  one the assertion needs: MEMBERSHIP is decided pointwise (`x ∈ a` and
  `x ∉ b`), which is what `q.roots() ⊆ ℂ - ℚ` asks, and everything that would
  need an element list — a cardinality, a canonical form to compare — refuses.
  DOMAINS on both sides deliberately: the difference of two finite sets is
  `A \ B`, which COMPUTES (§Sets), and this constructor is not a second
  spelling of it. -/
  | domainDiff (a b : Domain)
  deriving BEq, Repr, Inhabited

/-- The thing a notebook binding names: an object with a presentation.
Category memberships are NOT stored here — the profile is computed
(`Std.profileOf`), keeping presentation and category judgment separate. -/
inductive Obj where
  | elem (dom : Domain) (v : Value)
  | domainObj (d : Domain)
  | setObj (s : SetPresentation)
  /-- Module fixture: the ℤ-module ℤ/n (plan: inheritance demo without a
  premature Macaulay2/Singular bridge). -/
  | cyclicModule (n : Nat)
  deriving BEq, Repr, Inhabited

namespace Domain

/-- Mathematician-facing rendering. -/
partial def render : Domain → String
  | .nat => "ℕ"
  | .int => "ℤ"
  | .rat => "ℚ"
  | .real => "ℝ"
  | .complex => "ℂ"
  | .mod n => s!"ℤ/{n}"
  | .poly c => s!"{c.render}[x]"
  | .matrix n e => s!"Mat{subscript n}({e.render})"
  | .vector n e => s!"{e.render}{superscript n}"
  | .funcs s t => s!"{s.render} → {t.render}"
where
  subscript (n : Nat) : String := digitsOf "₀₁₂₃₄₅₆₇₈₉" n
  /-- SPEC.md writes the vector domains in superscript (`ℚ²`, `ℚ³`), which is
  also the spelling the surface reads back (`Syntax.casSupPow`). -/
  superscript (n : Nat) : String := digitsOf "⁰¹²³⁴⁵⁶⁷⁸⁹" n
  digitsOf (digits : String) (n : Nat) : String :=
    String.ofList <| (toString n).toList.map fun c =>
      if c.isDigit then digits.toList[c.toNat - '0'.toNat]! else c

/-- The same rendering in LaTeX (DESIGN.md §LaTeX-first display). A domain
always has one — the ℤ/n spelling is the full `\mathbb{Z}/n\mathbb{Z}`, since
`\mathbb{Z}/5` alone reads as a quotient by an element. -/
partial def latex : Domain → String
  | .nat => "\\mathbb{N}"
  | .int => "\\mathbb{Z}"
  | .rat => "\\mathbb{Q}"
  | .real => "\\mathbb{R}"
  | .complex => "\\mathbb{C}"
  | .mod n => "\\mathbb{Z}/" ++ toString n ++ "\\mathbb{Z}"
  | .poly c => c.latex ++ "[x]"
  | .matrix n e => "\\mathrm{Mat}_{" ++ toString n ++ "}(" ++ e.latex ++ ")"
  | .vector n e => e.latex ++ "^{" ++ toString n ++ "}"
  | .funcs s t => s.latex ++ " \\to " ++ t.latex

instance : ToString Domain := ⟨render⟩

end Domain

namespace Value

/-- Normalize an integer mod `n` into `Value.mod`. -/
def mkMod (n : Nat) (z : Int) : Value :=
  if n == 0 then .int z else .mod n (z.emod n).toNat

/-- Zero in whatever domain the coefficient presents. `ℤ/n`'s zero counts:
a normal form that stripped only ℤ and ℚ zeros would leave `t + 7` over ℤ/5
one degree too long, and two equal polynomials comparing unequal. -/
private def isZeroCoeff : Value → Bool
  | .int z => z == 0
  | .rat q => q == 0
  | .mod _ v => v == 0
  | _ => false

/-- A rational as the value presenting it: an integral rational is the
INTEGER, so a computed result compares with a literal one. -/
def ofRat (q : Rat) : Value := if q.den == 1 then .int q.num else .rat q

/-- Where trial division stops looking for a square factor of a radicand.
Past it, certifying square-freeness would need a prime above the cap, so the
answer is a loud refusal rather than an unnormalized radical — which would
compare unequal to its own normal form and quietly break `√8 = 2√2`. -/
def squareFactorCap : Nat := 100000

/-- `d = s²·core` with `core` square-free and `s > 0`: the normal form a
radical is kept in. The sign rides on `core`, since `√(-4)` is `2i`. -/
def squareFreePart (d : Int) : Except String (Int × Nat) := Id.run do
  let sign : Int := if d < 0 then -1 else 1
  let mut n : Nat := d.natAbs
  let mut s : Nat := 1
  let mut k : Nat := 2
  while k ≤ squareFactorCap && k * k ≤ n do
    while k * k ≤ n && n % (k * k) == 0 do
      n := n / (k * k)
      s := s * k
    k := k + 1
  if k * k ≤ n then
    return .error s!"the square-free part of {d} cannot be decided here: no \
square factor below {squareFactorCap} remains, and certifying that needs a \
larger search"
  return .ok (sign * Int.ofNat n, s)

/-- The one constructor of `Value.alg`: normalize `a + b√d` (see the
constructor's own docs). A radicand this slice cannot decide the square-free
part of is a loud failure, never an unnormalized value. -/
def mkAlg (a b : Rat) (d : Int) : Except String Value := do
  if b == 0 || d == 0 then return ofRat a
  if d == 1 then return ofRat (a + b)
  let (core, s) ← squareFreePart d
  let b' := b * Rat.ofInt (Int.ofNat s)
  if core == 1 then return ofRat (a + b') else return .alg a b' core

/-- `√q` for a rational `q`, exactly: `√(n/m)` is `√(nm)/m`, with the square
part of `nm` moved out front. A NEGATIVE `q` gives the imaginary root, on the
principal branch the constructor's `√(-1) = i` fixes. -/
def sqrtOfRat (q : Rat) : Except String Value := do
  if q == 0 then return .int 0
  let neg := q.blt 0
  let a := if neg then -q else q
  let (core, s) ← squareFreePart (a.num * Int.ofNat a.den)
  mkAlg 0 (mkRat (Int.ofNat s) a.den) (if neg then -core else core)

/-- Is the REAL surd `a + b√d` (`d > 0`) nonnegative? Exact: with `a` and `b`
of opposite signs the comparison squares to `a² ⋛ b²d`, and the two cannot be
equal (`d` is not a square).

A fact about this normal form, so it lives with the form rather than in one of
its users: the modulus of a real surd needs it (`Native`'s `alg_abs`) and so
does the certificate of an approximation (`absLtRat` below). Deciding a SIGN
is not deciding an ORDER — the surface's exact algebraic values stay unordered
(DESIGN.md §Ceilings), and `Native.scalarCmp` states that refusal itself. -/
def nonNegSurd (a b : Rat) (d : Int) : Bool :=
  let n := a * a - b * b * Rat.ofInt d
  if !a.blt 0 && !b.blt 0 then true
  else if a.blt 0 && b.blt 0 then false
  else if !a.blt 0 then !n.blt 0        -- a ≥ 0 > b: positive iff a² ≥ b²d
  else !Rat.blt 0 n                     -- b > 0 > a: positive iff a² ≤ b²d

/-- Strip trailing zero coefficients (the zero polynomial is `#[]`). -/
def mkPoly (coeff : Domain) (coeffs : Array Value) : Value := Id.run do
  let mut cs := coeffs
  while cs.size > 0 && isZeroCoeff cs[cs.size - 1]! do
    cs := cs.pop
  return .poly coeff cs

/-- How an exponent is spelled: `x^2` in plain text, `x^{2}` in LaTeX (braces
always, so a multi-digit exponent does not fall out of the superscript). -/
private def plainSup (i : Nat) : String := "^" ++ toString i
private def latexSup (i : Nat) : String := "^{" ++ toString i ++ "}"

/-- A rational, in the one spelling both renderers use: an inline solidus, and
an integral rational as the integer (`4`, never `4/1`). -/
private def ratText (q : Rat) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

/-- `n = 10^k`, when it is. -/
private partial def powerOfTen? (n : Nat) : Option Nat :=
  if n == 1 then some 0
  else if n == 0 || n % 10 != 0 then none
  else (powerOfTen? (n / 10)).map (· + 1)

/-- A tolerance, in the spelling SPEC.md writes it in: a reciprocal power of
ten as `1/10^{10}` — which is also valid input again — and any other rational
as itself. ONE spelling for plain text and LaTeX, because it already satisfies
both display conventions (an inline solidus for the rational, a braced
exponent) and because SPEC.md's own displayed line is exactly this.

`backends/sage_adapter.py`'s `tol_text` is the reciprocal of this: the backend
words its own refusals in the same spelling, so a tolerance reads alike whether
this side or that one reports it. -/
def tolText (q : Rat) : String :=
  match (if q.num == 1 && q.den > 1 then powerOfTen? q.den else none) with
  | some k => s!"1/10^\{{k}}"
  | none => ratText q

/-- `a + b√d`, given how the caller spells a square root. The two spellings a
sign gives the radical are the whole difference between the real and the
imaginary case: `√5`, and `i` / `i√3` for a negative radicand. -/
private def algText (sqrt : Nat → String) (a b : Rat) (d : Int) : String :=
  let rad :=
    if d == -1 then "i"
    else if d < 0 then "i" ++ sqrt d.natAbs
    else sqrt d.natAbs
  let term (q : Rat) : String :=
    if q == 1 then rad
    else if q == -1 then "-" ++ rad
    else if q.den == 1 then toString q.num ++ rad
    else s!"({ratText q}){rad}"
  if a == 0 then term b
  else if b.blt 0 then s!"{ratText a} - {term (-b)}"
  else s!"{ratText a} + {term b}"

/-- Term-joining for polynomials, shared by the plain and LaTeX renderers:
the two differ in the exponent spelling and in how a COEFFICIENT is spelled,
so the caller renders the coefficients itself and passes the strings. That is
what makes the LaTeX path propagate a coefficient with no LaTeX form (its
`mapM latex?` fails before this is reached) instead of silently substituting
the plain spelling of a value it cannot typeset. -/
private def renderPolyWith (x : String) (sup : Nat → String)
    (coeffs : Array String) : String := Id.run do
  if coeffs.isEmpty then return "0"
  let mut terms : List String := []
  for i in [0:coeffs.size] do
    let cs := coeffs[i]!
    if cs == "0" then continue
    let term :=
      if i == 0 then cs
      else
        let p := if i == 1 then x else s!"{x}{sup i}"
        let plainInt :=
          cs.all Char.isDigit || (cs.startsWith "-" && (cs.drop 1).all Char.isDigit)
        if cs == "1" then p
        else if cs == "-1" then s!"-{p}"
        -- anything that is not a plain integer is parenthesized: `(1/2)x`
        -- reads as a product rather than as one rational, and `(2 + 2i)x` as
        -- a product rather than as a sum that swallowed the indeterminate
        else if plainInt then s!"{cs}{p}"
        else s!"({cs}){p}"
    terms := term :: terms
  if terms.isEmpty then return "0"
  -- terms is highest-degree first; join with signs
  let mut out := ""
  for t in terms do
    if out.isEmpty then out := t
    else if t.startsWith "-" then out := out ++ " - " ++ (t.drop 1)
    else out := out ++ " + " ++ t
  return out

partial def render : Value → String
  | .int z => toString z
  | .rat q => ratText q
  | .mod _ v => toString v
  | .alg a b d => algText (fun n => "√" ++ toString n) a b d
  -- SPEC.md's own display line, `1.4142135623 + O(1/10^{10})`: the decimal
  -- and the tolerance that was ASKED for (the achieved bound is the backend's
  -- claim, checked at construction, not part of what is shown)
  | .approx _ decimal eps _ => s!"{decimal} + O({tolText eps})"
  | .poly _ coeffs => renderPolyWith "x" plainSup (coeffs.map render)
  | .mat _ _ rows =>
      let r := rows.toList.map fun row =>
        ", ".intercalate (row.toList.map render)
      "[" ++ "; ".intercalate r ++ "]"
  | .vec _ _ comps => "(" ++ ", ".intercalate (comps.toList.map render) ++ ")"
  | .factorization unit factors _ =>
      let fs := factors.toList.map fun (f, m) =>
        let base := match f with
          | .poly _ cs =>
              let p := renderPolyWith "x" plainSup (cs.map render)
              if (cs.filter (· != .int 0)).size > 1 ∨ cs.size > 2 then s!"({p})" else p
          | v => v.render
        if m == 1 then base else s!"{base}^{m}"
      let core := " * ".intercalate fs
      match unit with
      | .int 1 => if fs.isEmpty then "1" else core
      | .rat q =>
          if q == 1 then (if fs.isEmpty then "1" else core)
          else s!"{render (.rat q)} * {core}"
      | u => if fs.isEmpty then u.render else s!"{u.render} * {core}"
  | .idealV gens _ =>
      "(" ++ ", ".intercalate (gens.toList.map render) ++ ")"
  | .setV elems _ =>
      "{" ++ ", ".intercalate (elems.toList.map render) ++ "}"
  -- the AMBIENT is part of the display, in SPEC.md's own subobject notation:
  -- without it the trivial subspace would render as an empty `span_ℚ{}` that
  -- says nothing about which space it is the zero of
  | .spanV n basis =>
      "span_ℚ{" ++ ", ".intercalate (basis.toList.map render) ++ "} ≤ "
        ++ (Domain.vector n .rat).render
  | .progV _ first step last? =>
      let tail := match last? with | some l => s!", ..., {render l}" | none => ", ..."
      s!"\{{render first}, step {render step}{tail}}"
  | .cardinal (.finite n) => toString n
  | .cardinal .countablyInfinite => "ℵ₀"
  | .bool b => toString b
  | .func _ _ binder body =>
      -- the body is written back in the mathematician's own binder, not in
      -- the `x` a bare polynomial renders with
      let t := toString binder
      let b := match body with
        | .poly _ cs => renderPolyWith t plainSup (cs.map render)
        | v => v.render
      s!"{t} ↦ {b}"

instance : ToString Value := ⟨render⟩

/-! ## Subspaces of `ℚⁿ` (`SPEC.md` §Subspaces and spans)

A subspace is presented by a basis, and the basis is kept in REDUCED ROW
ECHELON FORM. That one normalization is what answers all three questions
SPEC.md asks of a span: the dimension is the basis size (the echelon form has
dropped every dependent generator), membership is one reduction of the
candidate against the basis, and equality is the bases compared as data —
because the reduced echelon form of a subspace does not depend on which
generators produced it.

Exact `Rat` arithmetic, and it lives here rather than in a backend for the
reason `mkAlg` does: it is the NORMAL FORM of a presentation, so every way a
span can be built — the surface's `span_QQ{…}`, an executor's `M.ker()`, a
decoded frame — must go through the same one or two spans denoting the same
subspace would compare unequal. -/

/-- Reduced row echelon form of `rows` over ℚ, with zero rows dropped: the
pivot columns are scanned left to right, each pivot is scaled to 1 and cleared
from every other row, and the smallest eligible row is always chosen — so the
result is a FUNCTION of the row space and nothing else. -/
def rref (n : Nat) (rows : Array (Array Rat)) : Array (Array Rat) := Id.run do
  let mut rs := rows
  let mut pivot := 0
  for col in [0:n] do
    match (Array.range rs.size).find? (fun i => pivot ≤ i && rs[i]![col]! != 0) with
    | none => pure ()
    | some i =>
        let (ri, rp) := (rs[i]!, rs[pivot]!)
        rs := (rs.set! pivot ri).set! i rp
        let p := rs[pivot]![col]!
        rs := rs.set! pivot (rs[pivot]!.map (· / p))
        for j in [0:rs.size] do
          if j != pivot && rs[j]![col]! != 0 then
            let f := rs[j]![col]!
            rs := rs.set! j ((Array.range n).map fun k => rs[j]![k]! - f * rs[pivot]![k]!)
        pivot := pivot + 1
  -- every row past the last pivot is zero in every column: a nonzero entry
  -- anywhere would have made its column a pivot column
  return rs.extract 0 pivot

/-- The rational components of a vector of `ℚⁿ`. `none` = it is not one —
the wrong length, not a vector at all, or a component this slice cannot read
as a rational (a surd above all: `√2·u` lies in the ℝ-span, not the ℚ-one, and
guessing either way would be a claim). -/
def ratComps? (n : Nat) : Value → Option (Array Rat)
  | .vec m _ comps =>
      if m != n || comps.size != n then none
      else comps.mapM fun
        | .int z => some (Rat.ofInt z)
        | .rat q => some q
        | _ => none
  | _ => none

/-- THE constructor of a span's basis: the generators, reduced. Every span in
the system is built from this — the surface's `span_QQ{…}`, an executor's
kernel, and a decoded frame — which is what makes equality of two spans the
equality of their bases. -/
def mkSpanBasis (n : Nat) (gens : Array Value) : Except String (Array Value) := do
  let rows ← gens.mapM fun g =>
    match ratComps? n g with
    | some r => .ok r
    | none => .error s!"{g.render} is not a vector of {(Domain.vector n .rat).render}: \
this slice spans subspaces over ℚ, and a generator outside it is a gap rather \
than a guess"
  return (rref n rows).map fun r => .vec n .rat (r.map Value.rat)

/-- The span as a `Value` — what an executor returns for `M.ker()`.
`Denote.ofValue` turns it into the ordinary set OBJECT, exactly as it does a
returned finite set or progression. -/
def mkSpan (n : Nat) (gens : Array Value) : Except String Value := do
  return .spanV n (← mkSpanBasis n gens)

/-- Is `v` the ZERO of a subspace of `ℚⁿ`? The zero vector, and the scalar
`0` — which is the mathematician's own spelling of the zero of the ambient
space, and the one SPEC.md writes in `assert M.ker() = {0}`.

The reading is exactly that narrow: only a ZERO is read across the boundary,
because 0 is the one element every additive group shares. Any other scalar is
not an element of `ℚⁿ` and answers false. -/
def isSpanZero (n : Nat) : Value → Bool
  | .int z => z == 0
  | .rat q => q == 0
  | v => match ratComps? n v with
         | some cs => cs.all (· == 0)
         | none => false

/-- Is `v` an element of the subspace the RREF `basis` presents?

The linear system is SOLVED rather than searched: each basis row has a leading
1 in a pivot column no other row touches, so the only linear combination that
could produce `v` is the one reading its coefficient off that column. Subtract
it, and what is left is zero exactly when `v` was in the span.

Three outcomes, all decided: a vector of the ambient reduces; a vector of a
DIFFERENT length is not an element of the ambient at all and is `false`, as is
anything that is not a vector; and a vector with a component this slice cannot
read as a rational is a loud refusal, because `√2·u` lies in the ℝ-span rather
than the ℚ-one and answering either way would be a claim. -/
def spanContains (n : Nat) (basis : Array Value) (v : Value)
    : Except String Bool := do
  if isSpanZero n v then return true
  match v with
  | .vec m _ _ =>
      if m != n then return false
      let some cs := ratComps? n v
        | .error s!"{v.render} has a component this slice cannot read as a \
rational, so its membership in a ℚ-subspace is a gap rather than a guess"
      let rows ← basis.mapM fun r =>
        match ratComps? n r with
        | some row => .ok row
        | none => .error s!"the basis vector {r.render} is not over ℚ: this span \
was not built through `Value.mkSpanBasis`"
      let mut w := cs
      for row in rows do
        if let some p := (Array.range n).find? (fun k => row[k]! != 0) then
          let f := w[p]!
          if f != 0 then
            w := (Array.range n).map fun k => w[k]! - f * row[k]!
      return w.all (· == 0)
  | _ => return false


/-- The element a progression shows after its first (`{0, 2, …}` needs the
`2`), or `ell` when the step is not one the presentation can take. -/
private def progSecond (ell : String) : Value → Value → String
  | .int a, .int d => toString (a + d)
  | _, _ => ell

/-- The LaTeX form of a value, or `none` when it has no natural one — in
which case the cell emits `text/plain` alone (DESIGN.md §LaTeX-first
display). A missing form is the documented fallback, never a failure.

Conventions: braced exponents, `\cdot` between factors, an inline solidus
for rationals (`3/2`, parenthesized as a polynomial coefficient exactly as
in plain text), `\mathbb` for the number systems, `\aleph_0`, `\{ \}` for
set braces. Every string is math-mode LaTeX: no raw Unicode (`ℤ`, `↦`)
survives here, because MathJax does not typeset it. -/
partial def latex? : Value → Option String
  | .int z => some (toString z)
  | .rat q => some (ratText q)
  | .mod _ v => some (toString v)
  -- `\sqrt{2}` and `i` are math mode's own spellings, so an exact algebraic
  -- value always has a form — the `√` and the raw `i` of the plain rendering
  -- are what MathJax would not typeset
  | .alg a b d => some (algText (fun n => "\\sqrt{" ++ toString n ++ "}") a b d)
  -- the SAME string as the plain rendering, deliberately: digits, `O(…)` and
  -- `1/10^{10}` are already math mode's own spellings, and they are the two
  -- conventions the table fixes (inline solidus, braced exponent). Inventing
  -- a second spelling here would make the LaTeX say something the plain text
  -- does not
  | .approx _ decimal eps _ => some s!"{decimal} + O({tolText eps})"
  | .poly _ coeffs => (coeffs.mapM latex?).map (renderPolyWith "x" latexSup)
  | .mat _ _ rows => do
      let rs ← rows.mapM fun row => do
        let cs ← row.mapM latex?
        return " & ".intercalate cs.toList
      return "\\begin{pmatrix} " ++ " \\\\ ".intercalate rs.toList ++ " \\end{pmatrix}"
  -- the TUPLE spelling, which is SPEC.md's own (`(1, 2)`) and the one this
  -- surface reads back. Parentheses and commas are math mode's own spellings,
  -- so a column `pmatrix` here would typeset something the plain rendering —
  -- and the input syntax — does not say
  | .vec _ _ comps => do
      let cs ← comps.mapM latex?
      return "(" ++ ", ".intercalate cs.toList ++ ")"
  | .factorization unit factors _ => do
      let fs ← factors.mapM fun (f, m) => do
        let base ← match f with
          | .poly _ cs =>
              (cs.mapM latex?).map fun ls =>
                let p := renderPolyWith "x" latexSup ls
                if (cs.filter (· != .int 0)).size > 1 ∨ cs.size > 2 then s!"({p})" else p
          | v => latex? v
        return if m == 1 then base else base ++ latexSup m
      let core := " \\cdot ".intercalate fs.toList
      match unit with
      | .int 1 => return if fs.isEmpty then "1" else core
      -- the unit is a scalar like any other: it goes through this renderer, so
      -- an integral rational is an integer (`2`, never `2/1`)
      | .rat q =>
          if q == 1 then return (if fs.isEmpty then "1" else core)
          else return (← latex? (.rat q)) ++ " \\cdot " ++ core
      | u => do
          let us ← latex? u
          return if fs.isEmpty then us else s!"{us} \\cdot {core}"
  | .idealV gens _ => do
      let gs ← gens.mapM latex?
      return "(" ++ ", ".intercalate gs.toList ++ ")"
  -- `setV`/`progV` are what an executor returns; `Denote.ofValue` turns both
  -- into set OBJECTS before display, so these agree with `SetPresentation`
  | .setV elems _ => do
      let es ← elems.mapM latex?
      return "\\{" ++ ", ".intercalate es.toList ++ "\\}"
  | .spanV n basis => do
      let bs ← basis.mapM latex?
      return "\\mathrm{span}_{\\mathbb{Q}}\\{" ++ ", ".intercalate bs.toList
        ++ "\\} \\leq " ++ (Domain.vector n .rat).latex
  | .progV _ first step last? => do
      let f ← first.latex?
      -- `some …`, not `return …`: a `return` inside a match arm returns from
      -- the ENCLOSING `do`, so it would ship the tail as the whole payload
      let tail ← match last? with
        | some l => do let ls ← l.latex?; some (", \\ldots, " ++ ls)
        | none => some ", \\ldots"
      return "\\{" ++ f ++ ", " ++ progSecond "\\ldots" first step ++ tail ++ "\\}"
  | .cardinal (.finite n) => some (toString n)
  | .cardinal .countablyInfinite => some "\\aleph_0"
  -- a truth value is the documented no-natural-form case: `\text{true}` is
  -- typesetting prose, not mathematics
  | .bool _ => none
  | .func _ _ binder body => do
      let t := toString binder
      let b ← match body with
        | .poly _ cs => (cs.mapM latex?).map (renderPolyWith t latexSup)
        | v => latex? v
      -- the binder is the mathematician's own name, and a `θ` reaches math
      -- mode as raw Unicode, which MathJax does not typeset and pdflatex
      -- rejects outright: no LaTeX form, so the cell falls back to plain text
      if t.all Char.isAlphanum then return t ++ " \\mapsto " ++ b else none

/-! ## The approximation certificate (`SPEC.md` §Exact number systems, #7)

A decimal presentation is a CLAIM about the exact value it presents, and the
digits shown are the whole of it. Everything needed to check that claim is
exact rational arithmetic over the normal form this file already owns, so the
check lives with the constructor: nothing builds a `Value.approx` without it,
which is what makes a backend that returns a wrong digit fail loudly at the
boundary instead of publishing a decimal that presents nothing. -/

/-- The exact rational a DECIMAL string denotes — an optional `-`, digits, and
at most one point. `none` = it is not a decimal at all, which from a backend
is a protocol failure rather than a string to read leniently.

STRICT, because this parses a certificate: a trailing point (`3.`) and a
padded integer part (`007`) are not spellings this accepts merely because
their value is guessable. -/
def decimalToRat? (s : String) : Option Rat := do
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let (ip, fp) ← match body.splitOn "." with
    | [i] => some (i, "")
    | [i, f] => if f.isEmpty then none else some (i, f)
    | _ => none
  guard (!ip.isEmpty && ip.all Char.isDigit && fp.all Char.isDigit
    && (ip == "0" || !ip.startsWith "0"))
  let n ← (ip ++ fp).toNat?
  let q := mkRat (Int.ofNat n) (10 ^ fp.length)
  return if neg then -q else q

/-- The exact REAL values this slice presents, as `(a, b, d)` with
`v = a + b√d` and `d > 0`. `none` = not one of them — a complex surd above all,
where a real decimal presents nothing and the honest answer is a refusal. -/
def realParts? : Value → Option (Rat × Rat × Int)
  | .int z => some (Rat.ofInt z, 0, 1)
  | .rat q => some (q, 0, 1)
  | .alg a b d => if d > 0 then some (a, b, d) else none
  | _ => none

/-- `|a + b√d| < q` for a real surd and a rational bound, decided EXACTLY by
the same squaring comparison a sign is decided by — never by comparing two
decimals, and never by a float.

`|A + B√d| < q` is `A + B√d < q` and `−q < A + B√d`, i.e. `(q − A) − B√d > 0`
and `(q + A) + B√d > 0`. A genuine surd is irrational, so neither can be zero
and the strictness `nonNegSurd` does not state comes for free; a rational
(`b = 0`) compares strictly on its own. -/
def absLtRat (a b : Rat) (d : Int) (q : Rat) : Bool :=
  if b == 0 then (if a.blt 0 then (-a).blt q else a.blt q)
  else nonNegSurd (q - a) (-b) d && nonNegSurd (q + a) b d

/-- THE constructor of `Value.approx`, and a CHECK rather than a wrapper: the
decimal must lie within the certified bound of the exact value, and that bound
must be positive and meet the tolerance that was requested.

Both boundaries a value can enter through go via this — the wire codec and the
executor's reply — so a backend that returns a wrong digit, or a bound it did
not achieve, fails here. Where the exact value is one this slice presents (a
rational, or `a + b√d` with `d > 0` — today that is ALL of them) the check is
this exact comparison; a value only a backend could evaluate would have no
`realParts?` and is refused rather than trusted silently. -/
def mkApprox (exact : Value) (decimal : String) (eps achieved : Rat)
    : Except String Value := do
  unless Rat.blt 0 achieved && !Rat.blt eps achieved do
    .error s!"a certified bound of O({tolText achieved}) does not meet the \
requested O({tolText eps}): the bound must be positive and at most what was asked"
  let some (a, b, d) := realParts? exact
    | .error s!"{exact.render} is not one of the exact REAL values this slice \
presents (a rational, or a + b√d with d > 0), so no decimal certificate covers it"
  let some r := decimalToRat? decimal
    | .error s!"{repr decimal} is not a decimal presentation"
  unless absLtRat (a - r) b d achieved do
    .error s!"the decimal {decimal} is not within O({tolText achieved}) of \
{exact.render}: the certificate does not hold, and the digits shown ARE the claim"
  return .approx exact decimal eps achieved

end Value

namespace SetPresentation

partial def render : SetPresentation → String
  | .finite _ elems =>
      "{" ++ ", ".intercalate (elems.toList.map (·.render)) ++ "}"
  | .arithProg _ first step none =>
      s!"\{{first.render}, {Value.progSecond "…" first step}, ...}"
  | .arithProg _ first step (some last) =>
      s!"\{{first.render}, {Value.progSecond "…" first step}, ..., {last.render}}"
  | .span n basis =>
      "span_ℚ{" ++ ", ".intercalate (basis.toList.map (·.render)) ++ "} ≤ "
        ++ (Domain.vector n .rat).render
  | .domainSet d => d.render
  | .product a b => s!"{render a} × {render b}"
  | .powerset s => s!"𝒫({render s})"
  | .domainDiff a b => s!"{a.render} - {b.render}"

instance : ToString SetPresentation := ⟨render⟩

/-- The LaTeX form of a set presentation. `none` propagates from an element
that has none. -/
partial def latex? : SetPresentation → Option String
  | .finite _ elems => do
      let es ← elems.mapM Value.latex?
      return "\\{" ++ ", ".intercalate es.toList ++ "\\}"
  | .arithProg _ first step last? => do
      let f ← first.latex?
      -- `some …`, not `return …`: a `return` inside a match arm returns from
      -- the ENCLOSING `do`, so it would ship the tail as the whole payload
      let tail ← match last? with
        | some l => do let ls ← l.latex?; some (", \\ldots, " ++ ls)
        | none => some ", \\ldots"
      return "\\{" ++ f ++ ", " ++ Value.progSecond "\\ldots" first step ++ tail ++ "\\}"
  | .span n basis => do
      let bs ← basis.mapM Value.latex?
      return "\\mathrm{span}_{\\mathbb{Q}}\\{" ++ ", ".intercalate bs.toList
        ++ "\\} \\leq " ++ (Domain.vector n .rat).latex
  | .domainSet d => some d.latex
  | .product a b => do return (← latex? a) ++ " \\times " ++ (← latex? b)
  | .powerset s => do return "\\mathcal{P}(" ++ (← latex? s) ++ ")"
  -- `\setminus` is what the minus between two SETS means in math mode
  | .domainDiff a b => some (a.latex ++ " \\setminus " ++ b.latex)

end SetPresentation

namespace Obj

def render : Obj → String
  | .elem _ v => v.render
  | .domainObj d => d.render
  | .setObj s => s.render
  | .cyclicModule n => s!"ℤ/{n} as ℤ-module"

/-- The LaTeX form of an object. The module fixture has none ON PURPOSE:
`\mathbb{Z}/4\mathbb{Z}` typeset alone is the ring, and equality here is
category-bound (DESIGN.md §Surface), so displaying the module as its
underlying object would be a display-level lie. -/
def latex? : Obj → Option String
  | .elem _ v => v.latex?
  | .domainObj d => some d.latex
  | .setObj s => s.latex?
  | .cyclicModule _ => none

/-- The presentation string used in capability gaps and diagnostics. -/
def presentation : Obj → String
  | .elem d v => s!"{v.render} ∈ {d.render}"
  | .domainObj d => d.render
  | .setObj s => s.render
  | .cyclicModule n => s!"ℤ/{n} as ℤ-module"

instance : ToString Obj := ⟨render⟩

end Obj

end CasDsl
