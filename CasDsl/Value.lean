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

  `Value.mkAlg` is the only way to build one: it moves the square part of `d`
  into `b` and returns the RATIONAL when `b` comes out zero, so `√8` IS `2√2`
  and a surd is never a rational in disguise. Everything stays exact —
  nothing here is ever a float.

  CEILING: ONE square root over ℚ. `√2 + √5` leaves this presentation and is
  a loud refusal, never an approximation and never a dropped term. -/
  | alg (a b : Rat) (d : Int)
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
  | .funcs s t => s!"{s.render} → {t.render}"
where
  subscript (n : Nat) : String :=
    let digits := "₀₁₂₃₄₅₆₇₈₉"
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
  | .poly _ coeffs => renderPolyWith "x" plainSup (coeffs.map render)
  | .mat _ _ rows =>
      let r := rows.toList.map fun row =>
        ", ".intercalate (row.toList.map render)
      "[" ++ "; ".intercalate r ++ "]"
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
  | .poly _ coeffs => (coeffs.mapM latex?).map (renderPolyWith "x" latexSup)
  | .mat _ _ rows => do
      let rs ← rows.mapM fun row => do
        let cs ← row.mapM latex?
        return " & ".intercalate cs.toList
      return "\\begin{pmatrix} " ++ " \\\\ ".intercalate rs.toList ++ " \\end{pmatrix}"
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

end Value

namespace SetPresentation

partial def render : SetPresentation → String
  | .finite _ elems =>
      "{" ++ ", ".intercalate (elems.toList.map (·.render)) ++ "}"
  | .arithProg _ first step none =>
      s!"\{{first.render}, {Value.progSecond "…" first step}, ...}"
  | .arithProg _ first step (some last) =>
      s!"\{{first.render}, {Value.progSecond "…" first step}, ..., {last.render}}"
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
