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
  /-- Formal power series `coeff[[t]]` — SPEC.md's `ℝ[[t]]` and `ℤ[[t]]`.
  Its indeterminate is spelled `t`, exactly as the polynomial ring's is
  spelled `x`: a `Domain` records no name, and one spelling per ring is the
  convention this surface already keeps. -/
  | series (coeff : Domain)
  deriving BEq, Repr, Hashable, Inhabited

/-- Cardinality values the slice can express. -/
inductive Cardinality where
  | finite (n : Nat)
  | countablyInfinite
  deriving BEq, Repr, Hashable, Inhabited

/-- A symbolic function EXPRESSION — the presentation `SPEC.md` §Elementary
calculus forces, and nothing wider.

The polynomial engine grounds every function this slice DECIDES things about
(`h(-t) = h(t)`, `(f ∘ g)(t) = t⁶` are settled by substitution). `sin(t)`,
`e^t` and `1/t` leave it, and until the calculus sections landed they were
refused at the binding. They are now presented — SYMBOLICALLY, which is
exactly as much as the operations `SPEC.md` asks of them need: a limit, a
definite integral and a Taylor expansion are computed by the backend from the
EXPRESSION, and nothing here evaluates one at a point or decides an identity
between two of them.

CEILING, and it is the whole vocabulary: the variable, exact rationals, the
named constants `e`, `π` and `∞`, the named function `sin`, and the five
arithmetic operations. A name outside it is a loud refusal LISTING the
vocabulary — never a symbol passed through to a backend to interpret, which
is how a CAS surface stops being backend-blind. -/
inductive SymExpr where
  | var (n : Lean.Name)
  | num (q : Rat)
  /-- `e`, `pi`, `infinity` — the points and bases `SPEC.md` writes. -/
  | const (n : Lean.Name)
  /-- A named unary function: `sin`. -/
  | app (f : Lean.Name) (a : SymExpr)
  | neg (a : SymExpr)
  | add (a b : SymExpr)
  | sub (a b : SymExpr)
  | mul (a b : SymExpr)
  | div (a b : SymExpr)
  | pow (a b : SymExpr)
  deriving BEq, Repr, Inhabited

/-- How a formal power series' coefficients are KNOWN.

The two shapes are genuinely different claims, and the DISPLAY says which: a
RULE knows every coefficient (so a bare series shows a few and `…`), while
TERMS knows exactly the ones it carries (so it shows them and `O(tⁿ)`). A
truncation is then a real operation on the presentation — it turns a rule
into terms — rather than a second value shape meaning the same thing.

CEILING: the coefficients are exact RATIONALS. Every series `SPEC.md` writes
has rational coefficients (`n²`, and the `1/n!` of a Taylor expansion), and
holding `Value`s here would make this type mutually recursive with `Value`
for no gain the surface asks for. -/
inductive SeriesGen where
  /-- `[tⁿ] = p(n)` for EVERY n, with `p` given by its coefficients ascending
  in `n`: SPEC.md's `∑_{n ∈ ℕ} n² tⁿ` has the rule `#[0, 0, 1]`. Any
  coefficient and any truncation is available. -/
  | rule (inN : Array Rat)
  /-- The coefficients of `t⁰ … t^(size-1)`, known exactly and no further —
  what a Taylor expansion comes back as. A truncation past the last one is a
  loud refusal naming the ceiling, never a shorter answer. -/
  | terms (coeffs : Array Rat)
  deriving BEq, Repr, Inhabited

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
  /-- A finite MULTISET of elements of one domain, as an executor RESULT —
  what `roots` answers (its anchor `Polynomial.roots` is `Multiset`-valued:
  `(x−1)²` has the root 1 twice). Multiplicity is carried by REPETITION — a
  representative list, exactly as Mathlib's `Multiset` is a list up to
  permutation. `Denote.ofValue` turns it into `SetPresentation.multiset`;
  it is a `Value` only because that is what crosses the backend wire.
  CEILING: an explicit finite multiset, nothing wider. -/
  | msetV (elems : Array Value) (dom : Domain)
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
  /-- A symbolic expression — the body of a function the polynomial engine
  cannot express (`t ↦ sin(t)`, `t ↦ e^t`, `t ↦ 1/t`), and the points
  `SPEC.md` writes its limits and integrals between (`π`, `∞`).

  It has NO domain (`valueDom?` gives it none), which is the honest slot: an
  expression is not an element of ℝ, and this slice neither evaluates one at
  a point nor decides an identity between two of them. Arithmetic on it is
  refused for the reason an approximation's is — there is nothing here that
  would not be invented. -/
  | sym (e : SymExpr)
  /-- SPEC.md §Differentials' `(6x + 1) dx` — a DIFFERENTIAL 1-FORM, the
  value `d(f)` takes.

  `Ω¹_{k[x]/k} ≅ k[x] dx` is free of rank one, so a 1-form IS a polynomial
  times `dx` — and it is not a polynomial. Keeping them apart is the whole
  return on this constructor: `d(f) = (6x + 1) dx` is true and
  `d(f) = 6x + 1` is FALSE rather than incomparable, exactly as a matrix is
  not the vector it acts on.
  CEILING: Ω¹ is not a `Domain` here (a 1-form joins the domainless RESULT
  family — a factorization, a cardinal, an approximation), so `d(f) ∈ Ω¹`
  is not a claim this surface can state at all. What SPEC.md asks of Ω¹ is
  its DISPLAY and the equality above; a module structure on it belongs to
  CategoryGraph per the trajectory ruling. -/
  | diff1 (coeff : Domain) (p : Value)
  /-- SPEC.md §Differentials' `d` and `(d/dx)` — the universal differential
  and the derivation, which are ONE operation with two result shapes: `d(f)`
  is the 1-form `f' dx` and `(d/dx)(f)` is the polynomial `f'`. The flag is
  which, and both are applied by elaboration like calling a polynomial.

  It is a VALUE rather than a production so that a bare `d` cell can display
  what the universal differential IS, which is what SPEC.md's own cell does. -/
  | derivation (asForm : Bool)
  /-- SPEC.md §Indefinite integration's `x³ + (1/2)x² + x + ℚ` — the value
  `∫ f dx` takes, as an executor RESULT. `Denote.ofValue` turns it into the
  ordinary set OBJECT, exactly as it does a returned finite set, progression
  or span: the indefinite integral is a COSET of `ker(d/dx)`, which is a set
  of primitives and not a primitive. -/
  | cosetV (offset : Value) (kernel : Domain)
  /-- A formal power series in `t` — SPEC.md's `∑_{n ∈ ℕ} n² tⁿ ∈ ℤ[[t]]` and
  the Taylor expansions of §Elementary calculus. -/
  | seriesV (coeff : Domain) (gen : SeriesGen)
  /-- `binder ↦ body` in `src → tgt`. The body is the exact polynomial the
  binder generates, so the identities SPEC.md asserts about functions
  (`h(-t) = h(t)`, `(f ∘ g)(t) = t⁶`) are decided by the polynomial engine
  rather than sampled. The binder is a BOUND NAME, not data: equality
  compares domains and bodies (`Native.valueEq`). -/
  | func (src tgt : Domain) (binder : Lean.Name) (body : Value)
  /-- A first-class HOM between free ℚ-modules — SPEC.md §Subspaces' `φ: ℚ³ →
  ℚ := (a, b, c) ↦ a + b - c`, under the owner ruling of 2026-07-31
  (DESIGN.md §Homs are first-class): the value is the domain, the codomain,
  and the map as the mathematician WROTE it — images of a general element,
  equivalently of the generators. A linear map is NOT a matrix: `rows` is the
  DERIVED matrix in the standard frame the `ℚⁿ` spelling itself provides
  (one row per codomain coordinate) — backend data behind `ker`/`im`, calls
  and composition, never the entity. The binders are BOUND names like
  `.func`'s: presentation, not data — equality ignores them.

  CEILING: linear over ℚ, the span machinery's own base. Polynomial maps in
  several variables are tier 2 (#31), and the finitely-presented-over-a-PID
  general case is CategoryGraph-era — nothing here identifies a hom with its
  matrix, which is what keeps that future open. -/
  | hom (src tgt : Domain) (binders : Array Lean.Name) (rows : Array (Array Rat))
  deriving BEq, Repr, Inhabited

/-! ## The surface AST

Produced by `CasDsl/Syntax.lean`; first-order, with no elaboration state.
Everything the parser cannot decide on its own — whether `D[x]` is a
polynomial ring or an index, whether an ascription names a domain or a
category — is decided in `Eval`, against the registries. It lives HERE,
below `Value`, because a presentation may carry an expression: a predicate
set (`SetPresentation.predicate`) is backed by the guard the mathematician
wrote. -/

inductive BinOp where
  | add | sub | mul | div | pow
  deriving BEq, Repr, Inhabited

/-- The order comparisons a set-comprehension guard is written with
(`n² ≤ 20`, `0 ≤ n < 6`). Equality is deliberately absent: `=` is the
assertion relation, category-bound, and reading it as a term-level
comparison here would give the surface two meanings for one symbol. -/
inductive CmpOp where
  | le | lt | ge | gt
  deriving BEq, Repr, Inhabited

inductive CasExpr where
  | num (z : Int)
  /-- A literal that is not a numeral: `ℵ₀`, `true`, `false`. -/
  | lit (v : Value)
  /-- A binding name, or the bound polynomial indeterminate. -/
  | ref (n : Lean.Name)
  /-- An atomic domain term (`ℕ`, `ℤ`, `ℚ`). -/
  | dom (d : Domain)
  /-- `Matₙ(E)`. -/
  | matDom (size : Nat) (entry : CasExpr)
  | neg (e : CasExpr)
  | bin (op : BinOp) (a b : CasExpr)
  /-- `f(args…)` — polynomial/function call. -/
  | app (f : CasExpr) (args : Array CasExpr)
  /-- `e.m(args…)`. -/
  | method (recv : CasExpr) (m : Lean.Name) (args : Array CasExpr)
  /-- `e[a]` — a polynomial ring or an index; decided in `eval`. -/
  | index (recv : CasExpr) (arg : CasExpr)
  | finSet (elems : Array CasExpr)
  /-- `{a, b, …, ...}` / `{a, b, …, ..., z}`: the leading elements and the
  optional inclusive bound. -/
  | progSet (leading : Array CasExpr) (last? : Option CasExpr)
  /-- Row-major; `rows * cols = entries.size`. -/
  | matLit (rows cols : Nat) (entries : Array CasExpr)
  /-- `(1, 2)` — a vector of `Eⁿ`, where `E` is the join of its components'
  domains and `n` their count (SPEC.md §Vectors and matrices). -/
  | vecLit (comps : Array CasExpr)
  /-- `span_QQ{u₁, u₂}` — the subspace of `ℚⁿ` the generators span. DENOTED
  like a set literal (no method, no route): what the span IS follows from the
  generators, and the reduction that normalizes them is a presentation's
  normal form rather than a computation a backend owns. -/
  | spanOf (gens : Array CasExpr)
  | mapTo (e target : CasExpr)
  /-- `ℝ/O(ε)` — the target of SPEC.md's `map √2 to ℝ/O(1/10^{10})`, and
  meaningful ONLY there. It is not a domain, not a set and not a quotient
  (`|a − b| < ε` is not transitive, so there are no classes): it is the
  REQUEST that a decimal presentation meet a tolerance. Written anywhere else
  it is a loud refusal, which is what keeps `ℝ ⊆ ℝ/O(ε)` from being a claim
  this surface can even state. -/
  | approxTarget (eps : CasExpr)
  /-- `binder ↦ body` — a function definition, meaningful only where an
  ascription says which domains it runs between (`evalBinderBinding`). -/
  | lam (binder : Lean.Name) (body : CasExpr)
  /-- `(a, b, c) ↦ body` — a MULTI-binder definition: a HOM of free
  ℚ-modules when the body is linear in the binders (`evalHomBinding`,
  DESIGN.md §Homs are first-class); a body that is not stays the disclosed
  tier-2 gap. -/
  | lamN (binders : Array Lean.Name) (body : CasExpr)
  /-- `S → T` / `S -> T` — a function domain. -/
  | arrow (src tgt : CasExpr)
  /-- `f ∘ g`. -/
  | comp (f g : CasExpr)
  /-- `√e` — the exact square root of a rational (SPEC.md's `√2`, `2√2`). -/
  | sqrt (e : CasExpr)
  /-- `|e|` — SPEC.md's bars, ONE spelling of "the size of e" whose METHOD
  depends on the receiver: `cardinality` for a set, `abs` for an element of
  ℝ or ℂ. Both are ordinary category methods; the bars invent nothing, so
  `|3|` is still the honest "not a method of any category this object
  belongs to". -/
  | magnitude (e : CasExpr)
  /-- `p dx` — a differential 1-form, DENOTED like a set literal: what the
  form IS follows from its coefficient, and `dx` is the free generator of
  `Ω¹_{k[x]/k}` rather than a value to multiply by. -/
  | diffForm (p : CasExpr)
  /-- `Spec R` — the affine scheme of a ring, an ascription TAG. -/
  | specOf (ring : CasExpr)
  /-- `∫ f dx` — the complete set of primitives of `f`, a COSET of
  `ker(d/dx)`. The `antiderivative` method, applied by elaboration. -/
  | integral (f : CasExpr)
  /-- `lim_{t → a} body` — the `limit` METHOD on the function `t ↦ body`,
  which this node builds by elaboration. -/
  | limitOf (binder : Lean.Name) (point body : CasExpr)
  /-- `∫₀¹ t² dt` — the `definite_integral` METHOD on `t ↦ body`, likewise. -/
  | defIntegral (binder : Lean.Name) (lo hi body : CasExpr)
  /-- `ℝ[[t]]` — the formal power series over a coefficient domain. -/
  | seriesDom (coeff : CasExpr)
  /-- `ℝ[[t]]/(t^6)` and `ℤ[[t]] / O(t^5)` — a TRUNCATION REQUEST, on the
  `ℝ/O(ε)` precedent: meaningful only after `map … to`, and a loud refusal
  anywhere else. It is not a quotient domain, and there is no `Domain`
  constructor for it, so it answers no membership or cardinality question. -/
  | truncTarget (order : Nat)
  /-- `∑_{n ∈ ℕ} n² tⁿ` — a series given by its GENERATING RULE. -/
  | seriesSum (binder : Lean.Name) (index rule : CasExpr)
  /-- `[t²]f` — one coefficient of a series. -/
  | coeffOf (power : Nat) (series : CasExpr)
  /-- `kernel(d/dx : ℚ[x] → ℚ[x])` — the kernel of a DERIVATION, which is the
  constants of its ring. The arrow is ascribed rather than inferred because a
  derivation names no domains of its own. -/
  | kernelOf (op arrow : CasExpr)
  /-- `A × B` and `𝒫(A)` / `2^A`. Both DENOTE a set rather than compute one
  (their elements are pairs and sets, which no `Value` presents), so they
  build a presentation exactly as a set literal does — no method, no route. -/
  | setProduct (a b : CasExpr)
  | powersetOf (a : CasExpr)
  /-- `a ≤ b` and the chain `a ≤ b < c`, which is its conjunction. -/
  | cmp (op : CmpOp) (a b : CasExpr)
  | conj (a b : CasExpr)
  /-- `∑_{x ∈ X} body` and `∏_{x ∈ X} body` — the aggregation named by `m`
  (`sum` or `prod`), over the set `index`. The body is evaluated at each
  element exactly as a comprehension's head is, and the aggregation itself is
  an ordinary category method on the resulting set. -/
  | aggregate (m : Lean.Name) (binder : Lean.Name) (index body : CasExpr)
  /-- `{x ∈ D | p(x) = q(x)}` — the set of solutions in `D`, which is the
  `roots` method applied to `p − q` in `D[x]`. A production of its own
  because `=` is the assertion relation everywhere else in this surface. -/
  | rootSet (binder : Lean.Name) (index lhs rhs : CasExpr)
  /-- A comprehension `{head | binder ∈ index, guard}`. SPEC.md's filtering
  spelling `{n ∈ ℤ | P}` is this node with `head = binder` — one shape, so
  one evaluator decides both. -/
  | comprehension (head : CasExpr) (binder : Lean.Name) (index : CasExpr)
      (guard? : Option CasExpr)
  deriving BEq, Repr, Inhabited

/-- Presentation of a set object. Semantic sets are not replaced by ordered
lists merely because indexing exists; the presentation records the
registered enumeration choice implicitly (first/step order for
progressions, literal order for finite sets, a registered convention for
`domainSet`). -/
inductive SetPresentation where
  | finite (dom : Domain) (elems : Array Value)
  /-- A finite MULTISET, elements carried with repetition (`p.roots()`, whose
  anchor `Polynomial.roots` is `Multiset`-valued). Not a second spelling of
  `finite`: the display repeats, `|·|` counts with multiplicity and equality
  compares counts, while `∈` and `⊆` read the SUPPORT — Mathlib's own split
  (`Multiset.card`/`=` against `∈`/`Multiset.Subset`). A finite SET compared
  against one is lifted along `Finset.val`, every multiplicity 1. -/
  | multiset (dom : Domain) (elems : Array Value)
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
  /-- `p + K` — SPEC.md §Indefinite integration's `x³ + (1/2)x² + x + ℚ`, the
  complete set of primitives of `f`.

  A COSET of the kernel of differentiation, and a presentation of its own for
  the reason `span` is one: its elements are polynomials, which `Value.poly`
  presents, but the SET of them is infinite and has a normal form of its own.
  `Value.mkCoset` is the ONE constructor and it CANONICALIZES — the kernel
  here is the constants, so the representative with constant term zero is a
  function of the coset and of nothing else, which is what makes two cosets
  compare as data. `span` is deliberately NOT widened to cover this: that
  presentation is hard-wired to ℚⁿ and its normal form is a reduced basis. -/
  | coset (offset : Value) (kernel : Domain)
  /-- `ℂ - ℚ` (SPEC.md §Polynomials). A presentation again, and the minimal
  one the assertion needs: MEMBERSHIP is decided pointwise (`x ∈ a` and
  `x ∉ b`), which is what `q.roots() ⊆ ℂ - ℚ` asks, and everything that would
  need an element list — a cardinality, a canonical form to compare — refuses.
  DOMAINS on both sides deliberately: the difference of two finite sets is
  `A \ B`, which COMPUTES (§Sets), and this constructor is not a second
  spelling of it. -/
  | domainDiff (a b : Domain)
  /-- `{n ∈ ℕ | n.is_prime()}` (#31 item 7) — a LAZY set backed by the guard
  the mathematician wrote: membership is decided by EVALUATING the guard at
  the candidate, enumeration is trial over the ambient's countable indexing,
  and cardinality honestly refuses — a guard says nothing about size. The
  guard is the surface expression AS WRITTEN; names inside it read the
  session's bindings at query time, which is the spike's documented ceiling
  (SPEC.md never rebinds a name a stored guard mentions). -/
  | predicate (dom : Domain) (binder : Lean.Name) (guard : CasExpr)
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
  /-- SPEC.md §Differentials' `Spec ℚ[x]` — the affine scheme of a ring.

  An ASCRIPTION TAG at this stage, the standing `QQ-Mod` has: the membership
  `in Schemes/ℚ` it states is real and checked, and the object carries the
  RING it is the spectrum of, which is what makes the differential's display
  concrete. What it does NOT carry is a scheme's structure — its topology,
  its sheaf, its morphisms — because that ontology is CategoryGraph's per
  the trajectory ruling, and nothing here may grow into it. -/
  | specOf (ring : Domain)
  /-- A SYMBOLIC expression as an object — `π`, `∞`, and the points a limit
  or a definite integral runs between.

  It exists because a method ARGUMENT is an `Obj`, and `SPEC.md` writes
  `lim_{t → ∞}` and `∫₀^π`: neither point is an element of a domain, so
  neither has an `Obj.elem` to be. Giving one a domain would be a display
  that lies (`∞ ∈ ℝ` is false), and this is the honest slot instead. It has
  NO profile — no method reaches it — which is exactly right: an expression
  is something operations are performed WITH, not ON. -/
  | symObj (e : SymExpr)
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
  | .series c => s!"{c.render}[[t]]"
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
  | .series c => c.latex ++ "[[t]]"
  | .matrix n e => "\\mathrm{Mat}_{" ++ toString n ++ "}(" ++ e.latex ++ ")"
  | .vector n e => e.latex ++ "^{" ++ toString n ++ "}"
  | .funcs s t => s.latex ++ " \\to " ++ t.latex

instance : ToString Domain := ⟨render⟩

end Domain

/-! ## Shared spellings

These three are the file's, not one namespace's: `SymExpr` and `Value` both
render rationals and exponents, and DESIGN.md §LaTeX-first display fixes ONE
spelling for each. Two copies would be two places for that table to drift. -/

/-- How an exponent is spelled: `x^2` in plain text, `x^{2}` in LaTeX (braces
always, so a multi-digit exponent does not fall out of the superscript). -/
private def plainSup (i : Nat) : String := "^" ++ toString i
private def latexSup (i : Nat) : String := "^{" ++ toString i ++ "}"

/-- A rational, in the one spelling both renderers use: an inline solidus, and
an integral rational as the integer (`4`, never `4/1`). -/
private def ratText (q : Rat) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

/-- The COEFFICIENT of a differential 1-form, parenthesized exactly as a
polynomial FACTOR is: a plain integer stands alone, anything else gets
brackets so it reads as one factor rather than as a sum that swallowed the
`dx`. Shared by the plain and LaTeX renderers for the reason
`renderPolyWith` is shared — they had drifted, and `2x` came out `2x dx` in
one and `(2x)\,dx` in the other. -/
private def diffCoeffText (s : String) : String :=
  if s.all Char.isDigit || (s.startsWith "-" && (s.drop 1).all Char.isDigit) then s
  else "(" ++ s ++ ")"

namespace SymExpr

/-- The named functions and constants this slice presents — the whole
vocabulary, and the reason a symbolic body is still backend-blind: a name
outside this list never reaches a backend to be interpreted there. -/
def functions : List Lean.Name := [`sin, `exp]
def constants : List Lean.Name := [`e, `pi, `infinity]

/-- Binding strength, on the surface grammar's own ladder (`+ -` at 65,
`* /` at 70, unary minus at 75, `^` at 80, atoms at the top). A child weaker
than the slot it sits in is parenthesized — ONE rule, so the plain and LaTeX
renderings cannot disagree about where a paren goes. A NEGATIVE rational
carries the unary minus's strength, since that is what it spells. -/
private def prec : SymExpr → Nat
  | .add .. | .sub .. => 65
  | .mul .. | .div .. => 70
  | .neg _ => 75
  | .num q => if q.blt 0 then 75 else 1024
  | .pow .. => 80
  | _ => 1024

private def constText (latex : Bool) : Lean.Name → String
  | `pi => if latex then "\\pi" else "π"
  | `infinity => if latex then "\\infty" else "∞"
  | n => toString n

private def funcText (latex : Bool) (f : Lean.Name) : String :=
  if latex then "\\" ++ toString f else toString f

/-- The plain and LaTeX renderings, which differ in exactly three places: a
named constant's spelling, a named function's, and whether an exponent is
braced. Everything else — the operators, the parentheses, the inline solidus
of a rational — is already math mode's own spelling, so one renderer produces
both and no raw `π` or `∞` can reach a LaTeX payload. -/
partial def renderWith (latex : Bool) (need : Nat) (e : SymExpr) : String :=
  let paren (s : String) : String := if prec e < need then "(" ++ s ++ ")" else s
  match e with
  | .var n => toString n
  | .num q => paren (ratText q)
  | .const n => constText latex n
  | .app f a => funcText latex f ++ "(" ++ renderWith latex 0 a ++ ")"
  | .neg a => paren ("-" ++ renderWith latex 75 a)
  | .add a b => paren (renderWith latex 65 a ++ " + " ++ renderWith latex 66 b)
  | .sub a b => paren (renderWith latex 65 a ++ " - " ++ renderWith latex 66 b)
  | .mul a b => paren (renderWith latex 70 a ++ "*" ++ renderWith latex 71 b)
  | .div a b => paren (renderWith latex 70 a ++ "/" ++ renderWith latex 71 b)
  -- the exponent is the one slot where the two renderings differ in SHAPE:
  -- LaTeX braces it always (`e^{t}`), so a compound exponent stays in the
  -- superscript instead of falling out of it
  | .pow a b =>
      let base := renderWith latex 81 a
      if latex then paren (base ++ "^{" ++ renderWith latex 0 b ++ "}")
      else paren (base ++ "^" ++ renderWith latex 81 b)

def render (e : SymExpr) : String := renderWith false 0 e
def latex (e : SymExpr) : String := renderWith true 0 e

/-- Is every VARIABLE name in here typesettable as written? The constants and
the function names come from the fixed vocabulary above and are spelled for
math mode by `constText`/`funcText`, so the variable is the only path by which
arbitrary text could reach a LaTeX payload — the same hole a function's binder
is, and the same rule closes it: ASCII letters and digits only, no invented
subscript typography. -/
partial def latexSafe : SymExpr → Bool
  | .var n => (toString n).all Char.isAlphanum
  | .num _ | .const _ => true
  | .app _ a | .neg a => latexSafe a
  | .add a b | .sub a b | .mul a b | .div a b | .pow a b => latexSafe a && latexSafe b

instance : ToString SymExpr := ⟨render⟩

end SymExpr

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

/-- The linear form a coefficient row denotes, written back in the binder
names: `#[1, 1, -1]` over `(a, b, c)` is `a + b - c`. The term conventions
are the polynomial renderer's own — `2x`, a parenthesized non-integer
coefficient `(1/2)x`, a leading minus — and the zero form is `0`. -/
private def linFormText (binders : Array Lean.Name) (row : Array Rat) : String := Id.run do
  let mut out := ""
  for i in [0:row.size] do
    let q := row[i]!
    if q == 0 then continue
    let x := toString (binders[i]?.getD Lean.Name.anonymous)
    let cs := ratText q
    let plainInt := cs.all Char.isDigit || (cs.startsWith "-" && (cs.drop 1).all Char.isDigit)
    let term :=
      if cs == "1" then x
      else if cs == "-1" then s!"-{x}"
      else if plainInt then s!"{cs}{x}"
      else s!"({cs}){x}"
    if out.isEmpty then out := term
    else if term.startsWith "-" then out := out ++ " - " ++ (term.drop 1)
    else out := out ++ " + " ++ term
  return if out.isEmpty then "0" else out

/-- Term-joining for polynomials, shared by the plain and LaTeX renderers:
the two differ in the exponent spelling and in how a COEFFICIENT is spelled,
so the caller renders the coefficients itself and passes the strings. That is
what makes the LaTeX path propagate a coefficient with no LaTeX form (its
`mapM latex?` fails before this is reached) instead of silently substituting
the plain spelling of a value it cannot typeset. -/
private def renderPolyWith (x : String) (sup : Nat → String)
    (coeffs : Array String) (ascending : Bool := false) : String := Id.run do
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
  -- `terms` came out highest-degree first, which is how a POLYNOMIAL is
  -- written. A SERIES is written the other way — it has no highest term, and
  -- its tail (`+ …`, `+ O(tⁿ)`) belongs at the end — so it asks for the
  -- ascending order instead
  let ordered := if ascending then terms.reverse else terms
  let mut out := ""
  for t in ordered do
    if out.isEmpty then out := t
    else if t.startsWith "-" then out := out ++ " - " ++ (t.drop 1)
    else out := out ++ " + " ++ t
  return out

/-! ## Formal power series (`SPEC.md` §Elementary calculus, §Ellipses)

A series is presented by finitely many coefficients PLUS the generating rule
where one exists. Both readings answer the same three questions — a
coefficient, a truncation, and a display — and the display is what says which
reading is in hand: `…` when every coefficient is known, `O(tⁿ)` when exactly
the carried ones are. -/

/-- How far a Taylor expansion is computed, and therefore how many
coefficients a `terms` series carries. A documented ceiling, not a fallback:
a truncation or a coefficient past it is a loud refusal naming this number.
(What a bare series SHOWS is `seriesShown`, below — a different question.) -/
def seriesTerms : Nat := 12

/-- How many terms a bare series displays before its tail. `SPEC.md` shows
`t + 4t^2 + 9t^3 + 16 t^4 + ...`, which is the coefficients of `t⁰ … t⁴`. -/
def seriesShown : Nat := 5

/-- The coefficient of `tⁿ`, when the presentation knows it. `none` = a
`terms` series was asked past its ceiling, which is the one thing about a
series this slice will not guess. -/
def seriesCoeff? : SeriesGen → Nat → Option Rat
  -- Horner in `n`, exactly: the rule is a polynomial with rational
  -- coefficients and `n` is a natural number
  | .rule inN, n =>
      some (inN.foldr (init := (0 : Rat)) fun c acc => acc * Rat.ofInt (Int.ofNat n) + c)
  | .terms cs, n => cs[n]?

/-- The coefficients of `t⁰ … t^(k-1)`, or `none` when a `terms` series does
not know them all. -/
def seriesUpTo? (g : SeriesGen) (k : Nat) : Option (Array Rat) :=
  (Array.range k).mapM (seriesCoeff? g)

/-- A series' visible terms and its TAIL, which says which reading is in
hand: `+ ...` for a rule (every coefficient is known, and there are infinitely
many), `+ O(tᵏ)` for terms (exactly these are known). -/
private def seriesParts : SeriesGen → Array Rat × String
  | .rule inN => ((Array.range seriesShown).map (fun n => (seriesCoeff? (.rule inN) n).getD 0),
      " + ...")
  | .terms cs => (cs, s!" + O(t^{cs.size})")

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
  -- repetition IS the display: `{1, 1}` is how a multiset says the root is double
  | .msetV elems _ =>
      "{" ++ ", ".intercalate (elems.toList.map render) ++ "}"
  -- the AMBIENT is part of the display, in SPEC.md's own subobject notation:
  -- without it the trivial subspace would render as an empty `span_ℚ{}` that
  -- says nothing about which space it is the zero of
  -- the TRIVIAL subspace displays as the {0} it is — an empty `span_ℚ{}`
  -- names no vector, and the mathematician's own spelling of the zero
  -- subspace is {0}
  | .spanV n basis =>
      if basis.isEmpty then s!"\{0} ≤ {(Domain.vector n .rat).render}"
      else
        "span_ℚ{" ++ ", ".intercalate (basis.toList.map render) ++ "} ≤ "
          ++ (Domain.vector n .rat).render
  | .progV _ first step last? =>
      let tail := match last? with | some l => s!", ..., {render l}" | none => ", ..."
      s!"\{{render first}, step {render step}{tail}}"
  | .cardinal (.finite n) => toString n
  | .cardinal .countablyInfinite => "ℵ₀"
  | .bool b => toString b
  | .sym e => e.render
  -- `(6x + 1) dx`: the coefficient is parenthesized exactly as a polynomial
  -- FACTOR is, so a sum reads as one factor rather than as a sum that
  -- swallowed the differential
  | .diff1 _ p => diffCoeffText p.render ++ " dx"
  -- SPEC.md's own displayed cell, in the generality the VALUE has: `d` knows
  -- the universal differential it is, and it does NOT know which scheme the
  -- session called `X` — a value carries no session, and naming one would be
  -- a display that lies whenever the binding is something else
  | .derivation true =>
      "d : 𝒪_X → Ω¹_{X / S}, the universal relative differential\n\n\
On global sections, for X = Spec R over S = Spec k with R = k[x]:\n\n  \
R → Ω¹_{R / k} ≅ R dx"
  | .derivation false =>
      "d/dx : k[x] → k[x], differentiation with respect to the indeterminate"
  | .cosetV offset kernel => s!"{offset.render} + {kernel.render}"
  | .seriesV _ gen =>
      let (cs, tail) := seriesParts gen
      renderPolyWith "t" plainSup (cs.map ratText) (ascending := true) ++ tail
  | .func _ _ binder body =>
      -- the body is written back in the mathematician's own binder, not in
      -- the `x` a bare polynomial renders with
      let t := toString binder
      let b := match body with
        | .poly _ cs => renderPolyWith t plainSup (cs.map render)
        | v => v.render
      s!"{t} ↦ {b}"
  | .hom _ tgt binders rows =>
      let forms := rows.toList.map (linFormText binders)
      let body := match tgt with
        | .vector .. => "(" ++ ", ".intercalate forms ++ ")"
        | _ => ", ".intercalate forms
      "(" ++ ", ".intercalate (binders.toList.map toString) ++ ") ↦ " ++ body

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

/-- The determinant over ℚ, by the same elimination `rref` runs — except that
this one KEEPS the scale `rref` normalizes away (the pivots' product, and a
sign per row swap), which is the whole of a determinant.

It exists so a reply CAN be checked against an invariant that is a number
rather than a shape (`Backends/Sage.lean`'s companion check); nothing routes
to it, and `det` on the surface is still the backend's. -/
def detQ (n : Nat) (rows : Array (Array Rat)) : Rat := Id.run do
  let mut rs := rows
  let mut d : Rat := 1
  for col in [0:n] do
    match (Array.range n).find? (fun i => col ≤ i && rs[i]![col]! != 0) with
    | none => return 0     -- a zero column: the matrix is singular
    | some i =>
        if i != col then
          let (ri, rc) := (rs[i]!, rs[col]!)
          rs := (rs.set! col ri).set! i rc
          d := -d
        let p := rs[col]![col]!
        d := d * p
        for j in [col + 1 : n] do
          let f := rs[j]![col]! / p
          if f != 0 then
            rs := rs.set! j ((Array.range n).map fun k => rs[j]![k]! - f * rs[col]![k]!)
  return d

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
subspaces are spanned over ℚ here, and a generator outside ℚⁿ is a gap rather \
than a guess"
  return (rref n rows).map fun r => .vec n .rat (r.map Value.rat)

/-- The span as a `Value` — what an executor returns for `M.ker()`.
`Denote.ofValue` turns it into the ordinary set OBJECT, exactly as it does a
returned finite set or progression. -/
def mkSpan (n : Nat) (gens : Array Value) : Except String Value := do
  return .spanV n (← mkSpanBasis n gens)

/-! ## Cosets of the constants (`SPEC.md` §Indefinite integration)

`∫ f dx` is a COSET of `ker(d/dx)`, and this slice's kernel is the CONSTANTS
of the coefficient ring. That one fact is what gives the presentation a normal
form: two primitives of the same `f` differ by a constant, so the
representative whose constant term is ZERO is a function of the coset and of
nothing else — the discipline `mkSpanBasis` follows for a subspace, and for
the same payoff (`∫ f dx = x³ + (1/2)x² + x + ℚ` compares as data). -/

/-- THE constructor of a coset: the offset, canonicalized. Every coset in the
system is built from this — the executor's antiderivative, the `p + K` a
surface `+` denotes, and a decoded frame — which is what makes two spellings
of one coset compare equal. A kernel that is not a scalar domain, or an
offset that is not a polynomial over it, is a loud refusal: this presentation
knows one kernel, and guessing another would be a claim. -/
def mkCoset (offset : Value) (kernel : Domain) : Except String (Value × Domain) :=
  match kernel with
  -- CEILING: the exact scalar domains whose ZERO is `Value.int 0` or
  -- `Value.rat 0`, which is what the canonicalization below writes. `ℤ/n` is
  -- refused rather than accepted-and-mis-canonicalized: its zero is
  -- `Value.mod n 0`, and this module cannot ask `Native.zeroOf` for it (a
  -- backend is not in `Value.lean`'s cone — see DESIGN.md §Module map's open
  -- note). No `SPEC.md` line asks for a coset over `ℤ/n`; when one does, that
  -- layering is what has to be settled first.
  | .nat | .mod _ | .series _ | .poly _ | .matrix .. | .vector .. | .funcs .. =>
      .error s!"the kernel of a coset here is the constants of a ring whose \
zero this presentation can write — ℤ, ℚ, ℝ or ℂ — and {kernel.render} is not \
one of them: a coset over it is a gap rather than a guess"
  | k =>
      match offset with
      -- the canonical representative has constant term ZERO, because two
      -- primitives of one `f` differ by exactly a constant
      | .poly c cs =>
          if cs.isEmpty then .ok (.poly c cs, k)
          else .ok (mkPoly c (cs.set! 0 (if c == .rat then .rat 0 else .int 0)), k)
      -- a SCALAR offset is its own constant polynomial, and that whole coset
      -- is the kernel: its canonical representative is zero
      | .int _ | .rat _ => .ok (mkPoly k #[], k)
      | v => .error s!"{v.render} is not a polynomial offset: a coset here is \
`p + K` with `p` in the ring and `K` its constants"

/-- Is `v` an element of the coset `offset + K`? The kernel is the CONSTANTS,
so membership is exactly "agrees with the offset in every degree above zero"
— no subtraction and no search, and the constant terms are free to differ by
anything, which is what the coset says. -/
def cosetContains (offset : Value) (v : Value) : Bool :=
  match offset, v with
  | .poly _ ps, .poly _ xs =>
      let n := max ps.size xs.size
      (Array.range n).all fun i =>
        i == 0 || (ps[i]?.getD (.int 0)) == (xs[i]?.getD (.int 0))
  -- a SCALAR is a constant polynomial, so it lies in the coset exactly when
  -- the offset has no term above degree zero
  | .poly _ ps, .int _ | .poly _ ps, .rat _ => ps.size ≤ 1
  | .int _, .int _ | .int _, .rat _ | .rat _, .int _ | .rat _, .rat _ => true
  | _, _ => false

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
        | .error s!"{v.render} has a component that does not read as a \
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
  | .msetV elems _ => do
      let es ← elems.mapM latex?
      return "\\{" ++ ", ".intercalate es.toList ++ "\\}"
  | .spanV n basis => do
      if basis.isEmpty then
        return "\\{0\\} \\leq " ++ (Domain.vector n .rat).latex
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
  -- a symbolic expression typesets: `\sin(t)`, `e^{t}`, `1/t`, `\pi`,
  -- `\infty` — its renderer is the one that spells the constants and the
  -- function names for math mode, so no raw `π` or `∞` reaches a payload.
  -- The VARIABLE is the mathematician's own name and gets the rule a
  -- function's binder gets below: ASCII alphanumerics only
  | .sym e => if e.latexSafe then some e.latex else none
  -- `(6x + 1)\,dx`: the thin space is what separates a coefficient from a
  -- differential in math mode, and `dx` is upright text in neither
  -- convention — it is two ordinary math italics, which is what `dx` means
  | .diff1 _ p => do return diffCoeffText (← latex? p) ++ "\\,dx"
  -- the two derivations are the documented no-natural-form case the truth
  -- value is: their renderings are prose ABOUT an operation, not mathematics
  | .derivation _ => none
  | .cosetV offset kernel => do return (← latex? offset) ++ " + " ++ kernel.latex
  -- `\ldots` and `O(t^{5})` are math mode's own spellings; the braced
  -- exponent is the table's convention
  | .seriesV _ gen =>
      let (cs, _) := seriesParts gen
      let tail := match gen with
        | .rule _ => " + \\ldots"
        | .terms ts => s!" + O(t^\{{ts.size}})"
      some (renderPolyWith "t" latexSup (cs.map ratText) (ascending := true) ++ tail)
  | .func _ _ binder body => do
      let t := toString binder
      let b ← match body with
        | .poly _ cs => (cs.mapM latex?).map (renderPolyWith t latexSup)
        | v => latex? v
      -- the binder is the mathematician's own name, and a `θ` reaches math
      -- mode as raw Unicode, which MathJax does not typeset and pdflatex
      -- rejects outright: no LaTeX form, so the cell falls back to plain text
      if t.all Char.isAlphanum then return t ++ " \\mapsto " ++ b else none
  | .hom _ tgt binders rows => do
      -- non-alphanumeric binders fall back to plain text, as `.func`'s does
      if !binders.all (fun b => (toString b).all Char.isAlphanum) then none
      else
        let forms := rows.toList.map (linFormText binders)
        let body := match tgt with
          | .vector .. => "(" ++ ", ".intercalate forms ++ ")"
          | _ => ", ".intercalate forms
        some ("(" ++ ", ".intercalate (binders.toList.map toString) ++ ") \\mapsto "
          ++ body)

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
    | .error s!"{exact.render} is not one of the exact real values presented \
here (a rational, or a + b√d with d > 0), so no decimal certificate covers it"
  let some r := decimalToRat? decimal
    | .error s!"{repr decimal} is not a decimal presentation"
  unless absLtRat (a - r) b d achieved do
    .error s!"the decimal {decimal} is not within O({tolText achieved}) of \
{exact.render}: the certificate does not hold, and the digits shown ARE the claim"
  return .approx exact decimal eps achieved

end Value

def CmpOp.render : CmpOp → String
  | .le => "≤" | .lt => "<" | .ge => "≥" | .gt => ">"

namespace CasExpr

/-- The spelling a stored surface expression displays with — what puts the
guard of a predicate set back on the screen as it was written. Total, in the
`reprShape` discipline: the shapes a comprehension guard can be are rendered
exactly, and a shape outside that vocabulary names itself rather than
rendering as something it is not. -/
partial def render : CasExpr → String
  | .num z => toString z
  | .lit v => v.render
  | .ref n => s!"{n}"
  | .dom d => d.render
  | .neg e => s!"-{e.render}"
  | .bin op a b =>
      let o := match op with
        | .add => " + " | .sub => " - " | .mul => "·" | .div => "/" | .pow => "^"
      s!"{a.render}{o}{b.render}"
  | .app f args =>
      s!"{f.render}({", ".intercalate (args.toList.map render)})"
  -- the `contains` call IS the guard-position `∈` (one relation, one
  -- production), so it displays as the membership it spells
  | .method r m args =>
      if m == `contains && args.size == 1 then s!"{args[0]!.render} ∈ {r.render}"
      else s!"{r.render}.{m}({", ".intercalate (args.toList.map render)})"
  | .cmp op a b => s!"{a.render} {op.render} {b.render}"
  | .conj a b => s!"{a.render} and {b.render}"
  | .sqrt e => s!"√{e.render}"
  | .magnitude e => s!"|{e.render}|"
  | .index r a => s!"{r.render}[{a.render}]"
  | _ => "(an expression this display does not spell)"

end CasExpr

namespace SetPresentation

partial def render : SetPresentation → String
  | .finite _ elems =>
      "{" ++ ", ".intercalate (elems.toList.map (·.render)) ++ "}"
  | .multiset _ elems =>
      "{" ++ ", ".intercalate (elems.toList.map (·.render)) ++ "}"
  | .arithProg _ first step none =>
      s!"\{{first.render}, {Value.progSecond "…" first step}, ...}"
  | .arithProg _ first step (some last) =>
      s!"\{{first.render}, {Value.progSecond "…" first step}, ..., {last.render}}"
  | .span n basis =>
      if basis.isEmpty then s!"\{0} ≤ {(Domain.vector n .rat).render}"
      else
        "span_ℚ{" ++ ", ".intercalate (basis.toList.map (·.render)) ++ "} ≤ "
          ++ (Domain.vector n .rat).render
  | .domainSet d => d.render
  | .product a b => s!"{render a} × {render b}"
  | .powerset s => s!"𝒫({render s})"
  | .coset offset kernel => s!"{offset.render} + {kernel.render}"
  | .domainDiff a b => s!"{a.render} - {b.render}"
  | .predicate dom binder guard =>
      s!"\{{binder} ∈ {dom.render} | {guard.render}}"

instance : ToString SetPresentation := ⟨render⟩

/-- The LaTeX form of a set presentation. `none` propagates from an element
that has none. -/
partial def latex? : SetPresentation → Option String
  | .finite _ elems => do
      let es ← elems.mapM Value.latex?
      return "\\{" ++ ", ".intercalate es.toList ++ "\\}"
  | .multiset _ elems => do
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
      if basis.isEmpty then
        return "\\{0\\} \\leq " ++ (Domain.vector n .rat).latex
      let bs ← basis.mapM Value.latex?
      return "\\mathrm{span}_{\\mathbb{Q}}\\{" ++ ", ".intercalate bs.toList
        ++ "\\} \\leq " ++ (Domain.vector n .rat).latex
  | .domainSet d => some d.latex
  | .product a b => do return (← latex? a) ++ " \\times " ++ (← latex? b)
  | .powerset s => do return "\\mathcal{P}(" ++ (← latex? s) ++ ")"
  | .coset offset kernel => do
      return (← Value.latex? offset) ++ " + " ++ kernel.latex
  -- `\setminus` is what the minus between two SETS means in math mode
  | .domainDiff a b => some (a.latex ++ " \\setminus " ++ b.latex)
  -- the guard is stored as the surface expression, which has a text spelling
  -- but no LaTeX one; `none` is the honest form, and the cell shows the text
  | .predicate .. => none

end SetPresentation

namespace Obj

def render : Obj → String
  | .elem _ v => v.render
  | .domainObj d => d.render
  | .setObj s => s.render
  | .cyclicModule n => s!"ℤ/{n} as ℤ-module"
  | .specOf r => s!"Spec {r.render}"
  | .symObj e => e.render

/-- The LaTeX form of an object. The module fixture has none ON PURPOSE:
`\mathbb{Z}/4\mathbb{Z}` typeset alone is the ring, and equality here is
category-bound (DESIGN.md §Surface), so displaying the module as its
underlying object would be a display-level lie. -/
def latex? : Obj → Option String
  | .elem _ v => v.latex?
  | .domainObj d => some d.latex
  | .setObj s => s.latex?
  | .cyclicModule _ => none
  -- `\mathrm{Spec}` is the operator name, as `\mathrm{Mat}` and
  -- `\mathrm{span}` already are in this renderer's table
  | .specOf r => some ("\\mathrm{Spec}\\, " ++ r.latex)
  | .symObj e => if e.latexSafe then some e.latex else none

/-- The presentation string used in capability gaps and diagnostics. -/
def presentation : Obj → String
  | .elem d v => s!"{v.render} ∈ {d.render}"
  | .domainObj d => d.render
  | .setObj s => s.render
  | .cyclicModule n => s!"ℤ/{n} as ℤ-module"
  | .specOf r => s!"Spec {r.render}"
  | .symObj e => e.render

/-- The LaTeX form matching `presentation`: for an element, the value and
its domain (`v \\in D`); for other objects, `latex?` unchanged. -/
def presentationLatex? : Obj → Option String
  | .elem d v => v.latex?.map fun l => s!"{l} \\in {d.latex}"
  | o => o.latex?

instance : ToString Obj := ⟨render⟩

end Obj

end CasDsl
