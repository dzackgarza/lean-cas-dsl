# CasDsl — design of the vertical slice

A categorically organized CAS hosted in Lean, shipped as a DSL plugin for
[lean-jupyter-kernel](https://github.com/dzackgarza/lean-jupyter-kernel).

**The governing surface spec is [`SPEC.md`](SPEC.md)** — the user's original
guiding document ("Elementary mathematics"), authored 2026-07-29 and recovered
into the repo verbatim on 2026-07-30. Every surface decision here subordinates
to it; the vertical slice's fixtures (`x³ − 2x + 1`, `[1,2;3,4] ∈ Mat₂(ℚ)`,
`360.factor()`, the ellipses, ℝ/O(ε)) come from it directly.

Derived planning artifacts live in the project vault (`FEATURE-LEAN-CAS-DSL`,
`SPEC-CATEGORICAL-CAS-PROBLEM` — an agent-authored problem *statement*, not
the user's spec — `PLAN-CAS-TYPE-PREPASS`, `PLAN-CAS-VERTICAL-SLICE`,
`DECISION-CAS-DSL-ANTI-DRIFT`). This file is the implementation-facing
contract: the module map, the core data model, and the decisions every
module must respect.

## Program trajectory (user ruling, 2026-07-30)

This repo is stage one of a three-stage program:

1. **Spike**: a proof of concept that is genuinely useful for standard
   Wolfram-Alpha-style undergraduate queries as sketched in `SPEC.md`, with
   slightly more mathematical rigour (`assert`, honest structured gaps) and
   *shadows* of the eventual language design (category-flavored ascription,
   the resolver seam). The spike's work queue is the `SPEC.md` coverage
   ledger (#24).
2. **Evaluation**: after the spike, real use judges actual usefulness,
   likely refining how the base language works (#13 is the mechanism).
3. **Rewrite** on the full proper categorical foundations — which this repo
   deliberately does NOT know yet; lean-lattices/CategoryGraph provides them
   (#12/#14/#15 track that boundary).

Binding consequence: **engine deepening is frozen at current depth** — no
further foundational machinery in this repo unless a `SPEC.md` item forces
it. Breadth of spec surface outranks foundation work until the evaluation.

## The invariant pipeline

```text
surface expression                     (backend-blind mathematical syntax)
  -> object + category profile         (rich memberships, not one nominal class)
  -> method resolution                 (direct + subcategory-inherited, ONE boundary)
  -> backend-neutral request           (method id + typed presentation)
  -> capability router                 (developer policy; deterministic)
  -> executor                          (native Lean, or a direct backend adapter)
  -> trusted typed Value               (ordinary CAS trust; no proof obligation)
  -> notebook state                    (env-extension bindings; snapshot/replay safe)
```

Two judgments are always kept separate:

- **semantic availability** — the category graph says the method is
  meaningful for this object;
- **implementation availability** — a registered route can currently
  execute it for this presentation.

A missing route is a structured `NoImplementation` gap surfaced at
execution. It never removes the method, narrows a category, weakens a type,
or picks a different operation.

## Module map

```text
CasDsl/Value.lean       Domain, Value, SetPresentation, Obj  (core data model)
                        + their plain-text and LaTeX renderings
                        + the shared EXACT-ARITHMETIC FLOOR (see below)
CasDsl/Category.lean    CatRef, category/method/functor/route/canonical-map TYPES
CasDsl/Registry.lean    env extensions + registration API (semantic state)
CasDsl/Resolve.lean     the method resolver (the ONE lookup boundary)
CasDsl/Route.lean       capability router + structured gaps
CasDsl/Native.lean      native Lean executors (arith, poly eval, nth, annihilator)
CasDsl/Port.lean        generic framed child-process port (no Sage branches)
CasDsl/Backends/Sage.lean  direct Sage adapter (Lean side)
CasDsl/Eval.lean        casTerm evaluator: resolve -> route -> execute
CasDsl/Syntax.lean      surface syntax: commands + casTerm category
CasDsl/Diagnostics.lean #explain_route, #capabilities, #capability_gaps
CasDsl/Std.lean         standard universe: categories, methods, routes, profiles
CasDsl/Notebook.lean    the prelude module (the plugin manifest)
backends/sage_adapter.py   Python half of the Sage adapter (runs under sage -python)
tests/                  Lean #guard test module + Python roundtrip + E2E notebook run
```

Dependency arrows flow downward only. `Port.lean` knows nothing about Sage
operations; `Backends/Sage.lean` knows nothing about surface syntax.

**`Value.lean` is the shared exact-arithmetic FLOOR** — the only module both
backends may import, and therefore where exact arithmetic goes when more than
one of them needs it. A backend that must compute something to CHECK a
certificate puts that computation here, not in its own half: a backend does
not import another backend, so a copy in `Backends/Sage.lean` would be the
second implementation of arithmetic that already exists. Nothing in this
module may route, execute, or name a backend — it is data, normal forms, and
the arithmetic those normal forms are made of. `mkAlg`, `rref`, `spanContains`
and `detQ` are all there for that reason.

PRE-RULING for the next unit (recorded as such, project-owner call): U8's
certificate arithmetic — polynomial add/sub/mul for the derivative and
integral reply checks — goes DOWN into this floor under the same rule. Not
duplicated in `Backends/Sage.lean`, and no import exception. `Eval.lean`'s
polynomial helpers stay where they are and keep serving the surface; what a
certificate needs gets a `Value`-level twin, and only as certificates demand
it — not preemptively.

## Core data model (`Value.lean`)

Presentations and values are first-order, serializable data (they live in
env extensions, so no closures):

```lean
inductive Domain
  | nat | int | rat
  | real | complex                 -- ℝ, ℂ: inhabited by exact algebraic values
  | mod (n : Nat)                  -- ℤ/n
  | poly (coeff : Domain)          -- coeff[x], univariate
  | matrix (n : Nat) (entry : Domain)   -- Matₙ(entry), square in the slice
  | vector (n : Nat) (entry : Domain)   -- Eⁿ, SPEC.md's ℚ² and ℚ³
  | funcs (src tgt : Domain)       -- src → tgt

inductive Value
  | int (z : Int)                  -- also ℕ elements
  | rat (q : Rat)
  | mod (n : Nat) (v : Nat)        -- normalized v < n on construction
  | poly (coeff : Domain) (coeffs : Array Value)   -- ascending, no trailing zeros
  | mat (n : Nat) (entry : Domain) (rows : Array (Array Value))
  | vec (n : Nat) (entry : Domain) (comps : Array Value)   -- (1, 2) ∈ ℚ²
  | factorization (unit : Value) (factors : Array (Value × Nat)) (dom : Domain)
  | idealV (gens : Array Value) (ring : Domain)    -- e.g. annihilator result
  | setV (elems : Array Value) (dom : Domain)      -- e.g. p.roots()
  | progV (dom : Domain) (first step : Value) (last? : Option Value)  -- e.image()
  | spanV (n : Nat) (basis : Array Value)          -- M.ker(), a subspace of ℚⁿ
  | cardinal (c : Cardinality)     -- finite n | countablyInfinite
  | bool (b : Bool)
  | func (src tgt : Domain) (binder : Name) (body : Value)   -- binder ↦ body

inductive SetPresentation
  | finite (dom : Domain) (elems : Array Value)
  | arithProg (dom : Domain) (first step : Value) (last? : Option Value)
  | domainSet (d : Domain)         -- the underlying set of ℤ, ℕ, ℚ, …
  | span (n : Nat) (basis : Array Value)   -- span_ℚ{…} ≤ ℚⁿ, by a REDUCED basis
  | product (a b : SetPresentation)     -- A × B, denoted
  | powerset (s : SetPresentation)      -- 𝒫(A) / 2^A, denoted
  | domainDiff (a b : Domain)           -- ℂ - ℚ, denoted

inductive Obj                       -- the thing a notebook binding names
  | elem (dom : Domain) (v : Value)         -- 360 ∈ ℤ, q ∈ ℚ[x], M ∈ Mat₂(ℚ)
  | domainObj (d : Domain)                  -- ℤ itself (a set-with-structure)
  | setObj (s : SetPresentation)            -- {0, 2, 4, ...}
  | cyclicModule (n : Nat)                  -- the ℤ-module ℤ/n (module fixture)
```

`setV`, `progV` and `spanV` are the three shapes an EXECUTOR may return as a
set (`p.roots()`, `e.image()`, `M.ker()`); `Denote.ofValue` turns them into
the ordinary `setObj (.finite …)` / `setObj (.arithProg …)` /
`setObj (.span …)`, so a returned set is a set object like any literal one —
same profile rules, same `contains`, same set equality — rather than a second
notion of set. CEILING: an explicit finite list, an arithmetic progression,
and a subspace of ℚⁿ, nothing wider. `product` and `powerset` are DENOTED
sets (see §Sets): presentations whose elements — pairs, and sets — no `Value`
presents.

Set equality (`X = ℕ`) is presentation normalization: `arithProg 0 1 none`
over ℕ normalizes to `domainSet nat`, etc. This is a documented ceiling,
not a general decision procedure.

`Cardinality` has no uncountable constructor, so `domainCard` is partial:
`ℝ`, `ℂ` and a function domain report that the slice CANNOT state their size
rather than being given `ℵ₀`. Giving ℝ and ℂ inhabitants does not change
that — see §Exact number systems.

## Exact number systems (`SPEC.md` §Exact number systems, issue #24)

ℝ and ℂ are INHABITED, by exact algebraic numbers in the normal form
`a + b√d` — `Value.alg` with `a`, `b` rational, `d` a square-free integer
other than 0 and 1, and `b ≠ 0`. `√(-1)` is `i`, so the SIGN of the radicand
decides which domain a value presents (ℝ for `d > 0`, ℂ for `d < 0`), and
`Value.mkAlg` is the constructor every value the surface produces goes
through: it moves the square part of `d` into `b` and returns the RATIONAL
when `b` vanishes (the prelude and test FIXTURES are written in normal form
directly, stating the value they mean — nothing computed skips it). That is
what makes `√8` literally `2√2` and keeps a surd out of ℚ, which in turn is
what lets equality, membership and set operations decide on these values at
all.

- **Everything here is exact, and nothing in this section approximates.**
  `√2`, `i`, `2√2`, `(-1+√5)/2` are algebraic numbers, not decimals; the
  arithmetic is `Rat` arithmetic inside one quadratic field
  (`Native.scalarAdd`/`Mul`/`Div` grow surd arms, and `√2 · √2 = 2` exactly,
  which is what makes `q(√2) = 0` an identity rather than a sample).
  Numerical approximation is a separate OPERATION on an exact element —
  `SPEC.md`'s `map √2 to ℝ/O(1/10^{10})` — and it lives in
  §Numerical approximation, where the exact value is KEPT and a decimal
  presentation of it is certified against it.
- **CEILING: one square root over ℚ.** `√2 + √5` leaves the presentation and
  is a loud refusal naming itself as a gap ("that is a gap, not an
  approximation"); `√` of anything but a rational is refused the same way.
  A second ceiling sits under the first: `Value.squareFactorCap` bounds the
  trial division that certifies a square-free radicand, and a radicand past
  it is refused rather than left unnormalized — an unnormalized radical would
  compare unequal to its own normal form and quietly break `√8 = 2√2`.
- **`re`, `im`, `bar` and `abs` are NATIVE.** They are structural reads of
  `a + b√d` that the engine genuinely decides (`im` carries the radical:
  `im(2i√3)` is `2√3`, and the modulus of a Gaussian rational is the exact
  `√(a² - b²d)`), so nothing is asked of a backend. A REAL receiver is its
  own real part, has no imaginary part and is its own conjugate — ℝ ⊆ ℂ,
  spelled out — and the sign of a real surd is decided by SQUARING, never by
  evaluating a decimal. They are declared on `ComplexElems`, whose profile
  rules name ℂ and ℝ one domain at a time (the convention `ℤ/n` already
  follows): `3.re()` is therefore the honest "not a method of any category
  this object belongs to", a missed specificity rather than a claim.
- **`|·|` is ONE spelling of two methods** — `cardinality` for a set, `abs`
  for an element — chosen by the receiver in `Eval`, both ordinary category
  methods resolved and routed like any other. `|3|` stays the not-a-method
  error it always was; only the method named in it changed.
- **ℝ and ℂ are `Sets` and nothing narrower.** Both are uncountable:
  `domainCard` still cannot state their size (`ℝ.cardinality()` says so), and
  `nth` — declared on `CountableSets` — does not reach them at all. What they
  gained is MEMBERSHIP: `√2 ∈ ℝ`, `2 + 2i ∈ ℂ`, `√2 ∉ ℚ` are decided from the
  presentation. A domain used as a method RECEIVER arrives as a name, not as
  its own token, which is why `Eval.domainAlias?` carries the Unicode
  spellings (§Surface).
- **`i` is a CONSTANT, not a binding** (`Eval.constantValue?`), consulted
  after the session bindings and the domain aliases — so `let i := 5 in ℤ`
  shadows it exactly as `let R := …` shadows ℝ, and `2 + 2i` is then 12.
- **ℂ[x] is where the cubic splits**, and `roots` STILL answers in the
  polynomial's own coefficient ring. `map p to ℂ[x]` is the ordinary
  registered coercion (ℤ ⊆ ℂ, coefficient-wise), `factor` and `roots` are
  routed there to their own Sage ops, and SPEC.md's displayed factorization
  `(x-1)(x - (-1+√5)/2)(x - (-1-√5)/2)` comes back as three monic linear
  factors with exact `a + b√d` coefficients. Its CONTENT is what is pinned —
  each displayed root evaluates to zero, and a near miss does not — because
  the factor ORDER and the unit convention are the backend's (decision 7).
  DISCLOSED, and OPEN: SPEC.md writes `assert q.roots() ⊆ ℂ - ℚ` for
  `q ∈ ℚ[x]`, where `q.roots()` is EMPTY — so that line runs and holds
  VACUOUSLY, checking nothing. The contentful claim is the same one after
  `map q to ℂ[x]`, where the root set is `{√2, -√2}`; both are pinned, side by
  side, everywhere they appear. Which of the two `roots` should DEFAULT to is
  an open question escalated to the project owner (§Open questions) — reaching
  into an extension by itself would be exactly the silent reach §Standard
  universe forbids, so the ring stays the default until that is ruled on.

## Numerical approximation (`SPEC.md` §Exact number systems, issue #7)

`map √2 to ℝ/O(1/10^{10})` displays `1.4142135623 + O(1/10^{10})`, and
everything about that line is a REQUEST rather than a new number system.

- **`ℝ/O(ε)` is SUGAR for a requested absolute tolerance, not a quotient.**
  `|a − b| < ε` is not transitive, so there are no classes: nothing is an
  element of `ℝ/O(ε)`, and ℝ is not included in it. The spelling is therefore
  a surface production that is meaningful ONLY after `map … to`
  (`CasExpr.approxTarget`); written anywhere else — `assert ℝ ⊆ ℝ/O(1/10)`,
  `√2 ∈ ℝ/O(1/10)`, a `let` — it is a loud refusal saying so. That is stronger
  than answering `false`: the claim cannot be stated at all, which is why no
  `Domain` constructor and no `CanonicalMap` entry exists for it (either would
  have to answer membership, cardinality and inclusion questions that a
  request has no answers to).
- **The fork this design came out of, recorded so it is not re-derived.**
  Issue #7's unit contract said the canonical-map registry should OWN
  `map … to ℝ/O(ε)`, registered with a `CanonOp` constructor declaring
  `isInclusion := false`. That is not satisfiable: `CanonOp.apply` is PURE
  while the value needs arbitrary-precision evaluation from a backend, so any
  such constructor's arm could only error — dead registry data — and keying a
  rule at all needs a `Domain` for `ℝ/O(ε)`, which would force total-match
  answers to membership, cardinality and inclusion that a REQUEST has none of
  (`x ∈ ℝ/O(ε)` answering `false` is a claim; `|ℝ/O(ε)|` is not a size).
  The branch taken instead is the one below: the registry keeps deciding what
  may be presented in ℝ, a routed method owns executability, and the result
  joins the results-that-are-not-elements family. `ℝ ⊆ ℝ/O(ε)` is then
  UNSTATABLE rather than false, which is strictly stronger than the flag would
  have been, and the refusal is pinned in its place (design review 2026-07-30,
  endorsed by the project owner).
- **TWO registries answer, in order, and neither answers the other's
  question.** The canonical-map registry decides whether the value may be
  PRESENTED IN ℝ at all — `map 1/3 to ℝ/O(ε)` rides the registered ℚ ⊆ ℝ, and
  `2 + 2i` is the ordinary "there is no preferred canonical map of 2 + 2i into
  ℝ", because no ℂ → ℝ rule is registered (§Coercions) — and the router
  decides whether a decimal to that tolerance can be COMPUTED. `approximate`
  is an ordinary category method (declared on `ComplexElems`, arity 1) with an
  ordinary route, so `x.approximate(ε)` is a second spelling of the same
  operation and `#explain_route` explains it. To the mathematician the map is
  ONE construct, and the desugaring stays internal: no failure of the map
  spelling names the method, and the pins say so. It appears where it is the
  audit's subject — `#capability_gaps`, `#explain_route`, and an explicit
  `x.approximate(ε)` call.
- **The result is a VALUE, not an element of a domain.** `Value.approx` keeps
  the exact source, the decimal presenting it, the tolerance requested and the
  bound the backend certified; `valueDom?` gives it none, the slot a
  factorization, an ideal and a cardinal already occupy. **Arithmetic on it is
  refused** — a requested tolerance is not an error term, and this slice does
  not invent an error calculus to propagate one (`Native.noCommonKind` words
  that refusal). Compute exactly and approximate the result.
- **The backend chooses the numeric strategy and the Lean side VERIFIES the
  certificate.** The adapter takes the exact value and ε and returns the
  decimal plus the bound it achieved; which arithmetic it used to get there
  (interval, ball, adaptive) is named nowhere in this surface. `Value.mkApprox`
  is the one constructor and it is a CHECK: the decimal must lie within the
  certified bound of the exact value, and that bound must be positive and meet
  the request. Both entry points — the wire codec and the executor's reply —
  go through it, so a backend returning a wrong digit fails at the boundary.
  The check is exact (`Value.absLtRat`, the squaring comparison
  `Value.nonNegSurd` makes), and it covers EVERY value this slice presents,
  since they are all rationals or `a + b√d`. A value only a backend could
  evaluate would have no `realParts?` and is refused rather than trusted
  silently; when such values arrive, this is the seam where trust would have
  to be declared, and the declaration would have to be visible here.
  What is checked in the ADAPTER's reply rather than in the constructor is
  that the approximation is OF the value that was sent — a certificate that
  holds for some other number is still a wrong answer to this call.
- **The digits shown ARE the claim, and the claim is the BOUND.** The
  certificate does not prescribe truncation or rounding: `1.4142135623` and
  `1.4142135624` both present √2 within `10^{-10}` and both are accepted,
  while a digit that is wrong at that bound is not. (The shipped adapter
  truncates, and reports `10^{-k}` — a strict bound, since truncation error
  lies in `[0, 10^{-k})`.)
- **ε ≤ 0 is refused at the SURFACE**, as not-a-tolerance rather than as a
  capability failure: no finite decimal presentation lies within 0 of an
  irrational number, and a negative bound is not a request. The two failures
  say different things about the system and are worded differently.
- **A tolerance no configured backend meets is a CAPABILITY failure naming
  what was asked** (`EvalError.approxRequest`). It WRAPS the underlying
  failure rather than replacing it, so a capability gap under it still renders
  as the structured `NoImplementation` it is, an unreachable backend still
  says so, and ε is visible either way. The shipped adapter's ceiling is
  `MAX_DIGITS = 1000`, a loud ceiling like `powersetExpCap` — past it the
  refusal names the requested tolerance and the ceiling, and never returns a
  coarser answer as if it had been requested.
- **A ℂ receiver is a deliberate capability gap**, asserted next to `det` over
  ℤ/5: asking for a decimal is meaningful for every exact number, only the
  reals are routed, and a real decimal is not a presentation of a complex
  number. Projecting to the real part or the modulus would answer a question
  nobody asked.

## Functions (`SPEC.md` §Functions, issue #25)

A function is `binder ↦ body` in an ascribed `src → tgt`. Both surface
spellings — `let h := t ↦ e in ℝ → ℝ` and `let h(t) := e in ℝ → ℝ` — reach
the same `evalBinderBinding`, where the ASCRIPTION decides what the binder
means: a polynomial domain reads it as the indeterminate of `D[x]`, a
function domain builds the `Value.func`. Equality is therefore the ordinary
value equality of two bodies, and the binder is a bound name — `t ↦ t² + 1`
and `s ↦ s² + 1` are one function (`Native.valueEq`).

Decisions, all load-bearing:

- **bodies are exact polynomials.** SPEC.md's claims here (`h(-t) = h(t)`,
  `(f ∘ g)(t) = t⁶`) are identities of function EXPRESSIONS, not samples, so
  they are settled by substituting one polynomial into another
  (`Eval.applyPoly`, Horner over `valueBin` rather than `Native.polyEval`'s
  scalar Horner). A body the polynomial engine cannot express — `t ↦ sin(t)`,
  `t ↦ e^t` — used to be refused AT THE BINDING, as a gap that would stay one
  "until the calculus sections land". They have landed, and such a body is now
  read SYMBOLICALLY instead (§Symbolic function expressions). The polynomial
  reading is still PREFERRED and still tried first, for the reason this bullet
  gives: it is the one that DECIDES. Nothing is approximated either way;
- **the ascription is CHECKED at the call boundary** (`Eval.atDomain`): the
  argument enters through the preferred canonical map into `src` and the
  result lands in `tgt`, or the call fails. `e(-1)` for `e : ℕ → ℕ` is
  therefore an error, and `k(t) = t + 7 in ℤ/5 → ℤ/5` gives `k(4) = 1`
  rather than 11 — on the SCALAR path the body is computed over ℤ and the
  target coercion is the ring quotient, which agrees because a polynomial
  with integer coefficients commutes with `ℤ → ℤ/n`. The SYMBOLIC path
  (a polynomial argument or result) does not rely on that: it coerces
  coefficient-wise into `D[x]`, so `k(t)` is `t + 2` in ℤ/5 rather than an
  unreduced ℤ polynomial escaping its own domain. Only `.real` passes
  through unchecked, having no `Value`s to check;
- **an ℝ arrow still checks nothing, and the reason CHANGED.** It used to be
  that no `Value` presented ℝ; §Exact number systems ended that, and
  `atDomain`'s `.real` pass-through is kept deliberately anyway. A check
  there would buy the rejection of values no canonical map carries into ℝ (a
  residue class, a matrix) and would cost the SYMBOLIC path its ring:
  `coerceValue (.poly .real)` re-tags a ℤ[x] function expression as ℝ[x], and
  `SPEC.md`'s `(f ∘ g)(t) = t⁶` would then be stated in a different ring from
  its right-hand side and compare unequal. Disclosed residue, unchanged by
  this unit: an ℝ-declared function applied to a residue class computes in
  ℤ/n, and says so in its result's presentation. `R` and `RR` are registered
  spellings of ℝ, `CC` of ℂ (`Eval.domainAlias?`), consulted after the
  bindings so `let R := …` still shadows them;
- **a callee's binder is in scope only where it is called.** Inside a call's
  argument, and across an assertion that contains such a call
  (`Eval.calledBinder?`), the binder names the indeterminate of
  `Eval.bodyRing body` — the ring the body actually lives in. That is what
  lets SPEC.md write `h(-t) = h(t)` and `(f ∘ g)(t) = t⁶`, where `t` appears
  on the side that is not the call. NOTHING wider: a bare `t` in an ordinary
  cell is the loud "not bound" error even with `h` in scope, so defining a
  function never converts a typo elsewhere into a silent indeterminate. A
  real `let t := …` wins over the binder, which `eval` consults only after
  the bindings. Disclosed residue: INSIDE an assertion that calls the
  function, a typo matching that callee's binder still reads as the
  indeterminate — the outcome is then the honest `unknown` or a false
  assertion, never a wrong answer;
- **the ring is the SOURCE domain** (`Eval.binderRing`), so a symbolic call
  on a `ℤ/5` arrow is symbolic in ℤ/5. ℝ is the exception it always is: with
  no `Value`s of its own, the body's ring stands in. A body that is not a
  polynomial has no such ring and fails loudly at both call sites — there is
  no silent ℤ default;
- **calling and composing are elaboration-inserted**, exactly like calling a
  polynomial (decision 6): no method, no route, no backend. `f ∘ g` keeps
  `g`'s binder and requires the domains to meet — composing along a mismatch
  is a mathematical error, not something to coerce past.

Functions register exactly ONE category, method and route: `image`
(see §Comprehensions and images). Everything else about them — calling,
composing, equality, the ascription check — is elaboration-inserted and
routes nothing, because none of it is a computability question this slice
can route. What a map does to a whole SET is one, so it is a method like any
other.

## Differentials (`SPEC.md` §Differentials, issue #24)

`d` and `(d/dx)` are ONE operation with two RESULT SHAPES, and the operation
is the ordinary `derivative` method: `d(f)` is the 1-form `f' dx` and
`(d/dx)(f)` is the polynomial `f'`. Applying either is elaboration-inserted
exactly as calling a polynomial is (decision 6) — no second method, no second
route, and `#explain_route f.derivative()` explains both.

- **The derivative is NATIVE, and therefore has no certificate.** The
  derivative of a KNOWN polynomial is `i·cᵢ` shifted down by one, which is
  exact coefficient arithmetic this engine already owns, so no backend is
  asked and there is nothing for one to get wrong. The pre-ruling recorded in
  §Module map — that U8's derivative and integral reply checks go down into
  `Value.lean`'s exact-arithmetic floor — presumed a BACKEND computed them;
  not having a backend is strictly stronger than checking one, and strictly
  less code, so it supersedes the pre-ruling. (`Value.lean` is unchanged by
  this section: no certificate needs an arithmetic twin there.)
- **A 1-FORM IS NOT A POLYNOMIAL.** `Ω¹_{k[x]/k} ≅ k[x] dx` is free of rank
  one, so `Value.diff1` carries the coefficient and nothing else — and
  `d(f) = 6x + 1` is FALSE rather than incomparable, which is the theorem
  about the two presentations that `valueEq` already states for a matrix
  against a vector. Two 1-forms compare by their coefficients; the
  coefficient DOMAIN is a presentation tag and does not decide, exactly as a
  vector's entry domain does not.
- **Ω¹ is not a `Domain`.** A 1-form joins the domainless RESULT family (a
  factorization, a cardinal, an approximation), so `d(f) ∈ Ω¹` is not a claim
  this surface can state at all. What `SPEC.md` asks of Ω¹ is its display and
  the equality above; the module structure belongs to CategoryGraph.
- **A bare `d` displays the universal differential in the generality the
  VALUE has.** `SPEC.md`'s own cell names the `X` it just defined; a value
  carries no session, so naming one here would be a display that lies the
  moment the binding is something else. The rendering states the general
  shape — `d : 𝒪_X → Ω¹_{X / S}`, and on global sections `R → Ω¹_{R/k} ≅ R dx`
  for `R = k[x]` — which is true whatever `X` is. Textual on purpose, like
  every other display that is prose ABOUT an operation.
- **`Spec R` and `Schemes/ℚ` are ASCRIPTION TAGS**, the standing `QQ-Mod`
  has. `Obj.specOf` carries the ring and NOTHING else — it is not a set, it
  owns no method, and the acceptance proofs assert exactly that
  (`cardinality`, `contains` and `derivative` are all `notApplicable` on it).
  `Schemes/ℚ` is read in ascription position the way `QQ-Mod` is: the term
  grammar sees a name over a domain, which has no other meaning there, so it
  names the registered category when there is one. The category's name is
  spelled in ASCII (`Schemes/QQ`) because a Lean name may not carry `ℚ`, and
  `renderName` puts the mathematician's spelling back.
- **`kernel(d/dx : ℚ[x] → ℚ[x])` is ℚ**, and the ARROW is ascribed rather
  than inferred because a derivation names no domains of its own. The kernel
  of `d/dx` is the constants exactly where the integers are invertible in the
  coefficient ring, so ℚ, ℝ and ℂ answer and everything else REFUSES rather
  than being given a ring this slice has not checked (over `ℤ/p` the p-th
  powers are killed too).
- **`dx` and `Spec` are real TOKENS, and both had to be.** `dx` keys a
  TRAILING production and `Spec` a leading one; Lean indexes both kinds by a
  token, and a non-reserved `&"dx"` is not one — the production is then never
  tried, which is the same lore the `span_QQ{…}` note records. The
  `ident`-plus-name-check trick that saves `span_QQ` does not save `Spec`
  either: that production has no closing delimiter, so it OUT-RUNS the bare
  name wherever an identifier is followed by an atom (`|z|` reads its closing
  bar as the start of a factor), and Lean's longest match prefers the
  alternative that got furthest even when it failed. The price is that `dx`
  and `Spec` are reserved words in this surface.
- **`kernel(… : …)` is folded into the CALL production** for that same
  reason: a separate parser starting where a call starts fails at the `)` of
  `f(2)`, which is further than the bare name that succeeded three tokens
  earlier, so every call in the corpus would stop parsing. The optional
  ascription tail keeps `:` confined to this one spelling, and which NAME may
  carry it is checked in `toExpr`.
- **A bound polynomial brings its indeterminate into scope across an
  assertion**, under the name this slice RENDERS it with (`x`).
  `SPEC.md` writes `assert d(f) = (6x + 1) dx` and `assert F(x) = x³ + …`,
  naming `x` on the side that is not the polynomial, and a `let f := x ↦ …`
  binding records no binder — a `Value.poly`'s indeterminate is anonymous and
  prints as `x`. Consulted after `calledBinder?` and after the session
  bindings, scoped to ONE assertion, publishing nothing: a bare `x` elsewhere
  is still the loud "not bound" error. Same disclosed residue
  `calledBinder?` carries — inside such an assertion a typo `x` reads as the
  indeterminate, and the outcome is an honest `unknown` or a false assertion,
  never a wrong answer.

## Symbolic function expressions (`SPEC.md` §Elementary calculus, issue #24)

`sin(t)`, `e^t` and `1/t` leave the polynomial engine, and `SPEC.md` asks
exactly three things of them: a limit, a definite integral and a Taylor
expansion. All three are computed by a backend FROM THE EXPRESSION, so what
this surface owes them is a presentation of the expression and nothing more.
`Value.sym` carries a first-order `SymExpr`; `Eval.toSymExpr` is the only way
into it.

- **The vocabulary is a CLOSED LIST** — the binder, exact rationals, the
  constants `e`/`pi`/`infinity`, the functions `sin`/`exp`, and `+ - * / ^`.
  A name outside it is a loud refusal that LISTS the list, at the surface and
  again at the wire codec in both directions. That closure is what keeps the
  surface backend-blind: an unknown symbol is never handed to a backend to
  read however it likes, and the adapter receives a typed TREE rather than
  source it has to parse (decision 2).
- **A symbolic body DECIDES NOTHING.** It has no domain (`valueDom?` gives it
  none, the slot a factorization and a cardinal already occupy), no
  arithmetic (`Native.noArithmetic` words that refusal beside the
  approximation's, for the same reason — there is nothing here that would not
  be invented), and no value at a point: `sine(0)` is a loud refusal naming
  the body, because a decimal for `sin(0)` is an APPROXIMATION and that is a
  separate operation on an exact element. Two symbolic bodies are
  INCOMPARABLE rather than unequal — `1/t` and `t^(-1)` are one function and
  two trees, so `false` would be a claim this slice cannot make.
- **TWO readings, in a fixed order with a stated reason.** A `↦` binding tries
  the POLYNOMIAL reading first and keeps it wherever it applies, because that
  is the reading that decides (`h(-t) = h(t)`, `(f ∘ g)(t) = t⁶`, and equality
  of two bodies). Only a body it cannot express is read symbolically. This is
  an ordering, not a fallback: a body NEITHER reading reaches is the symbolic
  reader's refusal, which is the wider of the two.
- **A bound name is REFUSED inside a symbolic body**, never substituted and
  never read as the constant it shadows. There is nothing to substitute into
  — a symbolic body is not evaluated — and reading a bound name as a constant
  would turn `let e := 5` followed by `t ↦ e^t` into Euler's number, a wrong
  answer where the refusal is only an inconvenience.
- **DISCLOSED COLLISION, and it is `SPEC.md`'s own.** `SPEC.md` binds `e` to
  the doubling map in §Set comprehensions and writes `e^t` for Euler's number
  in §Elementary calculus. A binding wins over a constant — the rule `i` and
  `R` already follow — so in a session that has read `SPEC.md` top to bottom,
  `e^t` reads the shadowed name and refuses. Both halves are pinned side by
  side (`CasDslTests/Eval.lean` and `tests/test_e2e.py` order their cells so
  that each is exercised), and `exp(t)` is the spelling no binding can
  shadow. The notebook is a single session that binds `e` in §8, so its
  calculus section shows the collision as a live refusal.
- `∞` is a TOKEN because it is not an identifier character; `π` and `e` are,
  so those two are ordinary constants consulted after the bindings. All three
  denote the same kind of thing — a symbolic constant with no domain.

## Sets (`SPEC.md` §Finite sets, issue #24)

The set operations SPEC.md writes — `∪ ∩ \ △ × 𝒫 |·| ⊆ ∈` — are all
category-owned methods on `Sets`, reached by the ordinary resolver and
router, except the two that construct rather than compute.

- **`A × B` and `𝒫(A)` are PRESENTATIONS, not element lists.** Their
  elements are pairs and sets, and `Value` presents neither; a `SetPresentation`
  constructor is therefore the only honest way to denote them, exactly as
  `arithProg` denotes `{0, 2, 4, …}`. They are built by elaboration like a set
  literal — no method, no route — and the consequences are stated rather
  than hidden: `|A × B|` and `|𝒫(A)|` are exact cardinal arithmetic
  (`Native.presCard`), while everything that would need an element list
  (`nth`, `contains` on a product, set equality, the binary operations)
  fails loudly. `𝒫` of a countably infinite set is UNCOUNTABLE, which
  `Cardinality` deliberately cannot state, so `|𝒫(ℕ)|` reports that it
  cannot be stated — never `ℵ₀`. A FINITE powerset has the other ceiling:
  `powersetExpCap` (2^4096) is where `2^n` stops being a number worth
  materializing, and `|𝒫(ℤ/5000)|` says so rather than hanging.
- **`ℂ - ℚ` is DENOTED, and it is not a second spelling of `\`.** SPEC.md
  writes both: `A \ B` (§Finite sets) computes an element list and is the
  `diff` method, routed for explicit finite receivers; `ℂ - ℚ` (§Polynomials)
  is a `SetPresentation.domainDiff` built by elaboration, like `A × B` and
  `𝒫(A)`. Only two DOMAINS build one — the minus between two finite sets is
  the ordinary arithmetic error it always was — and the presentation claims
  exactly what the assertion needs: MEMBERSHIP, decided pointwise by the two
  domains' own tests (so `x ∈ ℂ - ℚ` and `S ⊆ ℂ - ℚ` for an explicit finite
  `S` are decided), while a cardinality, a canonical form to compare, an
  enumeration and an inclusion with a non-finite left side all refuse.
- **`|·|` names a method and `⊆` is `subset`**; the bars and the symbol are
  spellings, not operations of their own. Which method the bars name is the
  receiver's business — `cardinality` for a set, `abs` for an element of ℝ or
  ℂ (§Exact number systems) — so `|3|` is still the ordinary "not a method of
  any category this object belongs to" error rather than a third notion of
  size.
  Likewise `X ∈ 𝒫(A)` and `X ⊆ A` are ONE decision procedure with two
  spellings: `contains` on a powerset receiver is the inclusion judgment.
- **`let A := {1,2,3} in 𝒫(ℤ)` is set membership**, and both SPEC.md
  spellings of the ascription (`𝒫(ℤ)`, `2^ℤ`) build the same presentation —
  `2^X` is read as the powerset only when the base is the literal `2` and the
  exponent is a set. An ascription naming a SET is checked through the same
  routed `contains` the surface's `∈` uses, so the ascription cannot decide
  membership differently from the assertion.
- **Only explicit finite receivers are routed for `∪ ∩ \ △`.** The operations
  are declared on `Sets`, where they are meaningful for every presentation;
  the native routes accept `finiteSet`, so `ℤ ∪ A` resolves and then reports
  the structured gap. Mixing ELEMENT domains inside one operation is refused
  rather than joined: the pure native backend cannot read the preferred-
  canonical-map registry the surface joins literals with.
- **Domain inclusion is the canonical-map registry's claim, and the registry
  answers it.** `ℕ ⊆ ℤ` is still refused by the SET layer — §Coercions owns
  which domains include which, and answering it twice would be two places to
  get it wrong — but the surface no longer stops there: `D ⊆ E` between two
  domains is decided by `Eval.domainSubset` against the registry, by
  elaboration, exactly as `A × B` and `𝒫(A)` are built there. One owner, one
  answer, and `Native.run "subset"` on two domains keeps saying so.
  Inclusion of SETS answers `false` without a decision procedure only where
  the normal forms make it a theorem (a countably infinite domain or an
  unbounded progression is not inside a finite list).
- **A finite cardinal answers to the integer counting it** (`|A| = 3`), ℵ₀
  answers to no integer, and `2^|A|` exponentiates by a finite cardinal —
  which is what makes `|𝒫(A)| = 2^|A|` a computed identity. `2^ℵ₀` has no
  exponent here and says so.

## Comprehensions and images (`SPEC.md` §Set comprehensions, issue #24)

`{x ∈ X | P(x)}` and `{f(x) | x ∈ X, P(x)}` are ONE node
(`CasExpr.comprehension`): the filtering spelling is the image of the
identity, so one evaluator decides both. What it may decide is deliberately
narrow, and everything outside it is refused at the binding rather than
approximated — the move §Functions already makes for `t ↦ sin(t)`.

- **A guarded comprehension is DECIDED, never sampled.** Each comparison in
  the guard is rewritten as `p(n) ⋈ 0` (both sides evaluated with the binder
  as the indeterminate, then subtracted), and a Cauchy-style bound
  `N = max(1, ⌈(S+1)/|a_d|⌉)` with `S = Σ_{i<d}|a_i|` puts every root of `p`
  inside `±N`. `p` therefore keeps one sign on each tail, so evaluating it at
  `±N` decides whether that tail satisfies the guard: if it does, the
  comprehension is INFINITE and says so; if it does not, every solution lies
  in the bound and each candidate is tested exactly. A conjunction (the chain
  `0 ≤ n < 6`) intersects the two conjuncts' bounds, which is what makes a
  guard bounded by neither conjunct alone decidable. A guard that does not
  mention the binder at all is a CONSTANT — including `0*n` and `n - n`,
  which reduce to the zero polynomial — and answers with the whole index set
  (refused as infinite) or the empty one (decided), never with a complaint
  about an unextractable bound. There is no enumeration cutoff: the candidate
  count past `comprehensionCap` is a loud failure. And the bounds are read
  with the binder as an INDETERMINATE, where a guard that is meaningless for
  elements can still answer — `n.deg()` is 1 for the indeterminate and a
  resolver error for an integer — so a verdict is never shipped without one
  element-world reading behind it: every enumerated candidate re-reads the
  guard as an element, and the three paths that enumerate NOTHING (the empty
  range, the infinite refusal, and an unguarded comprehension's one-shot head
  presentation) probe once before they are trusted. A guard whose
  element-world reading errors — or a head that produces no value there —
  gets the undecidable refusal, the same one an unreadable guard shape gets. Its practical reach is
  smaller than that number suggests over ℤ, because the tail bound is
  symmetric about the origin: an offset window costs ~2×|offset| candidates,
  so |offset| ≲ 50000 is the real ceiling there. Over ℕ the lower bound is 0
  and a window costs |offset| + width.
- **An unguarded comprehension is presented only when its image IS a
  presentation the slice has.** `{2n | n ∈ ℕ}` is the arithmetic progression
  `{0, 2, 4, …}` — SPEC.md's own identity (`Y = {2n | n in ℕ}`) — so its
  membership is the progression's exact solve (`8 ∈ E` and `9 ∉ E` are
  decided, and `10¹² ∈ E` costs nothing), its cardinality is ℵ₀, and its
  equality with the literal is presentation normalization. A non-linear image
  or an index that is not ℕ is a structured gap.
- **The index set is ℕ or ℤ.** Filtering an arbitrary finite set is not
  implemented (nothing in `SPEC.md` §Set comprehensions needs it), and says
  so rather than half-working.
- **The binder is a real local binding scoped to the braces**
  (`EvalCtx.local?`): consulted BEFORE the session bindings, so it shadows a
  `let n := …` INSIDE the comprehension and leaves it untouched outside, and
  it publishes nothing — a bare binder name elsewhere is still the loud "not
  bound" error. This is ordinary scoping and does not widen the name
  resolution §Functions narrowed.
- **Two `SPEC.md` §Ellipses lines stay uncovered, and they fail
  DIFFERENTLY.** `{n in ℕ | f(n) ∈ 2ℕ}` does not parse at all: `∈` is an
  assertion relation, not a term operator, so the guard position rejects it
  and the statement splitter runs what is left as fragments — `2` and `ℕ`
  print as results next to the parse error. That reading is the splitter's,
  not this surface's — a decided answer to a DIFFERENT claim, which is why
  the line is listed here rather than trusted. `2ℕ` no longer compounds it:
  there is still NO scaling production, but implicit multiplication takes an
  ATOM since #26 (§Surface), so `2ℕ` is the PRODUCT `2 · ℕ` and refuses
  loudly — `ℕ` is not an element value. It used to split into two statements
  and quietly assert `Y = 2` while displaying `ℕ` beside it, which is a
  decided answer to a claim nobody made; the refusal is strictly better and
  is pinned in `tests/test_e2e.py`.
  `{n in ℕ | n.is_prime()}` is the other kind: it parses, and gets the
  structured undecidable-guard refusal AT THE BINDING, even though
  `n.is_prime()` itself ships as a method — primality is not a polynomial
  comparison. All of it is on the `SPEC.md` ledger (#24), none of it is a
  silent approximation.
- **`e.image()` is the one method functions own** (`FunctionElems`,
  registered because what a map does to a whole set is a computability
  question), and `e(ℕ)` — applying a function to its SOURCE — desugars to it,
  so there is one implementation and two spellings. Applying a function to
  any other set is refused. The image of a linear map on ℕ is returned as
  `Value.progV`, the second shape an executor may return as a set: like
  `setV` it is reflected by `Denote.ofValue` into the ordinary
  `SetPresentation`, so `e.image()`, `e(ℕ)`, `{2n | n ∈ ℕ}` and
  `{0, 2, 4, …}` are all the same set object.

## Vectors, matrices and subspaces (`SPEC.md` §Vectors and matrices,
§Subspaces and spans, issue #24)

**A vector is not a matrix.** `Domain.matrix` is SQUARE by construction, so a
column of length `n` is not an `n × n` object and reusing it would make every
shape check a lie. `Domain.vector`/`Value.vec` are their own constructors and
the LENGTH is what they carry: `Mat₂(ℚ)` applied to a vector of ℚ³ is a loud
refusal naming both shapes, which is the whole return on keeping them apart.
`ℚ²` is SPEC.md's superscript spelling and the one `Domain.render` produces,
so a vector domain reads back as it displays; the LaTeX form of a vector is
the TUPLE, because that is what the surface writes and a column `pmatrix`
would typeset something the input syntax does not say. Equality is by length
and components, and the entry domain is a presentation tag that does not
decide — `(1, 2)` of ℤ² and of ℚ² are one vector, as `1` and `1/1` are one
number.

**The action joins `Common`.** A matrix and a vector are the one operand pair
that is not two elements of a shared kind — a matrix ACTS — so the pair is a
`Common` constructor rather than a layer in front of `promote`, and every
operation must STATE what it does with it: multiplication applies, addition
and subtraction say that a matrix acts rather than combines, division points
at the inverse, `scalarCmp` refuses in an arm of its own, and
`hasScalarArithmetic` answers false so no fold reports a seed. `Native.matApply`
CHECKS the shape, and REFUSES to join two entry domains for the reason the
binary set operations refuse: the canonical-map registry is not readable from
that backend. Both refusals name the fix, and SPEC.md ascribes both operands.
SPEC.md's four spellings of the action — `M*v`, `M v`, `M⁻¹ b`, `M(M⁻¹ b)` —
are one operation: `⁻¹` is the `inverse` METHOD's spelling and juxtaposition
is the product (§Surface).

**A subspace is a SET, presented by a REDUCED basis.** SPEC.md asks a
subobject for `dim`, `∈`, `∉` and `=`, and `M.ker() = {0}` for a fifth, so it
does NOT join the domainless-result family: its elements are vectors, which
`Value.vec` presents, and `∈ = ⊆ |·|` reach it through the ordinary `Sets`
hierarchy. One normalization answers all of it — the basis is kept in reduced
row echelon form, which is a FUNCTION of the subspace and of nothing else:

- `dim` is the basis SIZE, so a dependent generator contributes nothing;
- membership is one SOLVED reduction of the candidate against the basis (each
  row has a leading 1 in a pivot column no other row touches, so the only
  combination that could work is the one read off those columns), which is
  what makes `(1, 1, 0) ∉ W` DECIDE false rather than refuse;
- equality is the bases compared as data, and inclusion is membership of each
  basis vector. No search, no double inclusion, no cutoff.

`Value.mkSpanBasis` is the ONE constructor, the discipline `mkAlg` has: the
surface's `span_QQ{…}`, `M.ker()` and a decoded frame all go through it, which
is what makes two spans of one subspace compare equal. The reduction is exact
`Rat` arithmetic and lives in `Value.lean` beside `mkAlg` because it is a
presentation's NORMAL FORM rather than a computation a backend owns.

- **CEILING: over ℚ**, which is `span_QQ`'s own base and the entry domain of
  every matrix this slice routes. A generator this slice cannot read as a
  rational vector is a loud refusal — `√2·u` lies in the ℝ-span, not the
  ℚ-one, and either answer would be a claim.
- **`M.ker() = {0}` is decided**, and the reading is stated once, in one
  place: a span is finite exactly when it is TRIVIAL, and the scalar `0` on
  the other side is the mathematician's own spelling of the zero of the
  ambient space — the one element every additive group shares.
  `Value.isSpanZero` is where that crosses, and a scalar is the only thing
  that crosses: every other scalar is not an element of ℚⁿ and answers false.
- **The AMBIENT is part of the presentation and of the display**
  (`span_ℚ{…} ≤ ℚ³`): without it the trivial subspace would render as an
  empty brace saying nothing about which space it is the zero of. It is also
  why a span literal needs a generator — the ambient is read off them, so the
  trivial subspace is written with the zero vector of the space meant.
- **`≤` is the SUBOBJECT ascription** between a subspace and its ambient, and
  the ambient is CHECKED. Which reading `≤` has is the operands' business,
  exactly as the receiver decides which method `|·|` names and two domains
  decide that `-` denotes a difference. SPEC.md's `\leq` is a second spelling
  of the same relation.
- **`QQ-Mod` is an ASCRIPTION TAG at this stage**, registered under the name
  SPEC.md spells and owning `dim` alone. The membership it states is real and
  checked, but the CATEGORY — its morphisms, its limits, the subobject
  lattice `≤` really lives in — is deferred to CategoryGraph per the
  trajectory ruling. Nothing here may grow into that ontology. A subspace
  inhabits `CountableSets` and `QQ-Mod` INDEPENDENTLY, exactly as a
  polynomial inhabits the divisibility and structural hierarchies.
- **`rank` and `ker` are NATIVE**, because both are reads of the same echelon
  form the presentation already owns — the rank is its row count, the kernel
  its free columns. No backend is asked and none can lie. Routed for ℚ
  entries only, so Mat₂(ℤ/5) carries the gap `det` already carries.
- **`trace` is native too** and defined over every entry domain (it reads the
  diagonal), so Mat₂(ℤ/5) HAS a trace where its `det` gaps: the two judgments,
  visible in one object. `charpoly` and `companion_matrix` are the backend's,
  with the reply checked against this call's receiver (§The port).
- DISCLOSED GAP: SPEC.md's `φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c` and the
  `W = ker φ` that reads it. Functions here are grounded in the UNIVARIATE
  polynomial engine (§Functions), so a body in three variables is not
  expressible; the multi-binder lambda is refused where it is written, in
  words that name it as a gap rather than a syntax error. Nothing else in
  that SPEC.md section needs it.
- DISCLOSED, and not closed here: `elemsDomain` seeds a set literal's element
  domain with ℤ, so `{u₁, u₂}` — a set literal of VECTORS — has no common
  domain and is refused. `span_QQ{…}` does not go through it, so no SPEC.md
  line is affected, and a set of vectors has no shipped operation to be
  useful for yet.

## Aggregation (`SPEC.md` §A composed computation, issue #24)

`∑_{x ∈ X} body` and `∏` are ordinary category methods with a surface
spelling: `sum` and `prod`, declared on FINITE sets and folded natively.

`FiniteSets` rather than `Sets` is where they first make sense — aggregation
is a finite algebraic operation, and the sum over an infinite set is a limit
this slice has no notion of, so `∑_{n ∈ ℕ} n` is honestly not a method of ℕ
rather than a missing route. Residue: a BOUNDED progression is finite but
presents as `progression`, which enters at CountableSets because a pattern
cannot see the bound, so it misses this specificity as it misses FiniteSets.

Three decisions, each pinned: a SET counts each element once however the
literal was written; the empty sum is 0 and the empty product is 1, which are
the mathematical answers; and elements with no scalar arithmetic are a
REFUSAL naming the value, never the seed — the guard is
`Native.hasScalarArithmetic`, the predicate the power path already asks,
rather than a second derivation of it. A body other than the binder
aggregates the IMAGE, built by elaboration as a set literal is; the body binds
TIGHTLY, so `= 0` on the right of an assertion ends the sum where the
mathematician wrote it.

## The root set (`SPEC.md` §A composed computation, issue #24)

`{x ∈ D | p(x) = q(x)}` is the set of SOLUTIONS in `D` — a production of its
own, and the deliberate special form SPEC.md's `{a ∈ ℂ | r(a) = 0}` needs.

It is NOT the guarded comprehension's decision procedure: that one bounds a
binder over ℕ or ℤ from a polynomial COMPARISON and tests candidates
(§Comprehensions and images). Solving an equation is a different operation,
and one the surface already has — the equation is read with the binder as the
INDETERMINATE, moved to `p − q`, presented in `D[x]`, and handed to `roots`.
Same method, same route, same backend, one implementation.

`=` gains no term-level meaning by this: it appears inside this production and
nowhere else in a term, so the guarded comprehension is untouched and still
takes an order comparison. The INDEX DOMAIN decides where the roots are
sought, which is the mathematics rather than a default — `{a ∈ ℚ | r(a) = 0}`
is `{1}` and `{a ∈ ℂ | r(a) = 0}` has three elements — and it leaves the open
question about `roots`' default ring untouched, because this spelling names
the ring explicitly.

Two things it rests on: calling a polynomial at a POLYNOMIAL substitutes (the
move `f ∘ g` already makes), and a domain whose SIZE this slice cannot state
still normalizes for COMPARISON, so `S ⊆ ℂ` and `S ∈ 𝒫(ℂ)` are decided from
the elements and `ℝ = ℝ` answers true. Those two questions used to be tied
together by one normal form; the refusal that belongs to the cardinality
(`ℂ.cardinality()`) is unchanged.

## Categories (`Category.lean`, `Registry.lean`)

```lean
inductive ParamVal | dom (d : Domain) | nat (n : Nat)

structure CatRef where
  name   : Name              -- inheritance graph node
  params : Array ParamVal    -- instantiation data, preserved along edges
```

- The **inheritance graph** is on category *names*: a `CatDecl` registers
  `parents : Array Name`; params pass through unchanged along an edge
  (`SmallModules(ℤ) ≤ Modules(ℤ)` because `SmallModules ≤ Modules`).
- An object's **profile** is the set of `CatRef`s it directly inhabits
  (computed by `Std.profileOf : Obj → Array CatRef`); the resolver closes
  over parent edges. Profiles are rich: `ℤ` enters with sets, countable
  sets, commutative rings, euclidean domains, … — never one weakest class.
- **Method declarations** are category-owned:

```lean
structure MethodDecl where
  id        : Name           -- stable mathematical identity, e.g. `factor
  receiver  : Name           -- receiver category NAME (any params)
  argDoc    : String         -- slice keeps arg validation at execution
  resultDoc : String
  doc       : String
```

  No method declaration names a backend, algorithm, or capability limit.

- **Routes** live in a *separate* registry (the computability layer):

```lean
structure Route where
  method   : Name
  pattern  : PresPattern     -- first-order matcher on the receiver Obj
  backend  : Name            -- `native or `sage (executor looked up by name)
  opId     : String          -- backend operation identity
  priority : Nat             -- deterministic tie-break: highest wins, tie = error
```

- **Functors** are the transport layer, and are registry data too:

```lean
structure FunctorDecl where
  name   : Name
  source : Name              -- category NAME, never a backend
  target : Name
  objMap : ObjMap            -- first-order object map (no closures)
  doc    : String
```

- **Preferred canonical maps** are the coercion layer, and registry data too:

```lean
structure CanonicalMap where
  src : DomainPattern           -- patterns on BOTH sides, so ℤ → ℤ/n is ONE rule
  tgt : DomainPattern
  op  : CanonOp                 -- first-order value transform (no closures)
  doc : String
```

- **Bindings** (`let` results) are an env-extension map `Name → Obj`.
  Every registry is a `SimplePersistentEnvExtension`: cell atomicity,
  restart replay, and the olean session cache come for free from the
  plugin state law. No semantic state in `IO.Ref`s, ever.

## The resolver (`Resolve.lean`) — the one boundary

```lean
structure Resolution where
  decl : MethodDecl
  profileEntry : CatRef      -- instantiated receiver category
  via  : List Name           -- inheritance chain from a profile entry (possibly [])
  viaFunctor : Option FunctorStep   -- set when the RECEIVER was transported

resolveMethod (env : Environment) (o : Obj) (m : Name)
    : Except ResolveError Resolution
```

**Round one — method transport along inclusions.** Direct lookup on profile
entries, then upward closure through registered parent edges (BFS,
deduplicating diamond paths). Two *distinct* applicable declarations from
incomparable categories = `ambiguous` error. Method not declared on any
reachable category = `notApplicable`, and the error names the categories
where the method IS declared.

**Round two — receiver transport along functors.** `X.m()` where `m` is
declared on `D` and a registered `F : C → D` applies to `X` resolves as
`F(X).m()`, recorded in `viaFunctor`. Rules, all load-bearing:

- round one runs first and wins unconditionally, so registering a functor
  can never take a method away from an object that already had it;
- only `notApplicable` opens round two; a functor applies when the
  receiver's profile reaches its `source` and its object map is defined on
  the presentation;
- the image's profile must reach the functor's declared `target`, or the
  REGISTRATION is defective: `functorTargetMismatch`, and resolution stops
  rather than working around it;
- exactly one transported candidate resolves; several competing functors are
  the ordinary `ambiguous` error carrying all of them (never an order
  heuristic), and none leaves the original `notApplicable` unchanged.

Every caller routes and executes against `res.concreteReceiver o` — the
transported image, not the object it passed in. Nothing else — no method
declaration, no backend contract — may assume the resolver does only
direct/inherited lookup.

Ceilings of round two (deliberate): **one hop** (the image is resolved by
round one only — no functor composition, no path search, no preferred-path
registry); **no result lifting** (the image's result is the answer; no
shipped transported method needs a value carried back along `F`); and the
`ObjMap` ceiling — an object map that is not expressible adds a constructor,
exactly as `DomainPattern` does.

## Coercions (`Eval.lean` + the canonical-map registry)

`map e to D` means: **apply the preferred canonical map into `D` when one
exists, and fail otherwise** (design review 2026-07-30). Canonical maps are
preferred choices, not necessarily injections — a monomorphism in some
category (`ℤ ⊆ ℚ`), a universal-property-supplied map (the quotient
`ℤ → ℤ/n`; cokernels, when they arrive), and, behind this same lookup, a
later round may let transport along a preferred functor supply one.

Every coercion the surface inserts — `map e to D`, a mixed-domain join, the
element promotion of a set or matrix literal, a domain ascription — goes
through `coerceValue`/`domJoin`, and the BASE CASE (one scalar domain into
another) is decided by the registered `CanonicalMap`s. The prelude registers
`ℕ ⊆ ℤ`, `ℕ ⊆ ℚ`, `ℤ ⊆ ℚ`, the quotient `ℤ → ℤ/n`, and SPEC.md's number-system
chain `ℚ ⊆ ℝ ⊆ ℂ` with the ℕ/ℤ links; `ℤ ⊆ ℚ` in the surface is sugar for the
registered map (decision 6). No engine module knows those particular facts:
unregister a rule and the corresponding `map` stops working, with the honest
"there is no preferred canonical map of … into …" error.

The chain is registered as the TRANSITIVE CLOSURE — ℕ/ℤ/ℚ → ℝ, ℕ/ℤ/ℚ/ℝ → ℂ —
for the reason `ℕ ⊆ ℚ` is registered next to `ℕ ⊆ ℤ` and `ℤ ⊆ ℚ`: a coercion
applies ONE rule and rules do not compose, so the closure is what makes both
`assert ℚ ⊆ ℝ` and `map p to ℂ[x]` (the ℤ → ℂ image, coefficient-wise) work.
Every link is `CanonOp.identity`: a value this slice can present is carried by
the same `Value` in all of them, so the inclusion moves no data.

**`D ⊆ E` is that same registry, read as a judgment** (`Eval.domainSubset`,
SPEC.md's `assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ`): it means *the preferred
canonical map of `D` into `E` exists and is an INCLUSION*, and it recurses
exactly as `coerceValue` does (congruence under `poly`/`matrix`, a scalar as
its own constant polynomial, reflexivity), bottoming out in the rules.
`CanonOp.isInclusion` is where each transform states whether it is one — the
quotient `ℤ → ℤ/n` is the one that is not, which is what makes `ℤ ⊆ ℤ/5`
FALSE rather than true-because-a-map-exists. An unregistered pair is false by
the same definition: no preferred map is exactly the absence of the
identification the symbol asserts.

A visible consequence, decided rather than inherited: **`let r := 3 in ℝ` now
succeeds**, binding `3 ∈ ℝ`. Registering ℤ → ℂ is forced by `map p to ℂ[x]`,
and a registry that carried ℤ → ℂ but not ℤ → ℝ would contradict the very
chain SPEC.md asserts.

Exactly one applicable rule coerces. Zero is that honest error. MORE than one
— or two rules mapping two domains into each other, which leaves a join
with no preferred answer — is a defective registration, reported loudly with
both rules named. A coercion is never chosen by registration order, array
position, or invented specificity: the same discipline as the resolver's
`ambiguous` and the router's tied routes.

Four cases stay ENGINE-LEVEL because they are not canonical injections
between two domains and so cannot be registry data:

- **structural congruence** under `poly`/`matrix`, plus a scalar as a constant
  polynomial: a canonical map of coefficient/entry domains *induces* the one on
  polynomials and matrices, so a registered `ℤ[x] → ℚ[x]` would be a second
  place to state `ℤ ⊆ ℚ`. The recursion bottoms out in the registry;
- **identity**, when the value already presents the target domain;
- **`ℕ ← ℤ`**, a partial CHECK (a membership judgment, "is this integer in
  ℕ?"), not an injection — a registry of canonical injections must not be
  able to state it;
- **`ℤ/m` vs `ℤ/n`**, where the fact reported is the ABSENCE of a canonical
  map between different rings.

Two neighbouring mechanisms are deliberately NOT canonical maps. `Native.lean`'s
internal scalar promotion (`toRat?`/`promote` inside the executors) is the
trusted computation layer's own implementation detail — the analogue of
Sage's internal coercions — and stays code-level: it decides how an executor
computes `1 + 1/2`, never which domains the surface may move a value between.
And reading a literal in an ambient domain (`assert 2 + 3 = 0 in ℤ/5`) is
literal interpretation, not a map applied to an existing value.

## Routing and gaps (`Route.lean`)

`routeFor` filters routes by method id + pattern match on the concrete
receiver, then selects deterministically by priority. Failure produces the
structured gap the plans demand:

```lean
structure CapabilityGap where
  method : Name
  receiverCategory : CatRef
  presentation : String        -- rendered Obj presentation
  semanticVia : List Name      -- how the method was semantically available
  routesConsidered : Array Route
```

Gap rendering is a first-class output (text + JSON MIME), an auditable
developer backlog item — never a parse/type/category error.

**Op signatures (design review 2026-07-30).** The DSL surface can never
produce a wrong-shaped call — but the agreement between a route's pattern
("which objects") and its op ("which implementation") used to be a
convention, caught only by defensive arms in the executors. It is now a
checked invariant: each backend registers, per `opId`, the receiver
patterns that op accepts (`OpSig`, ordinary registry data declared by the
backend's own Lean half next to its encoders), and `addRouteChecked`
rejects any route naming an undeclared op or carrying a pattern the op's
signature does not accept (`PresPattern.implies`, the syntactic subsumption
order). A mismatched or typo'd route therefore fails `lake build`. The
executors' residual shape arms collapse to one shared diagnostic that can
only fire if a signature *declaration* misstates its encoder. Shapes only:
partiality within an accepted shape (out-of-range index, no membership
test for a domain) stays a loud runtime error.

## The port (`Port.lean`) and the Sage adapter

Generic framed child-process port, mirroring the worker's discipline:

- frame = ASCII byte length, `\n`, UTF-8 JSON, over the child's
  stdin/stdout (stderr is a log stream, never framed);
- on start the adapter emits
  `{"op":"ready","protocol":1,"backend":"sage","backend_version":…,
  "adapter_version":…,"capabilities":[opIds]}`;
- requests carry `request_id`; replies echo it;
  unknown op → `{"status":"unsupported"}`;
- the connection handle is a non-semantic process cache in an `IO.Ref`
  (like the worker's output sink: wiring, not state). Replays re-execute
  backend calls.

Typed values on the wire (bignums as strings):
`{"t":"int","v":"360"}`, `{"t":"rat","num":"1","den":"2"}`,
`{"t":"poly","coeffs":[rat…]}`, `{"t":"mat","rows":[[rat…]…]}`,
`{"t":"factorization","unit":…,"factors":[[value,mult]…]}`,
`{"t":"set","elems":[value…],"dom":domain}`,
`{"t":"alg","a":rat,"b":rat,"d":"5"}` (the exact `a + b√d`, decoded THROUGH
`Value.mkAlg` so a frame carrying `√8` becomes the `2√2` it denotes),
`{"t":"approx","exact":value,"decimal":"1.4142135623","eps":rat,
"achieved":rat}` (decoded THROUGH `Value.mkApprox`, which VERIFIES the
certificate: a decimal that does not present its own exact value within the
bound never becomes a value — §Numerical approximation),
`{"t":"vec","n":2,"entry":domain,"comps":[value…]}` (a frame whose component
count contradicts its declared LENGTH is refused, as a matrix that is not
n×n is), `{"t":"span","n":3,"basis":[value…]}` (decoded THROUGH
`Value.mkSpan`, which REDUCES: a frame carrying a dependent or unreduced
generating set becomes the basis it denotes — §Vectors, matrices and
subspaces).

Sage ops: `factor_int`, `factor_poly_q`, `factor_poly_z`, `factor_poly_c`,
`gcd_int`, `is_prime_int`, `roots_poly_z`, `roots_poly_q`, `roots_poly_c`,
`mat_det_q`, `mat_inv_q`, `mat_charpoly_q`, `poly_companion_q`,
`approx_real`. The last two are CHECKED against this call's receiver, the
discipline `approx_real` set: a characteristic polynomial must be monic of
the matrix's own degree, and a companion matrix must have the polynomial's
degree, its TRACE (the sum of the roots) and its DETERMINANT (their product).
That is deliberately not a positional read of the companion's entries: which
of the four LAYOUTS the adapter uses is its own convention (decision 7), and
similar matrices share both numbers, so the check holds the backend to the
mathematics without this side taking a position on a convention that is not
its own. BOTH numbers, because neither alone is enough — the zero matrix has
the right trace whenever `a_{d−1}` is 0, which SPEC.md's own cubic is.
`Value.detQ` is the determinant that check needs: the elimination `rref`
already runs, keeping the scale `rref` normalizes away.
The two ℂ ops work in `QQbar`, whose elements PRINT
as decimal approximations — so the adapter never reads a printed form: it
takes the coefficients of an algebraic number from its own minimal polynomial
and settles which conjugate it is by an exact `QQbar` comparison. A root of
degree > 2 over ℚ leaves the `a + b√d` presentation and is the loud
`not_expressible` refusal, never a decimal.
The adapter (`backends/sage_adapter.py`) runs under `sage -python`, builds
native Sage parents/elements from the typed request, and returns trusted
typed results with provenance versions. It never receives generated Sage
source and never proxies another CAS. Adapter discovery: env
`CASDSL_SAGE` (default `sage`) and `CASDSL_ADAPTER` (default
`backends/sage_adapter.py` relative to the worker cwd = the project dir).

## Surface (`Syntax.lean`)

Backend-blind; a `casTerm` syntax category plus commands:

```text
let n := 360 in ℤ                         -- binding with domain ascription
let p(x) := x^3 - 2x + 1 in ℤ[x]          -- univariate polynomial binding
let q := map p to ℚ[x]                    -- explicit coercion along ℤ ⊆ ℚ
let X := {0, 1, 2, ...}                   -- progression set literals
let M := [1, 2; 3, 4] in Mat₂(ℚ)          -- matrix literal
let v := (1, 2) in ℚ²                     -- vector literal, and the Eⁿ domain
M*v   M v   M⁻¹ b   M(M⁻¹ b)              -- the action, in SPEC.md's spellings
M.rank()   M.ker()   M.trace()   M.charpoly()   r.companion_matrix()
let W := span_QQ{u₁, u₂} \leq ℚ³ in QQ-Mod  -- the subobject ascription
W.dim()   (1, 1, 2) ∈ W                   -- a subspace is a set with a dim
∑_{a ∈ roots} a    ∏_{a ∈ roots} a        -- aggregation over a finite set
{a ∈ ℂ | r(a) = 0}                        -- the root set of an equation
let z := 2 + 2i in ℂ                      -- exact algebraic value; `i` is a constant
map √2 to ℝ/O(1/10^{10})                  -- a requested tolerance, not a quotient
√2   2√2   z.re()  z.im()  z.bar()  |z|   -- one square root over ℚ, exactly
let h := t ↦ t² + 1 in ℝ → ℝ              -- function, lambda spelling
let f(t) = t^2 in RR->RR                  -- …and the f(t) spelling, ASCII
let e: ℕ → ℕ := n ↦ 2n                    -- leading-ascription spelling
n.factor()   M.det()   M.inverse()  F.annihilator()   X.cardinality()
p.deg()   p.roots()   a.gcd(30)            -- polynomial and UFD methods
gcd(84, 30)                               -- …and the PREFIX spelling of one
q(1)   h(3)   h(-t)   (f ∘ g)(t)          -- call/compose: inserted coercions
ℤ[3]                                      -- nth element (numeral ⇒ index)
let A := {1, 2, 3} in 𝒫(ℤ)                -- powerset ascription (also 2^ℤ)
A ∪ B   A ∩ B   A \ B   A △ B             -- the Sets methods, spelled
A × B   𝒫(A)   |A|   2^|A|                -- denoted sets, and cardinality
ℂ - ℚ                                     -- …and a denoted domain difference
assert 2 + 3 = 5      assert 2 + 3 = 0 in ℤ/5
assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ         -- `and` chains ASSERTIONS
assert 8 ∈ Y          assert 9 ∉ Y        assert X = ℕ
assert x ∈ ℤ[x]       assert p ∈ ℚ[x]
assert A ⊆ A ∪ B      assert A in 𝒫(ℤ)    -- `in` is SPEC.md's ASCII `∈`
{n ∈ ℤ | n² ≤ 20}   {2n | n ∈ ℕ}   {e(n) | n ∈ ℕ, 0 ≤ n < 6}
e(ℕ)   e.image()                          -- the image, one method two spellings
#explain_route <expr>   #capabilities   #capability_gaps
```

Parser decisions (load-bearing):

- brackets after a domain: `D[ident]` is a polynomial ring in that
  indeterminate; `D[numeral/expr]` is nth-element indexing (matches the
  plans' `ℤ[3]`; ring adjunction `ℤ[√2]` is out of scope — ceiling). The
  ident must be UNBOUND to name an indeterminate: after `let z := 5 in ℤ`,
  `ℤ[z]` is the index `ℤ[5]`, not a polynomial ring. That is what makes a
  binding win over both readings a bare name can acquire — this one and the
  `NAME ∈ D[NAME]` membership below — and it is pinned as such.
- **implicit multiplication is a numeral against an ATOM-OR-POWER**
  (`casTerm:76`): `2x`, `2n`, `2√2`, and — since #26 was ruled — `3x²` and
  `2x^2`, both of which mean `3·(x²)` and `2·(x²)`. The EXPONENT binds
  tighter than the juxtaposition, which is the universal convention; before
  the ruling the product sat at `max` and the superscript took it as its
  base, so `3x²` was `(3x)² = 9x²` and `SPEC.md` §Differentials' own
  `f := x ↦ 3x² + x + 1` bound a polynomial nobody wrote. 76 rather than 71
  also EXCLUDES unary minus and `∘` (75), so `3-x` stays the subtraction it
  always was. `2√2` needs no production of its own any more — a radical is
  one of the atoms this takes, and a second parse of the same length would
  be an ambiguity rather than a spelling;
- **application by JUXTAPOSITION** (`M v`, `M⁻¹ b`) and the inverse's `⁻¹` are
  three productions rooted at an `ident` on the LEFT — the same hazard control
  as the `noWs` before `(` and `[`, and narrower than it. The residual, stated
  exactly: a cell swallows its next line when the previous line ENDS in a bare
  identifier and the next line BEGINS with one. NEITHER LINE NEED BE A BARE
  NAME — `k1 + 1` and `k1.is_prime()` end in a numeral and a `)` and do not
  swallow, while SPEC.md's own `let W := span_QQ{…} \leq ℚ³ in QQ-Mod` ends in
  `Mod` and does. Documented rather than closed — Lean's command parser spans
  lines, so nothing here can require "the same line" — and on the ledger (#24);
- **`span_QQ{…}` leads with an `ident` and checks the NAME** in `toExpr`,
  which is what keeps `span_QQ` an ordinary identifier: a leading
  `&"span_QQ"` is not indexed by a first token, so the bare-name production
  wins the longest match and the braces become a set literal on the next
  statement. Any other name gets a refusal naming the one spelling there is;
- **a hyphenated CATEGORY name is read in ascription position only**
  (`in QQ-Mod`): the term grammar reads `A-B` as a subtraction of two names,
  which in that position has no other meaning — neither name is bound — so it
  names the registered category `A-B` when there is one and is the ordinary
  error when there is not. Lean escapes such a name as `«QQ-Mod»`; the
  guillemets are its syntax for WRITING the name, so `Eval.renderName` drops
  them wherever a name reaches the mathematician.
  KNOWN INTERACTION with the juxtaposition above, and the reason that
  "neither name is bound" justification does not survive a following line: a
  bare name on the NEXT line becomes the right operand of `Mod`, so the
  ascription reads `QQ - Mod(next)` and fails with the misleading "'QQ' is not
  bound". Teaching `categoryAscription?` that shape would bind the category —
  and SILENTLY DROP the swallowed statement, which is a wrong answer where the
  error is only a confusing one, so it is not a contained fix. On the ledger
  (#24) with the juxtaposition residual it belongs to;
- **`x^{k}` is the braced exponent**, the spelling this system's own LaTeX
  renderer produces and the one `SPEC.md` writes its tolerance in
  (`1/10^{10}`). A single-element brace in EXPONENT position is therefore that
  exponent rather than the one-element set it would otherwise be; `2^{1, 2, 3}`
  has a comma and is still the powerset `SPEC.md` spells `2^A`, and `𝒫({3})`
  remains how a singleton's powerset is written;
- **`ℝ/O(ε)` is a production of its own**, and not a domain term: it is
  meaningful only as the target of `map … to` (§Numerical approximation).
  `O` is a non-reserved keyword like `and`, so `O` is an ordinary identifier
  everywhere else;
- a superscript exponent (`t²`, `x³`) is `^` in SPEC.md's other spelling.
  CEILING: one digit — `assert h = hp` is exactly the claim that the two
  spellings agree, and larger exponents have `^`;
- `→` and `->` build a function domain; `ℝ` and `ℂ` are tokens like
  `ℕ`/`ℤ`/`ℚ`, while the ASCII spellings `R`/`RR`/`CC` are ordinary
  identifiers resolved after the bindings. The Unicode names are registered as
  aliases too (`Eval.domainAlias?`), for a lexing reason rather than a
  spelling one: `ℝ.cardinality()` lexes as ONE hierarchical identifier, so a
  domain used as a method RECEIVER arrives as a name and never as its own
  token — without the alias it was the misleading "'ℝ' is not bound";
- **`and` chains ASSERTIONS, not terms.** SPEC.md's ⊆-chain is three claims,
  each decided on its own, under one ambient `in D`; the first that is not
  true stops the cell NAMING ITSELF, so a chain never reports "false" without
  saying which link was. It is a non-reserved keyword (`&"and"`), so `and`
  remains an ordinary identifier everywhere else;
- **`f(a, b, …)` is the PREFIX spelling of a method call** — SPEC.md writes
  `gcd(84, 30)`, which is `84.gcd(30)`. It reads that way only when `f` is
  UNBOUND *and* some category declares it as a method, so it converts an
  honest "not bound" error into the call the mathematician wrote; a binding
  always wins, and a name no category declares is still the ordinary
  unbound-name error. Nothing else changes: the desugared call goes through
  the same resolver, router and executor, and `#explain_route a.gcd(30)`
  explains it;
- **`NAME ∈ D[NAME]` reads the bare name as the indeterminate**, LOCALLY.
  SPEC.md asserts `x ∈ ℤ[x]`, which is a Sets question about the ring on the
  right — and the only element of `ℤ[x]` a repeated `x` could name there is
  its indeterminate. The reading needs the name written on BOTH sides (a
  `Domain` records no indeterminate name, so `y ∈ ℤ[x]` stays the unbound
  error), lasts exactly one assertion, and PUBLISHES NOTHING: a bare `x` in
  any other cell is still "not bound", so this does not re-widen the name
  resolution that §Functions deliberately narrowed;
- a bare `casTerm` cell displays its value (our own command production, low
  priority so genuine Lean commands still parse);
- `assert` outcomes are fourfold — `true | false | unknown | error` — only
  `true` commits the cell; false/unknown/error give distinct diagnostics.
  `assert` is a trusted computational assertion, never a Lean theorem.
- **equality is category-bound** (design review 2026-07-30): bare `=` never
  inserts a functor, so equality between objects of different categories is
  TRIVIALLY FALSE — `F = {0, 1, 2, 3}` is false for the module fixture even
  though `U(F)` *is* that set, because there is no unique module structure
  on it. Comparing across categories requires explicitly moving into a
  common comparison category: `F.set_eq({0, 1, 2, 3})` is the Sets question
  (its receiver transports, exactly like `∈`), and it is true.

Ellipses implement exactly the Haskell-style progressions
`{a, ...} {a, b, ...} {a, ..., z} {a, b, ..., z}`; nothing more.

## LaTeX-first display (`Value.lean`, `Syntax.lean`, issue #16)

A result that has a natural LaTeX form is typeset by default — no `show()`,
no opt-in. Every presentation carries `latex?` alongside `render`:

```lean
Domain.latex           : Domain → String            -- a domain always has one
Value.latex?           : Value → Option String
SetPresentation.latex? : SetPresentation → Option String
Obj.latex?             : Obj → Option String
Denote.latex?          : Denote → Option String
```

`none` is the DOCUMENTED FALLBACK, not a failure: the cell then emits
`text/plain` alone. `none` propagates out of containers, so a set whose
elements have no form has none either.

`elabCasShow` is the one emission seam. Its bundle is `text/plain`, then
`text/latex` when there is one, then the `vnd.casdsl.value+json` payload —
plain text is in EVERY bundle, so a consumer that does not render LaTeX
loses nothing. The LaTeX payload is the math wrapped in `$$…$$`: the
renderers produce bodies (composable, and what the `#guard` pins state), and
the delimiters that make MathJax pick the payload up are added at emission.

Conventions (one spelling each, chosen once):

| shape | LaTeX |
|----|----|
| delimiters | `$$…$$`, the DISPLAY register — a cell result is displayed math, as in Sage's `backend_ipython` and IPython's `display.Math`; inline `$…$` shrinks `pmatrix` to text size |
| exponent | braced always — `x^{3}`, `2^{3}` (`x^12` typesets as x¹·2) |
| rational | inline solidus `3/2`, never `\frac`; `(1/2)x` as a coefficient |
| number systems | `\mathbb{N} \mathbb{Z} \mathbb{Q} \mathbb{R}`, and `\mathbb{Z}/5\mathbb{Z}` (`\mathbb{Z}/5` reads as a quotient by an element) |
| matrix | `\begin{pmatrix} … \\ … \end{pmatrix}` |
| vectors | the TUPLE `(1, 2)` — SPEC.md's own spelling and the one the surface reads back; parentheses and commas are math mode's own, and a column `pmatrix` would typeset something the input syntax does not say. The domain is `\mathbb{Q}^{2}` |
| subspaces | `\mathrm{span}_{\mathbb{Q}}\{ … \} \leq \mathbb{Q}^{3}` — the AMBIENT is part of the display, without which the trivial subspace is an empty brace saying nothing |
| factorization | `\cdot` between every factor; polynomial factors parenthesized as in plain text |
| sets | `\{ \}`, progressions `\{0, 2, \ldots\}`, powerset `\mathcal{P}(A)`, product `\times` |
| cardinals, functions | `\aleph_0`, `t \mapsto t^{2} + 1` |
| exact algebraic numbers | `\sqrt{2}`, `2\sqrt{2}`, `2 + 2i`, `-1/2 + (1/2)\sqrt{5}` — `i` rather than `\sqrt{-1}`, and a non-integer coefficient parenthesized as in a polynomial |
| approximations | `1.4142135623 + O(1/10^{10})` — SPEC.md's own displayed line, and the SAME string as the plain rendering: digits and `O(…)` are math mode's own spellings, and a reciprocal power of ten in the tolerance is already both conventions above it (inline solidus, braced exponent). A tolerance that is not one is the ordinary rational, `O(1/3)` |
| ideals | generators in parentheses — `(4)`, `(2, x)` |
| domains | `\mathbb{Z}[x]`, `\mathrm{Mat}_{2}(\mathbb{Q})`, and the arrow `\mathbb{R} \to \mathbb{R}` |

Everything emitted is math-mode LaTeX: no raw `ℤ`, `↦` or `ℵ₀` survives into
a payload, because MathJax does not typeset them.

Textual on purpose (no `text/latex`, and no bundle at all — these are
`logInfo` lines): assertion check-marks, every diagnostic (`#explain_route`,
`#capabilities`, `#capability_gaps`, `#canonical_maps` keep their
`text/plain` + `vnd` bundle), capability-gap refusals, all error messages,
and the binding echo `h := t ↦ t² + 1 ∈ ℝ → ℝ`. The echo is a *statement
about* a binding rather than a value display, and it reaches the notebook as
a log line with no MIME bundle to put LaTeX in; typesetting it would mean
inventing a bundle for it, which is a display change, not this one.

Values with NO natural form, deliberately:

- a truth value (`m.is_prime()` displays `true`) — `\text{true}` is typeset
  prose, not mathematics;
- the module fixture `cyclicModule n` — `\mathbb{Z}/4\mathbb{Z}` typeset
  alone is the RING, and equality here is category-bound (§Surface), so it
  would be a display-level lie;
- a function whose BINDER is not LaTeX-safe — not ASCII (`θ ↦ θ + 1`), or
  ASCII but not typesettable as written (`x_1_2` is a double subscript,
  which pdflatex rejects; `x_ab` would typeset as x_a b, silently wrong).
  The rule is ASCII letters and digits only; subscript typography is NOT
  invented here. The binder is the mathematician's own name and the only
  path by which arbitrary text could reach a payload, so the function falls
  back to plain text whole. This is what keeps the no-raw-Unicode rule above
  true rather than aspirational;
- a polynomial, factorization or function whose COEFFICIENT has no LaTeX
  form. `none` propagates out of a polynomial exactly as it does out of a
  set: the coefficients are rendered by `latex?` and the joiner receives
  strings, so a value this renderer cannot typeset can never reach a payload
  in its plain spelling. (Today every constructible coefficient is a scalar
  with a form; this is the seam that keeps that true when it stops being.)

The `value+json` payload of a set result: RESOLVED, in the display seam.
`Denote.value?` is element-shaped by design (it feeds arithmetic and
comparison, where a set is not an operand), so a set OBJECT has none, and
`p.roots()` used to publish `"value": null`. `valueJson` now falls back to
`Denote.asSet?` and encodes the two set shapes that have wire forms
(`setV`, `progV`); the DENOTED sets — `A × B`, `𝒫(A)`, `ℤ` — have no `Value`
and stay null, which is the honest answer rather than a gap. The evaluator's
`value?` is untouched: this is a rendering decision and stays in the
renderer.

## Standard universe (`Std.lean`)

Category graph (names; `≤` = registered parent edge):

```text
FiniteSets ≤ CountableSets ≤ Sets
EuclideanElems ≤ FactorizationElems ≤ CommRingElems
SmallModules ≤ Modules            (the plan's inheritance demo)
MatrixElems                       (det/inverse/rank/ker/trace/charpoly;
                                   params (n, entry))
PolynomialElems                   (deg/roots/companion_matrix; params (the ring))
FunctionElems                     (image; params (the arrow src → tgt))
ComplexElems                      (re/im/bar/abs; params (ℂ or the ℝ in it))
QQ-Mod                            (dim; an ascription TAG at this stage —
                                   §Vectors, matrices and subspaces)
```

Profiles (selected): `ℤ` (domainObj) ∈ {Sets, CountableSets, …};
`n ∈ ℤ` (elem) ∈ {EuclideanElems(ℤ)}; `q ∈ ℚ[x]` ∈ {EuclideanElems(ℚ[x]),
PolynomialElems(ℚ[x])}; `M ∈ Mat₂(ℚ)` ∈ {MatrixElems(2, ℚ)};
`cyclicModule n` ∈ {SmallModules(ℤ)}. `ℤ[x]`/`ℚ[x]` as domainObjs are
CountableSets, which is what `p ∈ ℤ[x]` asks of them. `ℝ` and `ℂ` are `Sets`
and nothing narrower — both are uncountable, so `nth` (declared on
CountableSets) correctly does not reach them, while membership does.

Methods: `factor`, `gcd`, `is_prime` on FactorizationElems; `deg`, `roots`,
`companion_matrix` on PolynomialElems; `det`, `inverse`, `rank`, `ker`,
`trace`, `charpoly` on MatrixElems; `annihilator` on
Modules; `image` on FunctionElems; `re`, `im`, `bar`, `abs`, `approximate` on
ComplexElems; `dim` on QQ-Mod;
`nth`, `cardinality`, `contains`,
`set_eq`, `subset`, `union`, `intersect`, `diff`, `symdiff` on the set
hierarchy, and `sum`/`prod` on FiniteSets (§Aggregation). Inheritance is
exercised twice for real: `factor` reaches integers via `EuclideanElems ≤
FactorizationElems`, and `annihilator` reaches the fixture via
`SmallModules ≤ Modules` with **no forwarding declaration**.

`PolynomialElems` deliberately carries NO parent edge. Degree and roots are
a *structural* read of a polynomial and make sense over any coefficient
ring, including ones where factorization does not; a polynomial therefore
inhabits the divisibility hierarchy and this one INDEPENDENTLY, and neither
membership is allowed to imply the other. `roots` returns the roots in the
polynomial's own coefficient ring — an empty result (`x² − 2` over ℚ) is the
answer, never a silent reach into an extension. ℂ[x] is a routed coefficient
ring like the others, so the roots that ring DOES have are one explicit
`map q to ℂ[x]` away (§Exact number systems).

One functor ships: `UnderlyingSet : Modules → Sets` (object map: the
ℤ-module ℤ/n to the finite set of its residues). It is what makes
`F.cardinality()` work on the module fixture — a method declared on `Sets`,
which the module does not inhabit, reached by transporting the receiver and
routed against the image. `annihilator` on the same object still resolves
directly through the inclusion edge, untransported; both claims are asserted
in `acceptanceProofs`.

The deliberate capability gaps shipped by the universe (honest, auditable):
`det`/`inverse`/`rank`/`ker`/`charpoly` on matrices whose entry domain is not
ℚ — each is meaningful on any `MatrixElems` member, only ℚ-entry matrices are
routed, and `Mat₂(ℤ/5).det()` is the notebook's fails-on-purpose demo. The
same object shows the other side of the separation: its `trace` DOES route,
because reading a diagonal is native and needs no ℚ. Alongside them,
`companion_matrix` outside ℚ[x] (`map r to ℚ[x]` is one explicit step away),
`nth` on a subspace (countable, no enumeration registered), and
`gcd` and `is_prime` outside ℤ (both are meaningful in every UFD; only the
ℤ routes are registered), `roots` outside ℤ[x]/ℚ[x]/ℂ[x], `nth` on ℤ[x]
(countable, no enumeration registered), and the binary set operations on any
receiver that is not an explicit finite list (`ℤ ∪ A`, `𝒫(A) ∪ A`), and
`approximate` on ℂ (asking for a decimal is meaningful for every exact number;
only the reals are routed, and a real decimal presents no complex value) —
each one available, none executable, all asserted as gaps by the proofs at the
end of `Std.lean`. (The
original gaps — `nth` on ℚ and `factor` on ℤ[x] — were routed in round
three per the user-decided closure paths, #17/#18; the ℚ enumeration is
the registered Cantor zigzag, revisitable like ℤ's convention.)

## Decisions inherited from the anti-drift record (binding)

1. Ordinary syntax is backend-blind; no `using Sage`, ever.
2. Sage is reached by a direct adapter and brokers nothing else.
3. Methods are category-owned. Non-direct availability comes from exactly
   two registered mechanisms, both behind the resolver: subcategory
   inclusion (method transport) and preferred functors (receiver
   transport). Neither is ever a forwarding declaration on a leaf.
4. Capability gaps never flow upward into semantics; no
   implementation-shaped categories (no `EnumerableCountableSet`).
5. Results are trusted CAS values: no certificates, no theorem generation,
   no recomputation, no proof obligations on ordinary computation.
6. Mathematician-facing coercions (polynomial call, `ℤ ⊆ ℚ`) are inserted
   by elaboration; internal distinctions stay internal. `ℤ ⊆ ℚ` denotes the
   REGISTERED preferred structure-preserving map, not a code-level
   conversion, and an unregistered pair of domains has no coercion at all —
   it is never widened to a "reasonable" one.
7. Backend owns factorization order/unit convention; we keep only the
   neutral result shape.
8. Eager reflection of small values is a slice choice, not a permanent
   semantic requirement (future: typed computation descriptions + caches).

## Decided by user review, 2026-07-30 (vault: DECISION-CAS-ROUND2-REVIEW)

Formerly open questions, now user-decided — none was silently resolved:

- **user-defined categories**: DEFERRED behind the stage-2 evaluation
  (trajectory ruling, later 2026-07-30, superseding the same-day "ships
  now" ruling). The local-origin re-scope recorded on #6 — leaf categories
  only, membership by shape rule or ascription, methods derived only —
  stands as the design of record for when it returns. The spike implements
  `SPEC.md`'s *functions* section instead (`t ↦` lambdas, typed ascription,
  equality, composition), which delivers the derived-method value with no
  category machinery;
- **backend provenance**: never default output — an opt-in `info`-level
  logging layer with per-line/per-cell verbosity directives (issue #8);
  results themselves become LaTeX-first with plain-text fallback (#16 —
  shipped, §LaTeX-first display);
- **retry/migration policy**: ADOPTED — no automatic retry or migration,
  ever. Backend failure is a structured report; re-running a cell is the
  user's explicit act and re-routes from scratch. Revisit only when
  long-running computations exist (#4, deferred until a workload hurts);
- **which backend follows Sage**: GAP, direct adapter, justified by
  `unit_group` on ℤ/n (issue #3);
- **enumeration of ℚ**: Cantor zigzag (reduced-fraction skipping), a
  registered revisitable choice like ℤ's; implementing it must also
  replace the notebook's fails-on-purpose `ℚ[3]` demo (issue #17);
- **`factor` on ℤ[x]**: routed via Sage, content × primitive (#18) — the
  `map p to ℚ[x]` demo stays, reframed as the canonical-map demo;
- **route/op agreement**: checked at build time via registered op
  signatures, not left to runtime defensive arms (see §Routing and gaps).

## Open questions (kept open — do not silently resolve)

- **does `roots` default to the coefficient RING or to the splitting field?**
  Today it is the ring, and that default is pinned. `SPEC.md` writes
  `assert q.roots() ⊆ ℂ - ℚ` for `q = x² - 2 in ℚ[x]`, where the root set is
  EMPTY — so the line runs and is TRUE, but only vacuously, and its
  closure-reading (`{√2, -√2}`) needs the explicit `map q to ℂ[x]`. Both
  readings ship, side by side, in `CasDslTests`, `tests/test_e2e.py` and
  notebook §12, so the gap between what the line says and what it checks is
  visible in every artifact. Escalated to the project owner (unit U5, 2026-07-30):
  changing a pinned surface default is not this repo's call, and nothing here
  may quietly adopt the closure reading in the meantime;

- default enumeration convention for `ℤ` (slice: 0, 1, −1, 2, −2, …,
  zero-based — a *registered choice*, revisitable);
- the concrete declaration syntax for notebook-level categories (proposal
  owed under issue #6);
- the logging layer's level surface and directive syntax (#8);
- which methods beyond `unit_group` the GAP bridge routes first (#3).

## Ceilings (deliberate, documented)

- exact algebraic numbers are `a + b√d` — ONE square root over ℚ, and a
  square-free radicand certified only up to `squareFactorCap`;
- an approximation has NO arithmetic, and `ℝ/O(ε)` is not a number system:
  the value carries a requested tolerance rather than an error term, so a sum
  of two approximations is a loud refusal rather than an invented error
  calculus (§Numerical approximation);
- the shipped adapter certifies at most `MAX_DIGITS = 1000` decimal digits; a
  tighter tolerance is a capability refusal naming what was asked;
- exact algebraic values are UNORDERED at the SURFACE, the REAL ones included:
  `√2 ≤ 2` is the honest "not comparable" rather than an answer, even though ℝ
  is ordered and `Value.nonNegSurd` decides a sign by squaring. That comparison
  is used INTERNALLY — the approximation certificate is exactly it
  (§Numerical approximation) — and lifting the surface ceiling is still a
  separate decision: a `scalarCmp` arm, deliberately not taken here, and
  `Native.scalarCmp` states its refusal as its own arm so that the internal use
  cannot quietly become a surface answer;
- a subspace is spanned over ℚ, and presented by its REDUCED basis: a
  generator this slice cannot read as a rational vector is a loud refusal
  (§Vectors, matrices and subspaces), and a lambda with several binders — the
  `φ` of SPEC.md's own `W = ker φ` — is a disclosed gap that names itself;
- a matrix and a vector must be over ONE entry domain: this backend does not
  join them, for the reason the binary set operations do not;
- aggregation is over an EXPLICIT finite set; the sum over an infinite one is
  a limit this slice has no notion of, and says so as a non-method;
- set equality by presentation normalization only;
- argument validation at execution, not declaration;
- receiver transport is ONE hop, with no result lifting and no
  preferred-path registry; an object map that is not one of `ObjMap`'s
  constructors is not registrable;
- a canonical map whose value transform is not one of `CanonOp`'s constructors
  is not registrable either (the `ObjMap`/`DomainPattern` ceiling again: a
  new transform is a visible edit to the engine's vocabulary, never a closure
  in the environment);
- a coercion applies ONE rule: rules do not compose, which is why `ℕ ⊆ ℚ` is
  registered explicitly next to `ℕ ⊆ ℤ` and `ℤ ⊆ ℚ`;
- no backend-call cancellation beyond process teardown with the kernel;
- `#capability_gaps` crosses declared methods with registered
  representative presentations (not all conceivable objects);
- sandbox mode: Sage is unavailable inside bubblewrap — its routes surface
  as capability gaps there, which is exactly the honest behavior.
