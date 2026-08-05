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
CasDsl/Value.lean       Domain, SymExpr, SeriesGen, Value, SetPresentation,
                        Obj  (core data model — six inductives)
                        + their plain-text and LaTeX renderings
                        + the shared EXACT-ARITHMETIC FLOOR (see below)
CasDsl/Category.lean    CatRef, category/method/functor/route/canonical-map TYPES
CasDsl/Codec.lean       the wire codec: Value/Domain/SymExpr <-> backend JSON
CasDsl/Registry.lean    env extensions + registration API (semantic state)
CasDsl/Register.lean    the CHECKED registration adders (addRouteChecked, …)
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
CasDslTests/            Lean #guard + elaboration-time test modules
tests/                  Python roundtrip against real Sage + E2E kernel run
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

PRE-RULING, now SUPERSEDED and kept for the trail: it said U8's certificate
arithmetic — polynomial add/sub/mul for the derivative and integral reply
checks — would come down into this floor. It presumed a BACKEND computed
them. Both are NATIVE, so there is no reply to certify and the floor gained
no twin (§Differentials records why not having a backend beats checking one).
The rule the pre-ruling stated is untouched and still governs the next
certificate that needs arithmetic: it goes here, not into a backend's half.

OPEN NOTE, raised in review and deliberately not solved here: the ZERO of a
domain is known in two places. `Native.zeroOf` has it for every domain
including `ℤ/n`; `Value.mkCoset` needs it and cannot ask, because a backend is
not in this module's cone. `mkCoset` is therefore NARROWED to the kernels
whose zero it can write itself (ℤ, ℚ, ℝ, ℂ) and refuses `ℤ/n` loudly, which
is honest but leaves the two owners standing. Whether the arithmetic floor
should own `zeroOf` — an `Arith.lean` under `Value.lean` that both a backend
and the data model may import — is the question, and the first spec line that
wants a coset over `ℤ/n` is what should force it. The question is issue #30;
the freeze stands until that forcing line arrives.

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
  | setV (elems : Array Value) (dom : Domain)      -- a finite set result
  | msetV (elems : Array Value) (dom : Domain)     -- p.roots(): repetition = multiplicity
  | progV (dom : Domain) (first step : Value) (last? : Option Value)  -- e.image()
  | spanV (n : Nat) (basis : Array Value)          -- M.ker(), a subspace of ℚⁿ
  | cardinal (c : Cardinality)     -- finite n | countablyInfinite
  | bool (b : Bool)
  | func (src tgt : Domain) (binder : Name) (body : Value)   -- binder ↦ body

inductive SetPresentation
  | finite (dom : Domain) (elems : Array Value)
  | multiset (dom : Domain) (elems : Array Value)  -- with repetition; |·| counts it
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

`setV`, `msetV`, `progV` and `spanV` are the shapes an EXECUTOR may return
as a set-like object (`e.image()`, `p.roots()`, `M.ker()`);
`Denote.ofValue` turns them into the ordinary `setObj (.finite …)` /
`setObj (.multiset …)` / `setObj (.arithProg …)` / `setObj (.span …)`, so a
returned set answers to the set methods like any literal one — same profile
rules, same `contains`, same equality — rather than a second notion of set.
The multiset is not a second spelling of `finite`: display repeats, `|·|`
counts with multiplicity and `=` compares counts (a finite SET on the other
side lifts along `Finset.val`), while `∈` and `⊆` read the support —
Mathlib's own `Multiset.card`/`=` versus `∈`/`Multiset.Subset` split.
CEILING: an explicit finite list, a finite multiset, an arithmetic
progression, and a subspace of ℚⁿ, nothing wider. `product` and `powerset` are DENOTED
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
- **`i` is a RESERVED SYMBOL** (`Eval.constantValue?` carries the value;
  `reservedConstantMsg?` guards the name — ruling 2026-07-31, #31 item 3):
  the imaginary unit in every session state. Unlike `R`/`π`/`d`, which stay
  shadowable spellings, `let i := 5` is refused outright, so `2 + 2i` can
  never quietly mean 12.
- **ℂ[x] is where the cubic splits**, and `roots` STILL answers in the
  polynomial's own coefficient ring. `map p to ℂ[x]` is the ordinary
  registered coercion (ℤ ⊆ ℂ, coefficient-wise), `factor` and `roots` are
  routed there to their own Sage ops, and SPEC.md's displayed factorization
  `(x-1)(x - (-1+√5)/2)(x - (-1-√5)/2)` comes back as three monic linear
  factors with exact `a + b√d` coefficients. Its CONTENT is what is pinned —
  each displayed root evaluates to zero, and a near miss does not — because
  the factor ORDER and the unit convention are the backend's (decision 7).
  RULED (owner, 2026-07-31, refined the same day): the ring default STANDS
  — `p.roots()` always means the roots in `p`'s own coefficient ring, and
  no spelling implicitly applies a field extension or passes to an
  algebraic closure. SUPERSEDED IN CARRIER (approved pre-pass, 2026-08-05,
  SPEC-REGISTRY-TYPE-PREPASS §3.3): `roots` returns the MULTISET its
  anchor `Polynomial.roots` returns — multiplicity shown by repetition
  (`(x−1)²` answers `{1, 1}`), `|·|` counted with it — replacing the
  earlier set-plus-factor-carrier convention, which hid the double root.
  The deficit note is EXACT and needs no second call:
  `Eval.rootsRingNote` reads the multiset's size (which IS Σ mᵢ over the
  ring's linear factors) against the degree and fires precisely when `p`
  fails to SPLIT in its ring, naming the `map p to ℂ[x]` escalation;
  `(x−1)²` over ℚ splits and gets no note. The note's TEXT is the
  declaration's (`MethodDecl.advisory`), not the evaluator's. Two owner principles anchor the
  behavior: a PROPOSITION over the result has a truth value and is never
  refused — `assert q.roots() ⊆ ℂ - ℚ` stays vacuously TRUE over ℚ, with
  the unexpectedness carried as the advisory note (§Sets ⊆ ruling) — and a
  note is advice riding alongside a result, never part of the value
  (nothing downstream may read one back; distinct from the opt-in logging
  layer, #8). ℂ[x] receivers get no note (everything splits there), and
  the comprehension spelling `{a ∈ D | …}` gets none because it names its
  ring itself.

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
  THAT HAS HAPPENED, and the declaration is §Elementary calculus': a symbolic
  LIMIT and a symbolic definite integral have no finite exact computation on
  this side that could check them, so their replies are trusted and only their
  KIND is verified. The two statements are one policy, and it reads the same
  in both directions — a reply is trusted only where no exact check exists,
  the absence of the check is named where it bites, and what is still checked
  is written down.
  THE REAL BOUNDARY, stated exactly rather than as a slogan. Three replies are
  CHECKED against the receiver: `approx_real`'s certificate, `mat_charpoly_q`'s
  monicity and degree, `poly_companion_q`'s trace and determinant — and, since
  the review that noticed the exact check was sitting unused twenty lines
  away, `mat_det_q` against `Value.detQ`. Three are TRUSTED BY DECLARATION:
  `sym_limit`, `sym_definite_integral` and `sym_taylor` (§Elementary calculus).
  The REST are KIND-CHECKED ONLY — `factor_int`, `factor_poly_q/z/c`,
  `gcd_int`, `is_prime_int`, `roots_poly_z/q/c`, `mat_inv_q` — and that is a
  weaker position than either, so it is named here rather than implied away.
  Checking them is not free the way `detQ` was: verifying a factorization or a
  root set means multiplying the factors back or evaluating the polynomial at
  each root, and verifying an inverse means a matrix product — arithmetic
  `Value.lean` does not have and that no `SPEC.md` line has forced. When one
  is written, it belongs to that floor and these ops move up a row.
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
  less code, so it supersedes the pre-ruling. `Value.lean` gained the SHAPES
  this section needs (`diff1`, `derivation`, and `Obj.specOf`) — what it did
  NOT gain is the arithmetic TWIN the pre-ruling anticipated, because no
  certificate exists to need one.
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

## Indefinite integration (`SPEC.md` §Indefinite integration, issue #24)

`∫ f dx` is the COMPLETE SET OF PRIMITIVES — a coset of `ker(d/dx)`, which is
what `SPEC.md`'s `+ ℚ` says — and the `antiderivative` method returns exactly
that rather than one primitive plus a convention about which.

- **NATIVE, for the reason the derivative is.** `cᵢ/(i+1)` shifted up by one
  is exact coefficient arithmetic, so no backend is asked. The division is
  what makes it routable only where the fraction field is one this slice
  presents: ℤ[x] and ℚ[x] are routed (both land in ℚ[x]), and `ℤ/5[x]` is the
  honest capability gap `det` over ℤ/5 already is.
- **`SetPresentation.coset` is a NEW presentation, and `span` is deliberately
  NOT widened to cover it.** That one is hard-wired to ℚⁿ and its normal form
  is a reduced basis; this one's normal form is a canonical REPRESENTATIVE.
  `Value.mkCoset` is the one constructor and it canonicalizes: the kernel is
  the constants, so the representative with constant term ZERO is a function
  of the coset and of nothing else — the `mkSpanBasis` discipline, with the
  same payoff. Two cosets compare as data, so `∫ f dx = x³ + (1/2)x² + x + ℚ`
  and `… + 7 + ℚ` are the same set and a coset of a different function is
  not. Membership needs no subtraction either: `h ∈ p + K` is exactly "agrees
  with `p` above degree zero".
- **`p + ℚ` on the right of an assertion is built by ELABORATION** — a value
  plus a DOMAIN — exactly as `A × B`, `𝒫(A)` and `ℂ - ℚ` are. It goes through
  `mkCoset` too, so a coset a mathematician writes and one `∫` computes are
  the same value however either was spelled.
- **`{h ∈ ∫ f dx | h(0) = 0}` is the SAME production as the root set**, over a
  coset instead of a domain, and `=` gains no further meaning by it. The
  equation is solved rather than searched, and the CEILING is what makes that
  exact rather than a fit: one side must be an APPLICATION of the binder at a
  point. The members of `p + K` are `p + c`, so `h(a)` is `p(a) + c` and the
  equation is linear in `c` with slope one BY THE SHAPE — checked before any
  arithmetic runs. A guard of any other shape is a loud refusal naming the
  shape that works.
- **`(1/2)x²` needed a production.** This renderer parenthesizes a non-integer
  coefficient so it reads as a product rather than as one rational, and
  `SPEC.md` writes the same spelling — but until now the surface could not
  READ BACK what it prints. `casParenMul` takes the same atom-or-power
  (`casTerm:76`) that implicit multiplication takes, so the two spellings of
  an implicit product agree about the exponent, and its `noWs` is what leaves
  `(6x + 1) dx` to the differential form.

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
  be invented), and no value at a point: `sine(0)` AND `recip(2)` are both
  loud refusals naming the body, because a decimal for `sin(0)` — or for
  `1/t` at 2 — is an APPROXIMATION, and that is a separate operation on an
  exact element. A RATIONAL body gains no pointwise evaluation either; no
  `SPEC.md` line calls one, and inventing it would be that approximation. Two symbolic bodies are
  INCOMPARABLE rather than unequal — `1/t` and `t^(-1)` are one function and
  two trees, so `false` would be a claim this slice cannot make.
- **TWO readings, in a fixed order, and the order is PINNED rather than
  commented.** `h = hp`, `h(0) = 1`, `h(3) = 10` and `h(-t) = h(t)` are the
  sentinels: all four are identities or evaluations only the POLYNOMIAL
  reading decides, so flipping the order kills them — verified by mutation
  (`h = hp` becomes "unknown" and the three calls become the symbolic-body
  refusal). The reason for the order is unchanged: A `↦` binding tries
  the POLYNOMIAL reading first and keeps it wherever it applies, because that
  is the reading that decides (`h(-t) = h(t)`, `(f ∘ g)(t) = t⁶`, and equality
  of two bodies). Only a body it cannot express is read symbolically. This is
  an ordering, not a fallback: a body NEITHER reading reaches is the symbolic
  reader's refusal, which is the wider of the two.
- **A bound name is REFUSED inside a symbolic body**, never substituted and
  never read as the constant it shadows. There is nothing to substitute into
  — a symbolic body is not evaluated — and reading a bound name as a
  shadowable constant (`π`, `d`) would answer with a value the mathematician
  did not write; the refusal is only an inconvenience.
- **The e-collision is RESOLVED by reservation (owner ruling, 2026-07-31,
  #31 item 3 — superseding the earlier ratified refusal).** `SPEC.md` once
  bound `e` to the doubling map in §Set comprehensions while writing `e^t`
  for Euler's number in §Elementary calculus, and the binding won. The
  owner's resolution: there is no reason to keep `e` as a function name —
  that map is now `m2` in SPEC itself, and `e` is a RESERVED SYMBOL
  (`reservedConstantMsg?`) no binding or binder may shadow, `i` with it.
  `e^t` therefore reads Euler's constant in EVERY session state — SPEC's
  §Elementary calculus third block runs top-to-bottom — and
  `exp(x) := e^x` (the owner's words) remains the equivalent spelling.
- `∞` is a TOKEN because it is not an identifier character; `π` and `e` are,
  so those two are ordinary constants consulted after the bindings. All three
  denote the same kind of thing — a symbolic constant with no domain.

## Elementary calculus (`SPEC.md` §Elementary calculus, issue #24)

`lim`, the definite integral and the Taylor expansion are ONE shape: an
ordinary METHOD on a FUNCTION (`limit`, `definite_integral`,
`taylor_expansion`), with the surface production building the function by
elaboration exactly as `{a ∈ ℂ | r(a) = 0}` builds the polynomial it hands to
`roots`. `#explain_route` explains all three, and a backend that cannot run
one is the ordinary structured gap.

- **`lim` IS a routed operation, and `Domain.real` gains nothing.** The
  surface claims no epsilon-delta semantics: ℝ is still uncountable,
  unordered and un-enumerated, and `limit` is not a method of ℝ or of any
  number. It is asked of an EXPRESSION and it answers with an exact value —
  a rational or `a + b√d` — or refuses. A limit that does not exist or is
  infinite is the backend's refusal, not a value.
- **THE TRUST BOUNDARY, named here because this is the first one.** There is
  no finite exact computation on this side that decides `lim_{t→0} sin(t)/t`,
  so unlike `approx_real` (whose certificate is verified),
  `mat_charpoly_q` (monic, right degree) and `poly_companion_q` (trace and
  determinant), the reply is TRUSTED. What is checked is its KIND: an exact
  value this slice presents, so a decimal, a factorization or an unevaluated
  expression coming back is still an adapter defect rather than an answer.
  §Numerical approximation said such a seam "would have to be declared, and
  the declaration would have to be visible here". This is it, and that section
  now points here: ONE policy, stated from both ends — a reply is trusted only
  where no exact check exists, the absence is named where it bites, and what
  is still checked is written down.
  The definite integral sits on the same boundary; the Taylor expansion is
  checked one step further — its coefficients must be exact RATIONALS, and a
  coefficient that is not one is refused rather than turned into a decimal.
- **The adapter's strategy is its own, and is named nowhere in the surface.**
  It computes the Taylor coefficients from the DEFINITION (`f⁽ⁿ⁾(a)/n!`,
  through symbolic differentiation) rather than from a series routine, and it
  asks SymPy for a limit rather than Sage's default Maxima. That second one is
  worth recording rather than merely doing: the SageMath install this was
  developed against has a BROKEN Maxima — both the ECL library interface
  ("Module error: Don't know how to REQUIRE MAXIMA") and the `/bin/maxima`
  binary fail — so the default algorithm cannot run there at all.

## Formal power series (`SPEC.md` §Elementary calculus, §Ellipses, issue #24)

`Domain.series` is a real domain (the ascriptions `in ℝ[[t]]` and
`assert Tf ∈ ℝ[[t]]` force it), spelled `D[[t]]`. Its indeterminate is `t`
exactly as the polynomial ring's is `x` — a `Domain` records no name, and one
spelling per ring is what keeps a display readable back as input.

- **A series is presented by finitely many coefficients PLUS the generating
  rule where one exists**, and the DISPLAY says which reading is in hand: a
  RULE knows every coefficient, so a bare series shows a few and `…`; TERMS
  know exactly the ones they carry, so they show them and `O(tⁿ)`. A
  truncation is then a real operation on the presentation — it turns a rule
  into terms — rather than a second value meaning the same thing.
  A series is written in ASCENDING order, unlike a polynomial: it has no
  highest term, and its tail belongs at the end.
- **CEILING, and it is loud.** A `terms` series knows `Value.seriesTerms`
  coefficients — which is how far a Taylor expansion is computed, and a
  different number from the `seriesShown` a bare series DISPLAYS. A truncation or a coefficient past that is a refusal NAMING
  the ceiling — never a shorter answer returned as if it had been requested,
  which is the same discipline `MAX_DIGITS` follows for a tolerance. Both
  refusals share one wording, because they are one fact about the
  presentation.
- **`ℝ[[t]]/(t^6)` and `ℤ[[t]] / O(t^5)` are ONE truncation REQUEST with two
  spellings**, on the `ℝ/O(ε)` precedent: meaningful only after `map … to`,
  no `Domain` constructor, and a loud refusal written anywhere else — so it
  answers no membership, cardinality or inclusion question, because a request
  has none.
- **The series coefficients are exact RATIONALS.** Every series `SPEC.md`
  writes has them (`n²`, and the `1/n!` of a Taylor expansion), and holding
  `Value`s would make `SeriesGen` mutually recursive with `Value` for no gain
  the surface asks for.
- **Series membership is as narrow as the ascription needs.** `Tf ∈ ℝ[[t]]`
  is decided by the coefficient domain MATCHING, and the tag is a normal form
  rather than a guess — `coerceValue`'s structural congruence maintains it at
  every boundary a series crosses, so the ascription always meets a matching
  tag. A MISMATCH at the executor is still not answered there: `ℚ[[t]] ⊆
  ℝ[[t]]` is the canonical-map registry's claim, and `normalSubset` keeps
  refusing to restate it for `dom ⊆ dom`. The SURFACE, though, answers it
  (⊆-conformance audit, 2026-07-31, #31 item 9): both spellings — `assert
  ℚ[[t]] ⊆ ℝ[[t]]` and `(ℚ[[t]]).subset(ℝ[[t]])` — are the registry's
  decision at elaboration (`domainSubset`, and the `subset` intercept in
  `callMethod` that keeps the two spellings one decision), where the
  coefficient-wise ℚ ⊆ ℝ INDUCES the series inclusion exactly as it induces
  ℚ[x] ⊆ ℝ[x] — TRUE there, FALSE in the unregistered direction, never a
  refusal. Nothing new was registered: the induced reading is `domainSubset`'s
  standing structural recursion, bottoming out in the registry.
- **A series RING is a `Sets` member and nothing narrower**: a formal power
  series is an arbitrary SEQUENCE of coefficients, so `ℤ[[t]]` is
  UNCOUNTABLE — the standing ℂ[x] already has. Membership routes; `nth` is
  not even applicable.
- **`[t²]f` is a THIRD reading of the brackets**, beside the polynomial ring
  `D[x]` and the index `e[k]`, told apart by what follows: a matrix literal
  ends at its `]`, and this one has a receiver against it with no space. The
  exponent is read STRUCTURALLY — `t` names no binding, it is the series' own
  indeterminate — so `[t^{2}]f` works through the same brace-unwrapping the
  exponent slot already does.
- **`ℤ[[t]]` is two adjacent `[` tokens, not a `[[` token.** A `[[` token
  would be produced by the tokenizer everywhere, including inside Lean's own
  `#[…]` array literals. What keeps `ℤ[[t]]` from ALSO parsing as the index
  `ℤ[…]` applied to the one-row matrix `[t]` — a parse of exactly the same
  length — is a `notFollowedBy("[")` on the index production: an index is
  never written with a matrix literal as its subscript.
- **`lim_` is a token with its underscore**, because `_` is an identifier
  character: `lim_{t → 0}` lexes `lim_` as one IDENTIFIER, so a bare `lim`
  token is never seen. (`∑_{…}` has no such problem — `∑` is not an
  identifier character.)

## Sets (`SPEC.md` §Finite sets, issue #24)

The set operations SPEC.md writes — `∪ ∩ \ △ × 𝒫 |·| ⊆ ∈` — are all
category-owned methods on `Sets`, reached by the ordinary resolver and
router, except the two that construct rather than compute.

- **RULED (owner, 2026-07-31): `X ⊆ Y` is a PROPOSITION with a truth
  value.** In the owner's words: if `X ⊆ ℚ` and `Y` is a random set, then
  `X ⊆ Y` is FALSE unless there is a canonical monomorphism `m : X → Y`
  allowing `X` to be regarded as a subobject of `Y` in Sets, whence `X` is
  identified with `m(X)` as an actual subset. In this system the registered
  preferred canonical maps ARE that supply of monomorphisms — no
  identification registered means FALSE, not refused. A well-formed
  inclusion between honest sets is never "unknown", and a surprising-but-
  true outcome (a vacuous inclusion over an empty left side) is answered
  TRUE with an advisory note — info with advice on sharpening the result —
  never a refusal. Refusal remains correct only where the sentence is not a
  set proposition at all (`ℝ/O(ε)` on either side, a result with no set
  reading). The conformance audit (2026-07-31, #31 item 9) closed the one
  known candidate: series inclusion answers from the registry at both
  spellings — §Formal power series records the shape.

- **A scalar times a set is the IMAGE of the scaling map (ruling
  2026-07-31, #31 item 6).** SPEC.md §Ellipses asserts `Y = 2ℕ`, and
  `k·S` is DENOTED by elaboration exactly as `A × B` is: an arithmetic
  progression scales to an arithmetic progression, an explicit finite set
  scales elementwise, and `ℕ` is the progression `{0, 1, 2, ...}` — so
  `2ℕ` IS `{0, 2, 4, ...}`, and `Y = 2ℕ` is the ordinary progression
  equality. CEILING, stated in the refusal: those three presentations
  under a rational scalar (`Eval.scaleSet`); `2ℝ` names the rule and
  refuses. Every other `*` is untouched.

- **A predicate set is a LAZY presentation backed by its guard (ruling
  2026-07-31, #31 item 7).** `{n ∈ ℕ | n.is_prime()}` BINDS: a filtering
  comprehension whose guard the bound extraction does not read AT ALL
  presents as `SetPresentation.predicate dom binder guard`, provided the
  guard decides
  elementwise at the probe and the head is the binder itself (the IMAGE of
  a lazy set is not presented, and says so). A guard the extraction DOES
  read keeps its decided outcomes — a finite enumeration, the empty set, or
  the loud infinite refusal — exactly as before. Membership EVALUATES the guard
  at the candidate — after the ambient's own membership test — through the
  same routed calls every other spelling reaches (`predicateSetMethod?`, an
  elaboration decision like the powerset's); `nth` enumerates by TRIAL over
  the ambient's countable indexing, capped loudly at `predicateTrialCap`;
  cardinality refuses in `presCard`'s wording (a guard decides membership,
  not size); equality and inclusion refuse at `normalSubset`'s honest "no
  canonical form". The guard is stored AS WRITTEN and reads the session's
  bindings at query time — the spike's documented ceiling (SPEC.md never
  rebinds a name a stored guard mentions). Candidates of an ℕ-comprehension
  present as elements of ℤ — SPEC.md's own "plain numbers are naturally
  elements of ZZ" — since ℕ declares no methods (the empty-ℕ-profile fork
  is cas#29).

- **Membership is admitted in GUARD position, one relation in one
  production (ruling 2026-07-31, #31 item 6).** SPEC.md §Ellipses writes
  `{n in ℕ | f(n) ∈ 2ℕ}`; the `casMemFilterSet` production admits `∈` after
  the bar — the root set's discipline for `=` — and desugars it to the
  `contains` call it means, so the guard is decided by the same routed
  membership every other spelling of `∈` reaches, and the set presents
  lazily as above.

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
- **The three `SPEC.md` §Ellipses lines this section once ledgered are
  COVERED (rulings 2026-07-31, #31 items 6 and 7).** `2ℕ` is the image of
  the scaling map (§Sets); `{n in ℕ | f(n) ∈ 2ℕ}` parses — `∈` is admitted
  in guard position by its one production and desugars to `contains`
  (§Sets) — and presents lazily; `{n in ℕ | n.is_prime()}` presents lazily
  by its guard. The lazy fallback replaces the former undecidable-guard
  refusal wherever the head is the binder and the guard probes to a truth
  value; a guard the bound extraction reads — including the infinite and
  constant cases — still decides or refuses in the same structured words.
- **`m2.image()` is the one method functions own** (`FunctionElems`,
  registered because what a map does to a whole set is a computability
  question; SPEC's doubling map is spelled `m2` since the e-reservation
  ruling), and `m2(ℕ)` — applying a function to its SOURCE — desugars to it,
  so there is one implementation and two spellings. Applying a function to
  any other set is refused. The image of a linear map on ℕ is returned as
  `Value.progV`, the second shape an executor may return as a set: like
  `setV` it is reflected by `Denote.ofValue` into the ordinary
  `SetPresentation`, so `e.image()`, `e(ℕ)`, `{2n | n ∈ ℕ}` and
  `{0, 2, 4, …}` are all the same set object.

## Homs are first-class (owner ruling, 2026-07-31)

A linear map is NOT a matrix. For finitely presented modules over a PID a
morphism is a map from generators to generators that preserves relations;
in the free case (or over a field) there is a map `Mat_n(R) → Hom_R(V, W)`,
and it is not an isomorphism — many matrices present one map, and the
identification becomes an isomorphism only in the separate category of
FRAMED modules (modules with a chosen generating set, in which the map has
a unique matrix). The owner's ruling for this system, verbatim in effect:
homs are first-class categorical entities; matrices are EXTRACTED and
derived from them, and most of the actual matrix work is a backend
concern. Constructing a matrix in the DSL constructs an element of
`Mat_n(R)` — a point of that space, presenting no morphism, bilinear form
or anything else until SPECIFIED. Consequences for the shipped surface,
recorded so they are read the right way: `M * v` and `M.ker()` read
through the canonical specification map `Mat_n(R) → End(Rⁿ)` that the
STANDARD frame of `Rⁿ` provides — the frame choice is in the spelling,
exactly as `√d`'s branch is (§Open questions, embedding choices), not
silent. A future multi-binder morphism (`(x,y,z) ↦ (2x+3y+z, x−y, 3z−x)
in QQ-Mod`) is a HOM value presented the way the mathematician wrote it —
images of a general element, equivalently of the generators — with its
matrix in a frame a DERIVED presentation, never the entity itself. The
finitely-presented-over-a-PID general case (generators + relations) is
CategoryGraph-era ontology; nothing in the spike may pre-commit against
it by identifying homs with matrices.

THE TIER-1 SLICE SHIPPED (owner go, 2026-07-31): `Value.hom` is the
first-class value — domain, codomain, binders, and the map as written,
with its standard-frame rows DERIVED data. A multi-binder lambda whose
body is LINEAR in its binders elaborates to one (`evalHomBinding`, via the
structural `linearRow` reader); it is called on points of its domain,
composed (`∘` — the rows compose as the matrix product), compared (binders
are bound names and do not decide), and read by `ker`/`im` — methods a
`HomElems` category owns, routed natively to the same `rref`/`kernelGens`/
`mkSpanBasis` machinery every subspace presentation uses, so SPEC.md's
`assert W = ker φ` is decided by basis equality. The image of a map INTO ℚ
has no span presentation (spans are hard-wired to ℚⁿ) and refuses by name.
A NONLINEAR or affine body keeps the disclosed tier-2 refusal verbatim.
HELD boundary, deliberately: a hom is not ascribable `in Mod(QQ)` (it is
a MORPHISM of that category, not an object — the ontology CategoryGraph
owns). The owner's `Mod(QQ)`/`QQ^n` spellings are PINNED (2026-07-31, the
four spelling pins — §Surface): `Mod(K)` is the canonical category
spelling with `K-Mod` its alias, and `QQ^n` denotes ℚⁿ.

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
- **SPEC.md's `φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c` and `W = ker φ` are
  CLOSED** (tier-1 hom slice, 2026-07-31 — §Homs are first-class): φ binds
  as a first-class hom, `ker φ` presents its kernel through the same span
  normal form, and the equality is basis equality. The residue is exactly
  the NONLINEAR multi-binder body — polynomial maps in several variables —
  which keeps the disclosed-gap refusal (tier 2, #31, held for #13 demand).
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
Same method, same route, same backend, one implementation — and since the
production is SET-builder notation, the multiset the method answers
collapses to its support here: the solution SET.

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

## Categories (`Category.lean`, `Registry.lean`) — the TRANSITIONAL registry

**Status (2026-08-05 review, issue #35).** The categorical semantic layer is
owned upstream: the requirements catalogue is lean-lattices#56, and the
pinned consumer contract is lean-lattices#49. When #49 lands, this repo's
`CatDecl`/parents registry is **deleted, not refactored** — categories
become citations of catalogue entries, and any construct the catalogue
omits becomes a build failure. Until then the registry below is
transitional: frozen in shape, tethered to Mathlib at every claim it still
makes, and honest about the residue it cannot state (e.g. a multiset —
`p.roots()`'s result — profiles at `Sets` for its `∈`/`=`/`⊆`/`|·|`
methods although a multiset is not a set, and Σ/Π over a bare multiset is
not presentable here; the catalogue gives it its own entry).

```lean
inductive ParamVal | dom (d : Domain) | nat (n : Nat)

structure CatRef where
  name   : Name              -- inheritance graph node
  params : Array ParamVal    -- instantiation data, preserved along edges
```

- The **inheritance graph** is on category *names*: a `CatDecl` registers
  `parents : Array Name`; params pass through unchanged along an edge
  (`SmallModules(ℤ) ≤ Modules(ℤ)` because `SmallModules ≤ Modules`).
- A `CatDecl` carries a **telescope** — the Mathlib classes its membership
  MEANS, in dependency order. Registering an object into a category
  elaborates each class at the object's denoted type
  (`CasDsl/Mathlib/Denote.lean` is the single by-fiat presentation-tag ↦
  Lean-type bridge), so a membership the classes cannot discharge fails
  the build; a registered inclusion edge must likewise be an implication
  Mathlib discharges. An empty telescope is honest only for `Sets` and for
  nodes slated for re-anchoring or deletion at the migration.
- An object's **profile** is the set of `CatRef`s it directly inhabits
  (computed by `Std.profileOf : Obj → Array CatRef`); the resolver closes
  over parent edges. Profiles are rich: `ℤ` enters with sets, countable
  sets, commutative rings, euclidean domains, … — never one weakest class.
- **Method declarations** are category-owned:

```lean
structure MethodDecl where
  id          : Name       -- stable mathematical identity, e.g. `factor
  receiver    : Name       -- receiver category NAME (any params)
  argDoc      : String     -- slice keeps arg validation at execution
  resultDoc   : String
  doc         : String
  anchor      : Name       -- the Mathlib constant the answer is an answer TO
  conventions : String     -- presentation choices vs the anchor, stated
  advisory    : String     -- advice template for an unexpected-but-true result
```

  No method declaration names a backend, algorithm, or capability limit.
  The **anchor** is checked to exist at registration; `.anonymous` is
  permitted only where Mathlib holds no carrier, and `conventions` must
  then say so. A **convention chooses presentations** (display order, unit
  normalization, chosen basis), never the value of a well-defined
  predicate. The **advisory** text lives at the declaration; the method's
  own semantics decide when it fires and fill the `{…}` placeholders
  (`roots`' does-not-split note is the one producer today).

- **Routes** live in a *separate* registry (the computability layer):

```lean
structure Route where
  method   : Name
  pattern  : PresPattern     -- first-order matcher on the receiver Obj
  backend  : Name            -- `native or `sage (executor looked up by name)
  opId     : String          -- backend operation identity
  priority : Nat             -- deterministic tie-break: highest wins, tie = error
  doc      : String          -- rendered by the diagnostics
  docUrl   : String          -- source/docs link, rendered by the diagnostics
```

  Op signatures (`OpSig`) carry `doc`/`docUrl` and a provider-owned
  `advisory` the evaluator pushes generically with the op's results
  (Sage's fixed QQbar ↪ ℂ embedding disclosure rides the ℂ[x] ops this
  way — registration data, no advisory text in `Eval.lean`).

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

**The walk proposes; Mathlib disposes (runtime tripwire, 944f248).** Every
method call re-verifies the entry category's membership against Mathlib
(`verifyResolution` synthesizes the declaring category's telescope at the
concrete receiver's denoted type). A resolution the graph walk produces
that Lean cannot re-derive is reported as a registration defect — never
executed and never repaired in place. This is invariant I7 of
SPEC-REGISTRY-TYPE-PREPASS and survives the #49 migration unchanged.

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
q := map p to ℂ[x]                        -- bare `:=` — the same binding, no `let`
let X := {0, 1, 2, ...}                   -- progression set literals
let M := [1, 2; 3, 4] in Mat₂(ℚ)          -- matrix literal
let v := (1, 2) in ℚ²                     -- vector literal, and the Eⁿ domain
M*v   M v   M⁻¹ b   M(M⁻¹ b)              -- the action, in SPEC.md's spellings
M.rank()   M.ker()   M.trace()   M.charpoly()   r.companion_matrix()
let W := span_QQ{u₁, u₂} \leq ℚ³ in QQ-Mod  -- the subobject ascription
W.dim()   (1, 1, 2) ∈ W                   -- a subspace is a set with a dim
let φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c    -- a first-class HOM (linear body)
assert W = ker φ    φ((1, 1, 2))          -- its kernel, and a call; `im` for
                                          --   maps into ℚᵐ (a span lives in ℚⁿ)
∑_{a ∈ roots} a    ∏_{a ∈ roots} a        -- aggregation over a finite set
{a ∈ ℂ | r(a) = 0}                        -- the root set of an equation
let z := 2 + 2i in ℂ                      -- exact algebraic value; `i` is a constant
map √2 to ℝ/O(1/10^{10})                  -- a requested tolerance, not a quotient
√2   2√2   z.re()  z.im()  z.bar()  |z|   -- one square root over ℚ, exactly
let h := t ↦ t² + 1 in ℝ → ℝ              -- function, lambda spelling
let f(t) = t^2 in RR->RR                  -- …and the f(t) spelling, ASCII
let e: ℕ → ℕ := n ↦ 2n                    -- leading-ascription spelling
n.factor()   M.det()   M.inverse()  F.annihilator()   X.cardinality()
(360).factor()                            -- a parenthesized receiver takes a method
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
assert X = \NN        assert 7/3 \in ℚ    -- the backslash family, beside unicode
let f: NN -> NN := n ↦ n^2                -- …and the doubled-letter idents
assert R.dimension() is 10                -- `is` is a relation spelling of `=`
{n ∈ ℤ | n² ≤ 20}   {2n | n ∈ ℕ}   {m2(n) | n ∈ ℕ, 0 ≤ n < 6}
m2(ℕ)   m2.image()                        -- the image, one method two spellings
#explain_route <expr>   #capabilities   #capability_gaps
```

### The grammar on one page

Two word classes beyond Lean's own tokens, both PINNED as data
(`Syntax.reservedWords` / `Syntax.nonReservedKeywords`) and held to the
grammar by the parse guard in `CasDslTests/Core.lean`:

- **Reserved words — six, and that is the complete list**: `dx` (the
  differential atom, the 1-form `p dx`, `∫ f dx`), `Spec`, `lim_`
  (underscore included, lexically), `map`/`to` (the `map e to D`
  coercion — reserved by that production, a price the original three-word
  disclosure missed), and `is` (the relation spelling of `=`, a token
  reluctantly — the ruled non-reserved form leads a `casRel` category
  production, which the leading-ident dispatch never tries; the `Spec`
  lore, observed again). Each is a real token: an identifier by that
  spelling cannot be written ANYWHERE, including as a binding name, and the
  refusal is the parser's own. A segment merely CONTAINING one
  (`is_prime`) is untouched — tokens match whole identifier runs.
- **Non-reserved keywords**: `and` (chains assertions), `O` (tolerance and
  truncation), `dt` (the definite integral's variable), `span_QQ`
  (name-checked in `toExpr`). Ordinary identifiers everywhere else.
  Constants come in two kinds (ruling 2026-07-31, #31 item 3): `π` and `d`,
  and the ASCII domain names (`R`, `RR`, `CC`, and — #31 item 5 — the
  uniform doubled-letter family `NN`, `ZZ`, `QQ`), are SPELLINGS a binding
  always shadows; `e` (Euler's constant) and `i` (the imaginary unit) are
  **reserved symbols** no binding or binder may shadow — enforced where a
  name is INTRODUCED (`reservedConstantMsg?` in `bindObj` and every binder
  position), not by the tokenizer, so `is_prime` and `e1` still lex.

### The four spelling pins (owner rulings, 2026-07-31, #31)

The multivariable examples embedded four spellings, pinned before either
tier ships so both tiers share one vocabulary:

- **`|->` (and `\mapsto`) is the ASCII `↦`** — three alternatives on the one
  `casLam` production. `->` stays the domain arrow ONLY: one symbol, one
  meaning, no shape-based disambiguation.
- **`Mod(QQ)` is the CANONICAL module-category spelling**, `QQ-Mod` its
  accepted alias (SPEC's span line was edited to the canonical form). The
  REGISTERED Lean name stays the ASCII `«QQ-Mod»` — a Lean name cannot be
  spelled `Mod(ℚ)`, the `Schemes/QQ` situation exactly — with
  `categoryAscription?` resolving both input spellings and `renderName`
  displaying `Mod(ℚ)` everywhere.
- **The clean `^` split**: a DOMAIN base with a positive numeral exponent
  denotes the product space (`QQ^3` IS ℚ³ — the `Eval` denotation ℚ³'s
  superscript spelling already had), while a numeral 2 base with a set
  exponent stays the powerset (`2^ℤ` ≡ `𝒫(ℤ)`). Both halves are SPEC's own.
- **`AA^n(K)` is THE affine-space spelling**, held for #13 demand: it
  parses through the ordinary `^`/application grammar and refuses BY NAME
  at evaluation (a bound `AA` still wins, as a binding wins over a
  constant). Tier 2 — polynomial maps on AA^n — stays behind it.

Precedence, tightest first (`casTerm:N`, higher binds tighter):

| level | productions |
|---|---|
| max   | atoms — literals, `(…)`, set/matrix/vector braces, `\|A\|`, `√x`, `𝒫(A)`, `∫ f dx`, `lim_{…}`, `Spec R`, comprehensions, `∑`/`∏`, and the implicit product `2x`/`3x²` (numeral against a `:76` atom-or-power) |
| 80–81 | `^` (right-associative) and the one-digit superscripts; `x^{k}` reads a braced exponent |
| 75    | `∘`, unary `-` |
| 70–71 | `*` `·` `/` `∩` `×`; juxtaposition application `M v`, `M⁻¹ b` (ident-rooted); the 1-form `p dx` |
| 65–66 | `+` `-` `∪` `\` `△` |
| 50    | `≤ < ≥ >`, and three-term chains |
| 25    | `→` / `->` function domains |
| 20    | `map e to D` |
| 10    | `t ↦ body` |

`assert` relations (`=` `≠` `∈`/`in` `∉` `⊆`) sit OUTSIDE the term grammar,
and `and` joins whole assertions, never terms. The one rule a reader must
know before anything surprises them: **ident-follows-ident is application**
(`casJuxtApp`, level 70) — its next-line swallow residual and the two
rejected fixes are the parser-decision bullet below and the ledger (#24).

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
  lines, so nothing here can require "the same line" — and owned by issue #27
  (with both rejected fixes recorded there);
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
  error is only a confusing one, so it is not a contained fix. Owned by issue
  #27 with the juxtaposition residual it belongs to;
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
- **the backslash family is UNIFORM** (ruling 2026-07-31, #31 item 5): a
  unicode token's LaTeX spelling is accepted wherever the unicode form
  goes. Coverage: `\NN` `\ZZ` `\QQ` `\RR` `\CC` beside the five domain
  tokens, `\in` beside every `∈` (assert relation, comprehension binder,
  the `let f(t) = … ∈ D` ascription), and `\leq` — which predates the
  ruling — beside `≤`. An addition is declared beside its unicode token,
  same pattern. `is` belongs to the same SPEC §Ellipses block ("`is` just
  means `=`") and is the sixth reserved word (see above);
- **`and` chains ASSERTIONS, not terms.** SPEC.md's ⊆-chain is three claims,
  each decided on its own, under one ambient `in D`; the first that is not
  true stops the cell NAMING ITSELF, so a chain never reports "false" without
  saying which link was. It is a non-reserved keyword (`&"and"`), so `and`
  remains an ordinary identifier everywhere else;
- **a PARENTHESIZED receiver takes a method** — `(360).factor()` (ruling
  2026-07-31, #31 item 1). The literal `360.factor()` SPEC.md first wrote is
  a Lean-TOKENIZER casualty: the lexer eats `360.` as a decimal before any
  production can see it, so no grammar here can admit it, and SPEC L12 was
  edited to the parenthesized spelling under the ruling. `casApply` reaches
  a method through the DOTTED NAME the `ident` lexer produces
  (`n.factor` is ONE token), which a parenthesized receiver never is —
  hence `casParenMethod`, resolving the method on the receiver's VALUE
  through the same `.method` node. The prefix spelling below remains the
  same call;
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
- a bare proposition cell (a `casAssertion` with no command word) displays
  its truth value — `true | false | unknown` — the same low-priority display
  convention as the bare term cell; `assert` is the collapsing form and
  commits only on `true`;
- **a bare `NAME := expr [in D]` is the `let` binding without the word**
  (ruling 2026-07-31, #31 item 2): SPEC.md's opening sentence says
  "Definitions use :=" and its §Polynomials line `q := map p to ℂ[x]` writes
  one with no `let`. One production (`casDef`), the SAME elaborator and
  checked ascription as `let`, low priority like the display cell;
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

Textual on purpose (no `text/latex` — `logInfo` lines): assertion
check-marks, every diagnostic (`#explain_route`, `#capabilities`,
`#capability_gaps`, `#canonical_maps` keep their `text/plain` + `vnd`
bundle), capability-gap refusals, and all error messages.

One emission per event. A cell result, a bare proposition's truth value, and
the binding echo `h := t ↦ t² + 1 ∈ ℝ → ℝ` each emit exactly ONE MIME bundle
and no `logInfo` duplicate: the frontend shows `text/latex` when the bundle
carries it and `text/plain` otherwise, so LaTeX replaces the plain text
rather than appearing beside it — Sage's convention.

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
three per the user-decided closure paths, #17/#18; the enumerations of ℤ
and ℚ are Mathlib's `Denumerable` order, adopted verbatim — 2026-08-05
ruling, #35.)

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
- **enumeration of ℚ**: SUPERSEDED (2026-08-05 ruling, #35) — Mathlib's
  `Denumerable` order is adopted verbatim for ℤ and ℚ (`nth` calls
  `Denumerable.ofNat`); no CasDsl-owned enumeration exists (originally the
  Cantor zigzag, #17);
- **`factor` on ℤ[x]**: routed via Sage, content × primitive (#18) — the
  `map p to ℚ[x]` demo stays, reframed as the canonical-map demo;
- **route/op agreement**: checked at build time via registered op
  signatures, not left to runtime defensive arms (see §Routing and gaps).

## Embedding choices are logged at use (owner ruling, 2026-07-31, #31 item 10)

Passing to a larger field rides on CHOICES the mathematics does not make for
us: entire Galois groups and class groups govern field embeddings, and a DSL
that picks one silently is dangerous unless the choice is logged (owner's
words). RULED: a choice-carrying map **LOGS its choice at use**, on the notes
channel — the owner-sanctioned advisory surface — never silently and never
as default output. The declare-at-registration alternative (a declared-choice
field on `CanonicalMap`, constructions refusing until a choice is named) is
FAMILY MANAGEMENT — precisely the CategoryGraph cut — and stays deferred to
the foundations rewrite.

The two flows that carry a choice today, and their notes:

- **`√d`** denotes ONE root by convention — the non-negative branch for a
  positive radicand (`nonNegSurd`), `i·√|d|` upward for a negative one — and
  the `.sqrt` evaluation pushes a note saying so whenever the result is
  algebraic (a rational root is ordinary arithmetic and gets none);
- **`QQbar ↪ ℂ`**: all exact algebraic arithmetic rides Sage's one fixed
  embedding (`enc_alg` settles conjugates by exact QQbar comparison), and the
  ℂ[x] `roots`/`factor` calls — where complex algebraic results actually
  surface — push a note naming it (`embeddingNote`).

The prelude's chain ℕ ⊆ ℤ ⊆ ℚ ⊆ ℝ ⊆ ℂ is made of maps that are unique, so
no other non-canonical choice is being made yet; when splitting fields,
abstract number fields or Galois-orbit root sets arrive, their choices join
the log-at-use discipline (or force the registry question at CategoryGraph).

## Governing rulings (2026-08-05 review — this file is the owner)

Recorded on issue #35 until this section landed; #35 now points here.

1. **Elaborated claims only.** A semantic claim the registry makes must be
   an elaborated Mathlib term — a claim Lean cannot discharge fails the
   build. The **exact trusted boundary**: exactly one by-fiat
   correspondence exists (the codec's presentation-tag ↦ Lean-type bridge,
   `CasDsl/Mathlib/Denote.lean`), and backend-computed VALUES are the only
   other trusted residue; both are labeled as such where they live.
2. **The notation register.** The audience is a research mathematician:
   diagnostics render Lean-literate notation — the dependent signature
   over the declaring classes, the receiver's instance chain with Lean's
   live verdict, `≐` for the anchor, the implemented subcategory — never
   prose exposition of standard mathematics and never a dump of internal
   record fields. `#explain_route`, `#capabilities` and the gap rendering
   all speak it; `CasDslTests/Wording.lean` pins it verbatim.
3. **One emission per event** — per binding, result, and truth cell;
   LaTeX replaces plain text rather than stacking above it (§LaTeX-first
   display).
4. **Conventions choose presentations** (display order, unit
   normalization in rendering, chosen basis) — never the values of
   well-defined predicates. Hence the `is_prime` correction (7a6140c):
   (−7) is prime because (−7) = (7).
5. **The categorical semantic layer is owned upstream** (lean-lattices#56
   catalogue, #54 fibred-family idiom, #49 consumer contract): this
   repo's `CatDecl`/parents registry is transitional and gets deleted,
   not refactored, when #49 lands. Local tracking: issue #35.

## Open questions (kept open — do not silently resolve)

- ~~default enumeration convention for `ℤ`~~ RESOLVED (2026-08-05, #35):
  Mathlib's `Denumerable` order adopted verbatim for ℤ and ℚ — 0, −1, 1,
  −2, 2, …;
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
  (§Vectors, matrices and subspaces), and a multi-binder lambda whose body
  is NOT linear in its binders — a polynomial map in several variables — is
  a disclosed gap that names itself (the linear case is the tier-1 hom
  slice, §Homs are first-class);
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
