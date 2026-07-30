/-
Elaboration-time tests for the surface layer.

Two halves: `#guard` over the evaluator's PURE core (polynomial arithmetic,
canonical embeddings, progression construction, the `D[x]`-vs-`e[k]`
disambiguation, the `Matₙ` spelling), and a parser/command smoke that
exercises every command form — arithmetic assertions, bindings, ascriptions,
the polynomial binder, `map`, and a bare expression cell — plus the proof
that an ordinary Lean command in a cell still elaborates as Lean.

The coercions here are REGISTRY-driven (`CasDsl/Category.lean`'s
`CanonicalMap`), so the pure guards below carry their own rule array and the
command smoke needs the prelude's registrations: hence the import of the
standard universe. `CasDslTests/CanonicalMaps.lean` owns the claims about the
registry itself.
-/
import CasDsl.Diagnostics
import CasDsl.Std

namespace CasDslTests

open Lean (Name)
open CasDsl

/-- The canonical injections of the standard universe, spelled out so every
guard below is a pure claim about the coercion layer: polynomial arithmetic
joins coefficient domains through these rules too. -/
private def embeds : Array CanonicalMap := #[
  { src := .exact .nat, tgt := .exact .int, op := .identity },
  { src := .exact .nat, tgt := .exact .rat, op := .intToRat },
  { src := .exact .int, tgt := .exact .rat, op := .intToRat },
  { src := .exact .int, tgt := .anyMod, op := .intToMod }
]

/-! ## Polynomial arithmetic -/

private def x : Array Value := #[.int 0, .int 1]

#guard (polyAdd #[.int 1, .int 2] #[.int 3]).toOption == some #[.int 4, .int 2]
#guard (polySub #[.int 1] #[.int 1, .int 5]).toOption == some #[.int 0, .int (-5)]
-- (1 + 2x)(1 + 3x) = 1 + 5x + 6x²
#guard (polyMul #[.int 1, .int 2] #[.int 1, .int 3]).toOption
  == some #[.int 1, .int 5, .int 6]
#guard (polyMul #[] #[.int 1]).toOption == some #[]
#guard (polyPow x 3).toOption == some #[.int 0, .int 0, .int 0, .int 1]
#guard (polyPow x 0).toOption == some #[.int 1]
-- ℤ coefficients meeting ℚ coefficients promote pointwise
#guard (polyAdd #[.int 1] #[.rat (1/2)]).toOption == some #[.rat (3/2)]

/-- The notebook's `x^3 - 2x + 1`, evaluated as the surface evaluator does. -/
private def cubic : Except String Value := do
  let xv := Value.mkPoly .int x
  let x3 ← valueBin embeds .pow xv (.int 3)
  let lin ← valueBin embeds .mul (.int 2) xv
  valueBin embeds .add (← valueBin embeds .sub x3 lin) (.int 1)

#guard cubic.toOption
  == some (Value.poly .int #[.int 1, .int (-2), .int 0, .int 1])
#guard cubic.toOption.map (·.render) == some "x^3 - 2x + 1"

-- a polynomial call is exact and promotes: p(1) = 0
#guard (do Native.polyEval .int #[.int 1, .int (-2), .int 0, .int 1] (.int 1)).toOption
  == some (Value.int 0)

/-! ## Canonical embeddings (`map … to`, and ascription)

The rules are spelled out here rather than read from the registry, so these
stay pure `#guard`s over the coercion layer. That the prelude registers the
same ones — and that an EMPTY registry makes these coercions fail — is
`CasDslTests/CanonicalMaps.lean`'s business. -/

#guard (coerceValue embeds .rat (.int 3)).toOption == some (Value.rat 3)
#guard (coerceValue embeds (.mod 5) (.int 7)).toOption == some (Value.mod 5 2)
#guard (coerceValue embeds (.poly .rat) (.poly .int #[.int 1, .int 2])).toOption
  == some (Value.poly .rat #[.rat 1, .rat 2])
#guard (coerceValue embeds (.poly .int) (.int 4)).toOption
  == some (Value.poly .int #[.int 4])
#guard (coerceValue embeds (.matrix 2 .rat)
    (.mat 2 .int #[#[.int 1, .int 2], #[.int 3, .int 4]])).toOption
  == some (Value.mat 2 .rat #[#[.rat 1, .rat 2], #[.rat 3, .rat 4]])
-- a vector coerces COMPONENT-WISE, exactly as a matrix does entry-wise…
#guard (coerceValue embeds (.vector 2 .rat) (.vec 2 .int #[.int 1, .int 2])).toOption
  == some (Value.vec 2 .rat #[.rat 1, .rat 2])
-- …and the LENGTH is not something a coercion may change
#guard (coerceValue embeds (.vector 3 .rat) (.vec 2 .int #[.int 1, .int 2])).toOption
  == none
-- ℚ → ℤ is not an embedding, and is not invented
#guard (coerceValue embeds .int (.rat (1/2))).toOption == none
#guard (coerceValue embeds .nat (.int (-1))).toOption == none

#guard (domJoin embeds .int .rat).toOption == some (some .rat)
#guard (domJoin embeds (.poly .int) (.poly .rat)).toOption
  == some (some (.poly .rat))
-- `some none` = no canonical join; a bare `none` would be a REGISTRY DEFECT
#guard (domJoin embeds (.mod 4) (.mod 5)).toOption == some none

/-! ## Progression literals: the step is inferred, and then CHECKED -/

#guard (progressionOf embeds #[.int 0, .int 1, .int 2] none).toOption
  == some (SetPresentation.arithProg .int (.int 0) (.int 1) none)
#guard (progressionOf embeds #[.int 0, .int 2, .int 4] none).toOption
  == some (SetPresentation.arithProg .int (.int 0) (.int 2) none)
-- one leading element means step 1 (the Haskell `{a, ...}` reading)
#guard (progressionOf embeds #[.int 5] none).toOption
  == some (SetPresentation.arithProg .int (.int 5) (.int 1) none)
#guard (progressionOf embeds #[.int 1, .int 3] (some (.int 9))).toOption
  == some (SetPresentation.arithProg .int (.int 1) (.int 2) (some (.int 9)))
-- a literal that is not a progression is a mistake, not a set to guess at
#guard (progressionOf embeds #[.int 0, .int 2, .int 5] none).toOption == none

#guard (elemsDomain embeds #[.int 1, .rat (1/2)]).toOption == some .rat

/-! ## Functions

SPEC.md's function claims are identities of function EXPRESSIONS, so the pure
core is where they are decided: `applyPoly` substitutes a polynomial argument
into a polynomial body, which settles `h(-t) = h(t)` and `(f ∘ g)(t) = t⁶`
exactly, and evaluates ordinary points by the same Horner pass. -/

/-- `t ↦ t² + 1` — the body of SPEC.md's `h`, both spellings of which must
normalize to it. -/
private def sq1 : Value := Value.mkPoly .int #[.int 1, .int 0, .int 1]

private def xTo (k : Nat) : Value :=
  Value.mkPoly .int ((Array.replicate k (Value.int 0)).push (.int 1))

-- a scalar argument evaluates: h(0) = 1, h(3) = 10
#guard (applyPoly embeds sq1 (.int 0)).toOption == some (.int 1)
#guard (applyPoly embeds sq1 (.int 3)).toOption == some (.int 10)
-- a polynomial argument SUBSTITUTES: h(-t) is h(t), not a sample of it
#guard (applyPoly embeds sq1 (Value.mkPoly .int #[.int 0, .int (-1)])).toOption
  == some sq1
#guard (applyPoly embeds sq1 (xTo 1)).toOption == some sq1
-- and a genuinely different argument is a genuinely different body
#guard (applyPoly embeds sq1 (Value.mkPoly .int #[.int 1, .int 1])).toOption
  == some (Value.mkPoly .int #[.int 2, .int 2, .int 1])
-- a body the polynomial engine cannot read is refused, never approximated
#guard (applyPoly embeds (.bool true) (.int 0)).toOption == none

/-- `t ↦ tᵏ in ℝ → ℝ`. -/
private def pow (binder : Name) (k : Nat) : Value := .func .real .real binder (xTo k)

-- (f ∘ g)(t) = t⁶ from f = t², g = t³ — and the composite keeps g's binder
#guard (composeFuncs embeds (pow `t 2) (pow `s 3)).toOption == some (pow `s 6)

/-- `t ↦ t + 1 in ℝ → ℝ` — the shift, whose two composites with `t²` differ. -/
private def shift : Value := .func .real .real `t (Value.mkPoly .int #[.int 1, .int 1])

-- the order is substitution order, not an unordered pairing: (t + 1)² is the
-- one composite and t² + 1 the other
#guard (composeFuncs embeds (pow `t 2) shift).toOption
  == some (.func .real .real `t (Value.mkPoly .int #[.int 1, .int 2, .int 1]))
#guard (composeFuncs embeds shift (pow `t 2)).toOption
  == some (.func .real .real `t (Value.mkPoly .int #[.int 1, .int 0, .int 1]))
-- domains must meet: ℕ → ℕ followed by ℝ → ℝ does not compose
#guard (composeFuncs embeds (pow `t 2) (.func .nat .nat `s (xTo 3))).toOption == none
#guard (composeFuncs embeds (pow `t 2) (.int 3)).toOption == none

/- These two used to read "ℝ admits no canonical map, so nothing lands in
it". That is no longer true of ℝ: the prelude registers the chain ℚ ⊆ ℝ ⊆ ℂ
and its closure (DESIGN.md §Coercions), so `let r := 3 in ℝ` succeeds and
`CasDslTests/CanonicalMaps.lean` pins the shipped registry. What the two
guards claim is what they always mechanically claimed — that this LOCAL rule
array has no rule into ℝ, and the coercion layer therefore refuses. The
change was deliberate; the pin below states its real subject. -/
#guard (coerceValue embeds .real (.int 3)).toOption == none
#guard (domJoin embeds .real .rat).toOption == some none
-- …and with the rule registered, the same call succeeds and moves NO data
#guard (coerceValue #[{ src := .exact .int, tgt := .exact .real, op := .identity }]
    .real (.int 3)).toOption == some (Value.int 3)

/-! ### The `src → tgt` ascription is checked at the call boundary -/

-- an argument outside the source domain is refused, not computed with
#guard (atDomain embeds .nat (.int (-1))).toOption == none
#guard (atDomain embeds .nat (.int 3)).toOption == some (.int 3)
-- …and a result lands IN the target: t + 3 at 4 is 2 in ℤ/5, never 7
#guard (atDomain embeds (.mod 5) (.int 7)).toOption == some (.mod 5 2)
-- an ℝ arrow passes through unchecked. NOT because ℝ has no elements — it has
-- them since the ℂ unit — but because a check there would re-tag the symbolic
-- path's ℤ[x] expression as ℝ[x] and restate SPEC.md's `(f ∘ g)(t) = t⁶` in
-- another ring (DESIGN.md §Functions). Kept deliberately, with the new reason
#guard (atDomain embeds .real (.int (-1))).toOption == some (.int (-1))
-- the symbolic path travels coefficient-wise, so it lands in the domain too:
-- `t + 7` reduces to `t + 2` over ℤ/5 instead of staying an unreduced ℤ poly
#guard (atDomain embeds (.mod 5) (Value.mkPoly .int #[.int 7, .int 1])).toOption
  == some (Value.mkPoly (.mod 5) #[.mod 5 2, .mod 5 1])
#guard (atDomain embeds .nat (xTo 1)).toOption
  == some (Value.mkPoly .nat #[.int 0, .int 1])
-- …in either path, which is what keeps the identity in ℤ[x] where it was stated
#guard (atDomain embeds .real (xTo 1)).toOption == some (xTo 1)

-- the binder is the indeterminate of the SOURCE domain; ℝ has no polynomial
-- ring of its own here — its inhabitants are the exact algebraic values, not
-- an indeterminate — so there the body's own ring stands in
#guard binderRing (.mod 5) (xTo 2) == some (.mod 5)
#guard binderRing .nat (xTo 2) == some .nat
#guard binderRing .real (xTo 2) == some .int
#guard binderRing .real (Value.mkPoly (.mod 5) #[.mod 5 3, .mod 5 1]) == some (.mod 5)
-- a body that is no polynomial has no such ring, and does not default to ℤ
#guard binderRing .real (.bool true) == none

-- the ℤ/n zero is a zero: a normal form that missed it would leave two equal
-- polynomials comparing unequal
#guard Value.mkPoly (.mod 5) #[.mod 5 1, .mod 5 0] == .poly (.mod 5) #[.mod 5 1]

-- `R` and `RR` are spellings of ℝ, `CC` of ℂ; every other identifier is a name
#guard domainAlias? `RR == some .real
#guard domainAlias? `R == some .real
#guard domainAlias? `CC == some .complex
#guard domainAlias? `Reals == none
-- the Unicode names are aliases too, for the receiver path: `ℝ.cardinality()`
-- lexes as ONE identifier, so a domain used as a method receiver arrives here
-- as a name and never as its own token
#guard domainAlias? `ℝ == some .real
#guard domainAlias? `ℂ == some .complex
#guard domainAlias? `ℤ == some .int
#guard domainAlias? `ℚ == some .rat
#guard domainAlias? `ℕ == some .nat

/-! ## Comprehension bounds

The decision procedure's core, as pure claims: the tail bound really does
put every root inside `±N`, and a guard whose tail SATISFIES it is reported
as unbounded rather than truncated. -/

#guard ratCeil (mkRat 7 2) == 4
#guard ratCeil (mkRat (-7) 2) == -3
#guard ratCeil (mkRat 4 2) == 2

/-- `n² − 20`, the difference SPEC.md's `n² ≤ 20` is rewritten to. -/
private def nSq20 : Array Value := #[.int (-20), .int 0, .int 1]

-- N = max(1, ⌈(S+1)/|a_d|⌉) = 21, and 21² − 20 > 0: no root is missed
#guard polyTailBound nSq20 == some 21
#guard polyTailBound #[.int 0, .int 1] == some 1
#guard polyTailBound #[.int (-6), .int 1] == some 7
-- a constant has no bound to extract, and neither has an unordered ring
#guard polyTailBound #[.int 3] == none
#guard polyTailBound #[.mod 5 1, .mod 5 1] == none

-- `n² ≤ 20` is bounded on both sides, and every solution lies inside
#guard (boundsOfPoly .le nSq20).toOption.map (fun b => (b.lo, b.hi))
  == some (some (-20), some 20)
-- `n² ≥ 20` satisfies BOTH tails: unbounded, and reported as such rather
-- than silently cut off at the bound
#guard (boundsOfPoly .ge nSq20).toOption.map (fun b => (b.lo, b.hi))
  == some (none, none)
-- `n ≥ 0` bounds below only, `n < 6` above only — and their meet is finite,
-- which is exactly what makes `0 ≤ n < 6` decidable
#guard (boundsOfPoly .ge #[.int 0, .int 1]).toOption.map (fun b => (b.lo, b.hi))
  == some (some 0, none)
#guard (boundsOfPoly .lt #[.int (-6), .int 1]).toOption.map (fun b => (b.lo, b.hi))
  == some (none, some 6)
#guard (BinderBounds.meet { lo := some 0 } { hi := some 6 }).lo == some 0
#guard (BinderBounds.meet { lo := some 0 } { hi := some 6 }).hi == some 6
#guard (BinderBounds.meet { lo := some 0 } { lo := some 3 }).lo == some 3
#guard (BinderBounds.meet { hi := some 9 } { hi := some 6 }).hi == some 6

/- A guard that does not mention the binder is a CONSTANT, and the two
answers it has are both decided: every candidate (unbounded, so the
comprehension is infinite and refused as such) or none (the EMPTY range,
which enumerates to `{}`). `0*n` and `n - n` reach this through the zero
polynomial, so the poly arm below degree 1 must land here too — diagnosing
them as a polynomial with no extractable bound reported an unsupported guard
where the honest answer was infinite. -/
#guard (constantBounds .le (.int 0)).toOption.map (fun b => (b.lo, b.hi))
  == some (none, none)
#guard (constantBounds .lt (.int 0)).toOption.map (fun b => (b.lo, b.hi))
  == some (some 0, some (-1))
#guard (constantBounds .le (.bool true)).toOption.isNone

/-! ## The image of a function (`SPEC.md`'s `e.image()`) -/

-- `n ↦ 2n` on ℕ: the image IS the progression `{0, 2, 4, ...}`
#guard (Native.run "func_image" Std.doubling #[]).toOption
  == some (Value.progV .nat (.int 0) (.int 2) none)
-- …and it reflects into the ordinary set object a literal produces
#guard (Denote.ofValue (.progV .nat (.int 0) (.int 2) none)).obj?
  == some (Obj.setObj (.arithProg .nat (.int 0) (.int 2) none))
-- a constant map images to the one value it takes
#guard (Native.run "func_image"
    (.elem (.funcs .nat .nat) (.func .nat .nat `n (.int 7))) #[]).toOption
  == some (Value.setV #[.int 7] .nat)
-- a quadratic image on ℕ is not a progression: a loud gap, never a guess
#guard (Native.run "func_image"
    (.elem (.funcs .nat .nat)
      (.func .nat .nat `n (Value.mkPoly .int #[.int 0, .int 0, .int 1]))) #[]).toOption
  == none
-- …and neither is a linear image on ℤ, which runs both ways
#guard (Native.run "func_image"
    (.elem (.funcs .int .int)
      (.func .int .int `n (Value.mkPoly .int #[.int 0, .int 2]))) #[]).toOption
  == none

/-! ## `D[x]` versus `e[k]`, and the `Matₙ` spelling -/

private def bound (n : Name) : Bool := n == `p

#guard indeterminate? bound (.ref `x) == some `x
#guard indeterminate? bound (.ref `p) == none        -- a binding: this is an index
#guard indeterminate? bound (.num 3) == none

#guard matSize? `Mat₂ == some 2
#guard matSize? `Mat₁₀ == some 10
#guard matSize? `Mat == none
#guard matSize? `Matrix == none
#guard matSize? `n.factor == none

/-! ## The `NoImplementation` contract

The gap rendering is what an audit greps for, so its shape is asserted
directly: the literal token, the method id, the presentation — and NOT the
word "unknown", which would misreport an execution-layer backlog item as a
mathematical failure. -/

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def qGap : CapabilityGap := {
  method := `nth
  receiverCategory := { name := `CountableSets, params := #[.dom .rat] }
  presentation := "ℚ"
  semanticVia := [`Sets]
  routesConsidered := #[
    { method := `nth, pattern := .domainIs (.exact .int), backend := `native,
      opId := "nth", priority := 10 }]
}

#guard contains (renderGap qGap) "NoImplementation"
#guard contains (renderGap qGap) "nth"
#guard contains (renderGap qGap) "ℚ"
#guard contains (renderGap qGap) "routes considered: 1"
#guard !contains (renderGap qGap).toLower "unknown"
-- the inheritance chain that made the method available is reported as such
#guard contains (renderGap qGap) "inherited through CountableSets(ℚ) ≤ Sets"
#guard renderVia { name := `MatrixElems, params := #[.nat 2, .dom .rat] } []
  == "declared directly on MatrixElems(2, ℚ)"

/-- `e` is refused, in words containing `needle`. A refusal is only worth
pinning by what it SAYS: each one below distinguishes itself from a
neighbouring failure the user must not confuse it with. -/
private def refuses (env : Lean.Environment) (e : CasExpr) (needle : String)
    : Lean.Elab.Command.CommandElabM Unit := do
  match ← runEval { env } e with
  | .ok d => throwError s!"expected a refusal containing {repr needle}, got {d.render}"
  | .error err =>
      unless (err.render.splitOn needle).length > 1 do
        throwError s!"the refusal was worded {repr err.render}, expected {repr needle}"

/-! ## Command smoke

Scalar equality is `Native.valueEq`; the coercions in `map p to ℚ[x]` and in
the Mat₂(ℚ) ascription come from the imported standard universe's registered
embeddings. -/

assert 2 + 3 = 5
assert 2 + 3 = 0 in ℤ/5
assert 1 / 2 ≠ 1
assert -2 + 2 = 0

let n := 360 in ℤ
let S := {1, 2, 3}
let X := {0, 1, 2, ...}
let B := {1, 3, ..., 9}
let M := [1, 2; 3, 4] in Mat₂(ℚ)
let p(x) := x^3 - 2x + 1 in ℤ[x]
let q := map p to ℚ[x]

assert q(1) = 0
assert p(2) = 5

-- a bare expression cell displays its value
2 + 3
q

/-! ## SPEC.md's Functions section, verbatim

Every line of the section runs here, so a false assertion fails the build
rather than the notebook. Both binder spellings and both domain spellings are
exercised, and `assert h = hp` is the claim that they agree. -/

let h := t ↦ t² + 1 in ℝ → ℝ
let hp(t) := t^2 + 1 in R->R
assert h = hp
assert h(0) = 1
assert h(3) = 10
assert h(-t) = h(t)

/-! ## SPEC.md §Elementary calculus: a body the polynomial engine cannot express

Placed HERE, above `let e := …`, and that placement is the point: `e` is
Euler's number only while nothing has bound the name, and SPEC.md itself binds
it to the doubling map two lines down. A binding wins over a constant — the
rule `i` and `R` already follow — so the collision is SPEC.md's own, and it is
pinned below as a live refusal rather than described.

These bodies are SYMBOLIC: they are presented so a backend can take a limit, a
definite integral or a Taylor expansion of them, and this slice decides
NOTHING about them — no value at a point, no identity between two of them.
That is the U1 gap closing, and closing to exactly this much. -/

let expo := t ↦ e^t in ℝ → ℝ
let sine: ℝ → ℝ := t ↦ sin(t)
let recip := t ↦ 1/t in ℝ → ℝ

-- the polynomial reading is preferred where it applies, so a polynomial body
-- is untouched by any of this: `h` above is still a polynomial and still
-- decides its identity
assert h(-t) = h(t)

let e: ℕ → ℕ := n ↦ 2n

-- …and with the name bound, SPEC.md's own `e^t` reads the BINDING. The
-- constant loses, which is the documented rule, and `exp(t)` is the spelling
-- no binding can shadow
let expo2 := t ↦ exp(t) in ℝ → ℝ

let f(t) = t^2 in RR->RR
let g(t) = t^3 in RR->RR
assert (f ∘ g)(t) = t^6

-- the composite is a function like any other: it evaluates at a point, and
-- equality tells it apart from its factors
assert (f ∘ g)(2) = 64
assert h ≠ f

-- the ascribed domains are CHECKED at the call: the argument enters through
-- the source and the result lands in the target, so a ℤ/5 arrow computes in
-- ℤ/5 (4 + 3 = 2) rather than in ℤ
assert e(3) = 6
let k(t) = t + 7 in ℤ/5 → ℤ/5
assert k(4) = 1
-- the symbolic call reduces in ℤ/5 too, so the identity is decided there and
-- not in the ℤ the body was written in
assert k(t) = t + 2
assert k(t) ≠ t + 3

run_cmd do
  let env ← Lean.getEnv
  let expect : List (Name × String × String) :=
    [(`h, "t ↦ t^2 + 1", "t ↦ t^2 + 1 ∈ ℝ → ℝ"),
     (`hp, "t ↦ t^2 + 1", "t ↦ t^2 + 1 ∈ ℝ → ℝ"),
     (`e, "n ↦ 2n", "n ↦ 2n ∈ ℕ → ℕ"),
     (`g, "t ↦ t^3", "t ↦ t^3 ∈ ℝ → ℝ")]
  for (name, rendered, presented) in expect do
    match CasDsl.binding? env name with
    | none => throwError "'{name}' was not bound"
    | some o =>
        if o.render != rendered then
          throwError "'{name}' rendered as {o.render}, expected {rendered}"
        if o.presentation != presented then
          throwError "'{name}' presented as {o.presentation}, expected {presented}"
  -- the two spellings really are one value, binder included
  unless CasDsl.binding? env `h == CasDsl.binding? env `hp do
    throwError "the ↦ and f(t) spellings of the same function differ"

-- The bindings above really landed in the environment extension, and the
-- `let` command did not shadow `let` inside this `do` block.
run_cmd do
  let env ← Lean.getEnv
  let expect : List (Name × String) :=
    [(`n, "360"), (`S, "{1, 2, 3}"), (`X, "{0, 1, ...}"), (`B, "{1, 3, ..., 9}"),
     (`M, "[1, 2; 3, 4]"), (`p, "x^3 - 2x + 1"), (`q, "x^3 - 2x + 1")]
  for (name, rendered) in expect do
    match CasDsl.binding? env name with
    | none => throwError "'{name}' was not bound"
    | some o =>
        if o.render != rendered then
          throwError "'{name}' rendered as {o.render}, expected {rendered}"
  match CasDsl.binding? env `q with
  | some (.elem (.poly .rat) _) => pure ()
  | some o => throwError "map to ℚ[x] produced {o.presentation}"
  | none => throwError "'q' was not bound"

/-! ## SPEC.md's degree and polynomial-ring membership (#24)

The claims that need no backend are asserted here as surface commands, so a
false one fails the build. Their Sage-routed siblings — the VALUE of
`gcd(84, 30)` and the root sets — are pinned semantically by the routing
proofs in `CasDsl/Std.lean` and executed against the real adapter by
`tests/roundtrip.py` and `tests/test_e2e.py`: this build stays backend-free,
as it was before. -/

-- the degree is a native structural read of the coefficient array
#guard (Native.run "poly_deg" Std.polyZ #[]).toOption == some (Value.int 3)
#guard (Native.run "poly_deg" (.elem (.poly .rat) (Value.mkPoly .rat #[.rat 7])) #[]).toOption
  == some (Value.int 0)
-- …and the zero polynomial is refused rather than given a conventional one
#guard (Native.run "poly_deg" (.elem (.poly .int) (Value.mkPoly .int #[])) #[]).toOption
  == none

-- SPEC.md §Polynomials: the bare indeterminate is an element of its own ring
assert x ∈ ℤ[x]
-- …and so is the polynomial its binder defined
assert p ∈ ℤ[x]
-- ℤ[x] sits in ℚ[x] for the reason ℤ sits in ℚ — coefficient by coefficient
assert p ∈ ℚ[x]
-- membership is a judgment about the coefficients, not a shape test
assert 1 / 2 ∉ ℤ[x]
assert 1 / 2 ∈ ℚ[x]
-- …coefficient by coefficient, which is the POLYNOMIAL case rather than the
-- scalar one above: one non-integral coefficient keeps `x + 1/2` out of ℤ[x]
let r := x ↦ x + 1 / 2 in ℚ[x]
assert r ∉ ℤ[x]
assert r ∈ ℚ[x]

assert p.deg() = 3
assert p.deg() ≠ 2

/- SPEC.md §Differentials' ℚ[x] polynomial: the same operation, one ring
over, and now in SPEC's OWN spelling. The superscript binds tighter than
implicit multiplication (#26), so `3x²` is `3·(x²)`; until that was ruled,
this line bound `9x² + x + 1` silently and was written `3*x²` here with a
comment saying so. `f(2) = 15` is SPEC's own check that tells the two
polynomials apart, and the wrong reading is pinned as FALSE below rather
than merely absent — `(3x)² + x + 1` at 2 is 39. -/
let f := x ↦ 3x² + x + 1 in ℚ[x]
assert f.deg() = 2
assert f(2) = 15
assert f(2) ≠ 39

/-! ### SPEC.md §Differentials, verbatim

`Spec ℚ[x]` and `Schemes/ℚ` are ASCRIPTION TAGS (DESIGN.md §Differentials):
the membership is real and checked, the categorical structure is deferred.
`d` and `(d/dx)` are ONE operation with two result shapes — the `derivative`
METHOD, applied by elaboration exactly as calling a polynomial is. -/

let X := Spec ℚ[x] in Schemes/ℚ

assert f ∈ ℚ[x]
assert d(f) = (6x + 1) dx
assert (d/dx)(f) = 6x + 1

-- a 1-form is NOT the polynomial that coefficients it: `Ω¹ ≅ ℚ[x] dx` is
-- free of rank one, so these two are unequal rather than incomparable
assert d(f) ≠ 6x + 1
assert (d/dx)(f) ≠ (6x + 1) dx
-- …and the wrong derivative, which the same read must reject
assert d(f) ≠ (6x + 2) dx
assert (d/dx)(f) ≠ 6x + 2

/-! ### SPEC.md §Indefinite integration, verbatim

`∫ f dx` is the COMPLETE set of primitives — a coset of `ker(d/dx)`, which is
what SPEC.md's `+ ℚ` says. The coset's canonical representative has constant
term zero, so a coset a mathematician writes and one `∫` computes compare as
data however either was spelled. -/

assert kernel(d/dx : ℚ[x] → ℚ[x]) = ℚ

assert ∫ f dx = x³ + (1/2)x² + x + ℚ
-- the SET is what is asserted, so any representative writes the same coset:
-- two primitives differ by a constant, and the presentation says so
assert ∫ f dx = x³ + (1/2)x² + x + 7 + ℚ
-- …and a coset of a DIFFERENT function is a different set
assert ∫ f dx ≠ x³ + x² + x + ℚ
-- it is a set: countable, and its members are exactly the primitives
assert |∫ f dx| = ℵ₀

let Fs := {h ∈ ∫ f dx | h(0) = 0} in 𝒫(ℚ[x])
assert Fs.cardinality() = 1
assert Fs.cardinality() ≠ 2
let F := Fs[0] in ℚ[x]

assert F(x) = x³ + (1/2)x² + x
assert d(F) = f dx
assert (d/dx)(F) = f
-- …the round trip in the other direction, and a wrong primitive
assert F ∈ ∫ f dx
assert F(x) ≠ x³ + (1/2)x² + x + 1

-- a guard that pins a DIFFERENT constant picks a different primitive: the
-- solve is exact, not a convention about which primitive is "the" one
let Gs := {h ∈ ∫ f dx | h(0) = 5} in 𝒫(ℚ[x])
let G := Gs[0] in ℚ[x]
assert G(x) = x³ + (1/2)x² + x + 5
assert G ∈ ∫ f dx
assert (d/dx)(G) = f

-- BOTH exponent spellings bind the same way: `2x^2` is `2·(x²)` (18 at 3),
-- not `(2x)²` (36)
let twoXsq := x ↦ 2x^2 in ℚ[x]
assert twoXsq(3) = 18
assert twoXsq(3) ≠ 36

-- …and 76 is the precedence that keeps unary minus OUT of the implicit
-- product: `3-x` is the subtraction it always was, not `3·(-x)`
let threeMinus := x ↦ 3-x in ℤ[x]
assert threeMinus(1) = 2
assert threeMinus(1) ≠ -3

/-! ## SPEC.md §Exact number systems: the ⊆-chain

`and` is a conjunction of ASSERTIONS, and each link is the canonical-map
registry's claim rather than a set-layer computation (`domainSubset`). The
false cases cannot be written as an `assert` — a false one is a build error —
so they are pinned as `#guard`s in `CasDslTests/CanonicalMaps.lean` and as
surface failures in `tests/test_e2e.py`. -/

assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ

-- the link the sets unit refused and pointed here for, now answered
assert ℕ ⊆ ℤ
-- the chain composes as inclusions do, and each conjunct stands alone
assert ℕ ⊆ ℂ
assert ℤ ⊆ ℝ

/-! ## SPEC.md §Exact number systems: √2, i, and the complex plane

Every value here is EXACT. `√2`, `i`, `2√2` and `2 + 2i` are algebraic
numbers in the normal form `a + b√d`, never decimals — approximation is a
separate operation on an exact element (SPEC.md's `map √2 to ℝ/O(ε)`, #7) and
nothing in this section performs one. -/

assert √2 ∈ ℝ
assert 2 + 2i ∈ ℂ
-- …and the two memberships that must fail: √2 is irrational, and a number
-- with an imaginary part is not real
assert √2 ∉ ℚ
assert 2 + 2i ∉ ℝ

let z := 2 + 2i in ℂ
assert z.re() = 2
assert z.im() = 2
assert z.bar() = 2 - 2i
assert z · z.bar() = 8
assert |z| = 2√2

-- each of those with a wrong answer, which the surface can state as `≠`
assert z.re() ≠ 3
assert z.im() ≠ 0
assert z.bar() ≠ 2 + 2i
assert z · z.bar() ≠ 4
assert |z| ≠ 2

-- the normal form is one value with one spelling: √8 IS 2√2, and the square
-- root of a square is the integer
assert √8 = 2√2
assert √9 = 3
assert √2 · √2 = 2
-- a real surd is its own real part and its own conjugate — ℝ ⊆ ℂ, spelled
-- out. (A method call takes a NAME receiver, so the surd is bound first.)
let s2 := √2 in ℝ
assert s2.re() = √2
assert s2.im() = 0
assert s2.bar() = √2
assert |s2| = √2
-- and `i` is a CONSTANT, not a binding: a `let` shadows it exactly as one
-- shadows the `R` spelling of ℝ. (Bound last in this file on purpose —
-- nothing below reads `i`.)
/-! ### `map p to ℂ[x]` and `ℂ - ℚ` (SPEC.md §Polynomials)

The coercion and the difference set are decided here; the FACTORIZATION and
the roots over ℂ are Sage's, so they are pinned semantically by the routing
proofs in `CasDsl/Std.lean` and executed against the real adapter by
`tests/roundtrip.py` and `tests/test_e2e.py` — this build stays backend-free. -/

let pc := map p to ℂ[x]
assert pc ∈ ℂ[x]
assert pc.deg() = 3

-- The CONTENT of SPEC.md's displayed factorization `(x-1)(x - (-1+√5)/2)(x -
-- (-1-√5)/2)`, checked without a backend: each displayed root is a root, and
-- a near miss is not. What the adapter actually returns is pinned in
-- tests/roundtrip.py; this is the claim that makes the display true.
assert pc(1) = 0
assert pc((-1 + √5) / 2) = 0
assert pc((-1 - √5) / 2) = 0
assert pc((-1 + √5) / 3) ≠ 0
assert pc(√2) ≠ 0

-- SPEC.md §Polynomials, verbatim: an exact irrational is a root of an exact
-- polynomial, decided rather than sampled — `√2 · √2` is 2 and not 1.9999999
let qsq := x ↦ x² - 2 in ℚ[x]
assert qsq(√2) = 0
assert qsq(-√2) = 0
assert qsq(√2) ≠ 1
assert qsq(2) ≠ 0

-- `ℂ - ℚ` decides membership pointwise, and that is all it claims
assert √2 ∈ ℂ - ℚ
assert 2 + 2i ∈ ℂ - ℚ
assert 1 ∉ ℂ - ℚ
assert 1 / 2 ∉ ℂ - ℚ
-- SPEC.md's `q.roots() ⊆ ℂ - ℚ`, over the root set ℂ[x] gives it (spelled
-- out here; that the backend RETURNS this set is tests/roundtrip.py's claim)
assert {√2, -√2} ⊆ ℂ - ℚ
-- (the false case has no surface spelling — there is no `⊄` relation — so it
-- is a `#guard` over the executor in CasDslTests/Core.lean)

let i := 5 in ℤ
assert 2 + 2i = 12

/-! ## SPEC.md's Finite sets section, verbatim

Every line of `SPEC.md` §Finite sets runs here, so a false assertion fails
the build. Both powerset ascriptions are exercised (`𝒫(ℤ)` and `2^ℤ`), and
each operator family carries its false case — as an `≠` where the surface
can state one, and as a `Native.run` guard where a false `assert` would
simply be a build error. -/

let A := {1, 2, 3} in 𝒫(ℤ)
let B := {3, 4, 5} in 2^ℤ

assert A ∪ B = {1, 2, 3, 4, 5}
assert A ∩ B = {3}
assert A \ B = {1, 2}
assert A △ B = {1, 2, 4, 5}

assert |A| = 3
assert |A × B| = 9
assert |𝒫(A)| = 2^|A|

assert 2 ∈ A
assert 4 ∉ A
assert A ⊆ A ∪ B
assert A ∩ B ⊆ A

-- each operator family gets a wrong answer it must reject
assert A ∪ B ≠ {1, 2, 3, 4}
assert A ∩ B ≠ {3, 4}
assert A \ B ≠ {1, 2, 3}
assert A △ B ≠ {1, 2, 4}
assert |A| ≠ 4
assert |A × B| ≠ 8
assert |𝒫(A)| ≠ 2^|A ∪ B|

-- the ascription is a CHECKED membership judgment, in the surface's own
-- spelling too: SPEC.md writes the ASCII `in` for `∈`
assert A in 𝒫(ℤ)
assert A ∈ 𝒫(ℤ)
assert A ∪ B ∉ 𝒫(A)

-- an inclusion the presentations settle to FALSE (a false `assert` is a
-- build error, so the negative case is stated through the executor)
#guard (Native.run "subset" (.setObj (.finite .int #[.int 1, .int 2, .int 3]))
    #[.setObj (.finite .int #[.int 3, .int 4, .int 5])]).toOption
  == some (Value.bool false)

/-! ## SPEC.md's Set comprehensions section, verbatim

Every line runs here. The finite comprehension is DECIDED (bounded, then
every candidate tested exactly), and the infinite one is the arithmetic
progression its image is — so its membership, cardinality and equality are
the ones the progression presentation already decides. -/

let S := {n ∈ ℤ | n² ≤ 20}
assert S in 𝒫(ℤ)

assert S = {-4, -3, -2, -1, 0, 1, 2, 3, 4}
assert |S| = 9
-- the decision is exact on both sides of the boundary: 4² = 16 ≤ 20 < 25
assert 4 ∈ S
assert 5 ∉ S
assert -4 ∈ S
assert S ≠ {-4, -3, -2, -1, 0, 1, 2, 3}

let E := {2n | n ∈ ℕ}
assert E in 𝒫(ℕ)

assert 8 ∈ E
assert 9 ∉ E
assert |E| = ℵ₀
-- membership is SOLVED, not enumerated: no candidate list reaches 10¹²
assert 1000000000000 ∈ E
assert 1000000000001 ∉ E
assert E ≠ {0, 3, ...}

-- `e` was bound in the Functions section above; both spellings of its image
-- are the same set, and equal to the comprehension by normalization
assert e(ℕ) = E
assert e.image() = E
assert e.image() ≠ {0, 4, ...}

assert {e(n) | n ∈ ℕ, 0 ≤ n < 6} = {0, 2, 4, 6, 8, 10}
assert {e(n) | n ∈ ℕ, 0 ≤ n < 6} ≠ {0, 2, 4, 6, 8}

-- SPEC.md §Ellipses spells the binder with the ASCII `in` too
assert {n in ℤ | n² ≤ 20} = S

-- a constant guard that no candidate satisfies is DECIDED empty, including
-- when it reaches the constant through the zero polynomial (`n - n`)
assert {n ∈ ℤ | n - n < 0} = {}
assert {n ∈ ℤ | 0*n > 0} = {}

-- an unguarded head is read once, so it is read in the ELEMENT world too:
-- these three are genuinely constant or linear there and still decide
assert {p.deg() | n ∈ ℕ} = {3}
assert {7 | n ∈ ℕ} = {7}
assert {2n | n ∈ ℕ} = {0, 2, 4, ...}

/- The comprehension binder is a REAL local binding scoped to the braces: it
shadows a session binding INSIDE them (ordinary scoping), leaves it untouched
outside, and publishes nothing. `n` is bound to 360 nowhere near here, so the
shadowing claim is made against a binding introduced for it. -/
let cn := 100 in ℤ
assert {cn ∈ ℤ | cn² ≤ 20} = S
assert cn = 100

/-! ## Vectors (SPEC.md §Vectors and matrices)

`ℚ²` is SPEC.md's own superscript spelling of the vector domain, and the one
`Domain.render` produces — so a vector domain reads back exactly as it
displays. Nothing here reaches a backend. -/

let vv := (1, 2) in ℚ²
let vb := (5, 11) in ℚ²

assert vv = (1, 2)
assert vv ≠ vb
-- the LENGTH is part of the vector, so a longer one is unequal rather than
-- incomparable — and a vector is not the scalar its single component is
assert vv ≠ (1, 2, 3)
-- a vector literal needs TWO components: `(1)` is the parenthesized scalar it
-- always was, and a scalar against a vector stays INCOMPARABLE (Core.lean)
assert (1) = 1

/- SPEC.md's `M*v = b`, in all three spellings it writes the ACTION in: the
explicit product, juxtaposition, and the call. One implementation — `M` is
the Mat₂(ℚ) bound in the command smoke above. (`M⁻¹` routes to a backend, so
its four SPEC.md lines are `tests/test_e2e.py`'s claim.) -/
assert M*vv = vb
assert M vv = vb
assert M(vv) = vb
-- …and the wrong vector, which the same operation must reject
assert M*vv ≠ vv
assert M*vv ≠ (5, 12)

/- `and` is a NON-RESERVED keyword, hence an identifier token, so the
juxtaposition production would eat it as an argument and SPEC.md's ⊆-chain
would be lost for any conjunct ENDING in a name. Every conjunct below ends in
one, which is what the corpus's `and` chains — all of them over domain tokens
— never exercised. -/
assert vv = vv and vb = vb
assert M vv = vb and vv = vv
assert M*vv = vb and M vv = vb and vb = vb

run_cmd do
  let env ← Lean.getEnv
  let m : CasExpr := .ref `M
  -- the SHAPE is checked: Mat₂ does not apply to a vector of ℚ³, and the
  -- refusal names the shapes rather than reporting a missing common kind
  refuses env (.bin .mul m (.vecLit #[.num 1, .num 0, .num 1]))
    "does not apply to a vector of length 3"
  refuses env (.app m #[.vecLit #[.num 1, .num 0, .num 1]])
    "does not apply to a vector of length 3"
  -- a matrix ACTS on a vector: no other operation between them has a meaning,
  -- and each says which one the mathematician wanted
  refuses env (.bin .add m (.ref `vv)) "a matrix ACTS on a vector"
  refuses env (.bin .sub m (.ref `vv)) "a matrix ACTS on a vector"
  refuses env (.bin .div m (.ref `vv)) "is its INVERSE"
  -- …and the action is not symmetric: a row vector times a matrix is a
  -- different operation, which this slice does not present
  refuses env (.bin .mul (.ref `vv) m) "multiplication is not defined on"

/-! ## Subspaces and spans (SPEC.md §Subspaces and spans)

Every line of the section runs here except the two that need a multi-binder
lambda (`φ`, `W = ker φ`), which are the disclosed gap DESIGN.md records.
Nothing here reaches a backend: the reduced echelon basis is a presentation's
normal form, and `dim`, membership and equality are read off it. -/

let u₁ := (1, 0, 1) in ℚ³
let u₂ := (0, 1, 1) in ℚ³
let W := span_QQ{u₁, u₂} \leq ℚ³ in QQ-Mod

assert W.dim() = 2
assert (1, 1, 2) ∈ W
assert (1, 1, 0) ∉ W

-- the dimension is the size of a BASIS, not of a generating list: a
-- dependent generator adds nothing, and a different generating list of the
-- same subspace is the same subspace
let Wdep := span_QQ{u₁, u₂, (1, 1, 2)} ≤ ℚ³ in QQ-Mod
assert Wdep.dim() = 2
assert Wdep = W
assert span_QQ{(1, 1, 2), (0, 1, 1)} = W
assert span_QQ{(1, 0, 0), (0, 1, 1)} ≠ W
-- …and the wrong dimension, which the same read must reject
assert W.dim() ≠ 3

-- a subspace is a SET: inclusion and the trivial subspace are the ordinary
-- set judgments, decided from the same basis
assert span_QQ{u₁} ⊆ W
assert W ⊆ W
assert |W| = ℵ₀
-- …and the TRIVIAL subspace is the one-element set {0}: written with the zero
-- vector of the space meant, since the ambient is read off the generators
let Wzero := span_QQ{(0, 0)} ≤ ℚ² in QQ-Mod
assert |Wzero| = 1
assert Wzero.dim() = 0
-- SPEC.md's own `M.ker() = {0}`, in the form that needs no backend: the
-- trivial subspace IS the one-element set whose element is the zero of the
-- ambient space, which is what `0` spells there
assert Wzero = {0}
assert Wzero ≠ W
assert 0 ∈ Wzero
assert (1, 0) ∉ Wzero

run_cmd do
  let env ← Lean.getEnv
  -- the ambient of the subobject ascription is CHECKED, not taken on trust
  refuses env (.cmp .le (.ref `W) (.bin .pow (.dom .rat) (.num 2)))
    "is not a subobject of ℚ²"
  -- a generator outside ℚⁿ is a loud refusal rather than a dropped term
  refuses env (.spanOf #[.num 1]) "is not a vector"
  -- …and a generator of a DIFFERENT ambient is refused by the ordinary
  -- coercion, before any reduction: a span has one ambient space
  refuses env (.spanOf #[.ref `u₁, .vecLit #[.num 1, .num 1]])
    "a vector of length 2 is not an element of ℚ³"
  -- an empty brace has no ambient to span in, and points at the two ways the
  -- trivial subspace IS written
  refuses env (.spanOf #[]) "names no ambient space"

run_cmd do
  let env ← Lean.getEnv
  for (name, rendered, presented) in
      [(`vv, "(1, 2)", "(1, 2) ∈ ℚ²"), (`vb, "(5, 11)", "(5, 11) ∈ ℚ²")] do
    match CasDsl.binding? env name with
    | none => throwError "'{name}' was not bound"
    | some o =>
        if o.render != rendered then
          throwError "'{name}' rendered as {o.render}, expected {rendered}"
        if o.presentation != presented then
          throwError "'{name}' presented as {o.presentation}, expected {presented}"

/-! ## The root set (SPEC.md §A composed computation)

`{x ∈ D | p(x) = q(x)}` is the set of SOLUTIONS in `D`, which is the `roots`
method the surface already has — not the guarded comprehension's decision
procedure, which bounds a binder from an order comparison. What it computes
needs a backend, so the SPEC.md lines are `tests/test_e2e.py`'s claim; the
parse, the substitution it rests on and the refusals are here. -/

-- calling a polynomial at a POLYNOMIAL substitutes, which is what makes the
-- equation readable with the binder as the indeterminate at all
let pin(x) := x^2 in ℚ[x]
let pcomp(x) := pin(x) + 1 in ℚ[x]
assert pcomp(2) = 5
assert pcomp(0) = 1

run_cmd do
  let env ← Lean.getEnv
  -- the index must be a DOMAIN: that is where the roots are sought
  refuses env (.rootSet `a (.finSet #[.num 1]) (.ref `a) (.num 0))
    "is the set of solutions in a DOMAIN"
  -- …and a polynomial that cannot be presented there is the ordinary
  -- canonical-map refusal, not a silent reach into a larger ring
  refuses env (.rootSet `a (.dom .int) (.ref `pcomp) (.bin .div (.num 1) (.num 2)))
    "no preferred canonical map"

/-! ## Aggregation (SPEC.md §A composed computation)

`∑` and `∏` fold an explicit finite set. The body binds TIGHTLY — SPEC.md
writes the bare binder, and a wider body is parenthesized — so `= 0` on the
right of an assertion ends the sum exactly where it is written. -/

assert ∑_{a ∈ {1, 2, 3}} a = 6
assert ∏_{a ∈ {1, 2, 3}} a = 6
assert ∑_{a in {1, 2, 3}} a = 6
-- a SET counts each element once, however the literal was written
assert ∑_{a ∈ {1, 1, 2, 3}} a = 6
-- the empty sum is 0 and the empty product is 1: the mathematical answers,
-- pinned so a later refactor cannot quietly make them something else
assert ∑_{a ∈ {}} a = 0
assert ∏_{a ∈ {}} a = 1
-- a body other than the binder aggregates the IMAGE, with the binder a real
-- local binding scoped to the expression
assert ∑_{a ∈ {1, 2, 3}} (a^2) = 14
assert ∏_{a ∈ {1, 2, 3}} (2*a) = 48
-- …exact over ℚ and over the surds, never a decimal
assert ∑_{a ∈ {1/2, 1/3}} a = 5/6
assert ∑_{a ∈ {√2, -√2}} a = 0
assert ∏_{a ∈ {√2, -√2}} a = -2
-- and the wrong answers the same folds must reject
assert ∑_{a ∈ {1, 2, 3}} a ≠ 7
assert ∏_{a ∈ {1, 2, 3}} a ≠ 0

run_cmd do
  let env ← Lean.getEnv
  let three : CasExpr := .finSet #[.num 1, .num 2, .num 3]
  -- (the fold's own guard — that an identity-seeded fold never REPORTS the
  -- seed — is pinned in CasDslTests/Core.lean against the executor: a set
  -- literal of values with no arithmetic does not survive `elemsDomain`, so
  -- the surface cannot build one to aggregate)
  -- the sum over an infinite set is a limit this slice has no notion of, so
  -- it is not a method of ℕ at all — a different statement from "no route"
  refuses env (.aggregate `sum `n (.dom .nat) (.ref `n))
    "not a method of any category"
  -- …and a body that is not the binder needs an EXPLICIT finite set
  refuses env (.aggregate `sum `n (.dom .nat) (.bin .mul (.num 2) (.ref `n)))
    "EXPLICIT finite set"
  -- aggregating over something that is not a set at all
  refuses env (.aggregate `sum `a (.num 3) (.ref `a)) "aggregates over a SET"
  -- the binder publishes nothing: outside the expression it is unbound
  refuses env (.ref `a) "not bound"
  -- …and the aggregation is decided over `three` for the positive claims above
  match ← runEval { env } (.aggregate `sum `a three (.ref `a)) with
  | .ok d => unless d.render == "6" do throwError s!"∑ gave {d.render}"
  | .error e => throwError e.render

/-! ## Numerical approximation (SPEC.md §Exact number systems, #7)

Everything here needs NO backend: the braced exponent is a parser decision,
and each refusal below happens before any route is taken. What the surface
does when a backend IS reached is `tests/test_e2e.py`'s claim. -/

-- `x^{k}` is the braced exponent spelling — the one this system's own LaTeX
-- renderer produces and the one SPEC.md writes its tolerance in
assert 10^{3} = 1000
assert 2^{3} = 8
assert 1/10^{2} = 1/100
-- …and a brace with more than one element is still the powerset `2^A`
assert |2^{1, 2, 3}| = 8

run_cmd do
  let env ← Lean.getEnv
  let sqrt2 : CasExpr := .sqrt (.num 2)
  let tenth : CasExpr := .bin .div (.num 1) (.num 10)
  -- ε ≤ 0 is refused at the SURFACE — it is not a tolerance at all, which is
  -- a different statement from "no backend could meet it"
  refuses env (.mapTo sqrt2 (.approxTarget (.num 0))) "is not a tolerance"
  refuses env (.mapTo sqrt2 (.approxTarget (.neg (.num 1)))) "is not a tolerance"
  refuses env (.mapTo sqrt2 (.approxTarget (.dom .int))) "exact positive rational"
  -- `ℝ/O(ε)` is not a value anywhere else, so `ℝ ⊆ ℝ/O(ε)` cannot be stated
  -- at all — let alone answered `true`
  refuses env (.approxTarget tenth) "not a domain"
  -- the CANONICAL-MAP registry owns which values may be presented in ℝ, and
  -- it registers no map of ℂ into it: `2 + 2i` is refused before any backend
  -- is asked, by the registry rather than by a special case here
  -- (the value is written as a literal rather than as `2 + 2i`, because `i` is
  -- bound to 5 above — and because nothing in this file may reach a backend:
  -- every claim here is decided before a route is taken)
  refuses env (.mapTo (.lit (.alg 2 2 (-1))) (.approxTarget tenth))
    "no preferred canonical map"
  refuses env (.mapTo (.dom .int) (.approxTarget tenth)) "needs an element value"

/-- A genuine Lean command in a cell is unaffected by the low-priority
bare-expression production. -/
def foo : Nat := 1

#guard foo == 1

end CasDslTests
