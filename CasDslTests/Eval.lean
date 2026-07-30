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

-- ℝ is an ascription tag: it admits no canonical map, so nothing lands in it
#guard (coerceValue embeds .real (.int 3)).toOption == none
#guard (domJoin embeds .real .rat).toOption == some none

/-! ### The `src → tgt` ascription is checked at the call boundary -/

-- an argument outside the source domain is refused, not computed with
#guard (atDomain embeds .nat (.int (-1))).toOption == none
#guard (atDomain embeds .nat (.int 3)).toOption == some (.int 3)
-- …and a result lands IN the target: t + 3 at 4 is 2 in ℤ/5, never 7
#guard (atDomain embeds (.mod 5) (.int 7)).toOption == some (.mod 5 2)
-- ℝ has no elements to check — that is the whole content of "ascription tag"
#guard (atDomain embeds .real (.int (-1))).toOption == some (.int (-1))
-- the symbolic path travels coefficient-wise, so it lands in the domain too:
-- `t + 7` reduces to `t + 2` over ℤ/5 instead of staying an unreduced ℤ poly
#guard (atDomain embeds (.mod 5) (Value.mkPoly .int #[.int 7, .int 1])).toOption
  == some (Value.mkPoly (.mod 5) #[.mod 5 2, .mod 5 1])
#guard (atDomain embeds .nat (xTo 1)).toOption
  == some (Value.mkPoly .nat #[.int 0, .int 1])
-- an ℝ arrow checks nothing, in either path — that is the tag exception
#guard (atDomain embeds .real (xTo 1)).toOption == some (xTo 1)

-- the binder is the indeterminate of the SOURCE domain; ℝ has no elements,
-- so there the body's own ring stands in
#guard binderRing (.mod 5) (xTo 2) == some (.mod 5)
#guard binderRing .nat (xTo 2) == some .nat
#guard binderRing .real (xTo 2) == some .int
#guard binderRing .real (Value.mkPoly (.mod 5) #[.mod 5 3, .mod 5 1]) == some (.mod 5)
-- a body that is no polynomial has no such ring, and does not default to ℤ
#guard binderRing .real (.bool true) == none

-- the ℤ/n zero is a zero: a normal form that missed it would leave two equal
-- polynomials comparing unequal
#guard Value.mkPoly (.mod 5) #[.mod 5 1, .mod 5 0] == .poly (.mod 5) #[.mod 5 1]

-- `R` and `RR` are spellings of ℝ; every other identifier is a name
#guard domainAlias? `RR == some .real
#guard domainAlias? `R == some .real
#guard domainAlias? `Reals == none

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

let e: ℕ → ℕ := n ↦ 2n

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
over. SPEC spells the leading term `3x²`; implicit multiplication binds
tighter than the superscript in this grammar (`3x²` parses as `(3x)²`), so
the product is written out — `f(2) = 15` is SPEC's own check that this is
the intended polynomial. -/
let f := x ↦ 3*x² + x + 1 in ℚ[x]
assert f.deg() = 2
assert f(2) = 15

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

/-- A genuine Lean command in a cell is unaffected by the low-priority
bare-expression production. -/
def foo : Nat := 1

#guard foo == 1

end CasDslTests
