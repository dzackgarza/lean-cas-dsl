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

-- `R` and `RR` are spellings of ℝ; every other identifier is a name
#guard domainAlias? `RR == some .real
#guard domainAlias? `R == some .real
#guard domainAlias? `Reals == none

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

/-- A genuine Lean command in a cell is unaffected by the low-priority
bare-expression production. -/
def foo : Nat := 1

#guard foo == 1

end CasDslTests
