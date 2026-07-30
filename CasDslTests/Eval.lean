/-
Elaboration-time tests for the surface layer.

Two halves: `#guard` over the evaluator's PURE core (polynomial arithmetic,
canonical embeddings, progression construction, the `D[x]`-vs-`e[k]`
disambiguation, the `Matₙ` spelling), and a parser/command smoke that
exercises every command form — arithmetic assertions, bindings, ascriptions,
the polynomial binder, `map`, and a bare expression cell — plus the proof
that an ordinary Lean command in a cell still elaborates as Lean.

The coercions here are REGISTRY-driven (`CasDsl/Category.lean`'s
`EmbedRule`), so the pure guards below carry their own rule array and the
command smoke needs the prelude's registrations: hence the import of the
standard universe. `CasDslTests/Embed.lean` owns the claims about the
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
private def embeds : Array EmbedRule := #[
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
`CasDslTests/Embed.lean`'s business. -/

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
