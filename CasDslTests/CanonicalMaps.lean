/-
Elaboration-time tests for the coercion layer: preferred canonical maps as
REGISTRY DATA (`CasDsl/Category.lean`'s `CanonicalMap`, consulted by
`Eval.coerceValue`/`Eval.domJoin`).

The first half is `#guard` over fixture rule arrays, so every claim about
*what the registry decides* is checked without an `Environment`. The pivotal
pair is a coercion that succeeds against a registered edge and FAILS against
an EMPTY array: that is what proves the embeddings became data rather than
code with a registry-shaped comment. The engine-level cases are asserted the
other way round — they must still hold with NO rules registered at all, which
is what makes them engine-level.

Defective registrations are the other half of the discipline: two rules for
one pair, or two rules pointing at each other, are loud errors naming both
rules. A coercion never ranks registrations, exactly as the resolver never
ranks competing functors.

The second half runs against the real standard universe, after the olean
round trip, and pins the surface behaviour the notebook depends on:
`map p to ℚ[x]`, a mixed ℤ/ℚ join, `7 in ℤ/5`, and the honest failure of a
pair nobody registered.
-/
import CasDsl

namespace CasDslTests.CanonicalMaps

open Lean Elab Command
open CasDsl

/-! ## Fixtures (plain data — no `Environment` needed)

Spelled out here rather than imported from `CasDsl/Std.lean`, so a guard that
passes is a claim about the coercion layer and not about the prelude. -/

/-- The canonical injections of the standard universe. -/
private def std : Array CanonicalMap := #[
  { src := .exact .nat, tgt := .exact .int, op := .identity },
  { src := .exact .nat, tgt := .exact .rat, op := .intToRat },
  { src := .exact .int, tgt := .exact .rat, op := .intToRat },
  { src := .exact .int, tgt := .anyMod, op := .intToMod }
]

/-- …and the number-system chain SPEC.md §Exact number systems asserts, added
to them: `ℚ ⊆ ℝ ⊆ ℂ` with the ℤ/ℕ links the one-hop rule needs. -/
private def chain : Array CanonicalMap := std ++ #[
  { src := .exact .nat, tgt := .exact .real, op := .identity },
  { src := .exact .int, tgt := .exact .real, op := .identity },
  { src := .exact .rat, tgt := .exact .real, op := .identity },
  { src := .exact .nat, tgt := .exact .complex, op := .identity },
  { src := .exact .int, tgt := .exact .complex, op := .identity },
  { src := .exact .rat, tgt := .exact .complex, op := .identity },
  { src := .exact .real, tgt := .exact .complex, op := .identity }
]

/-- Two rules that both accept `(ℤ, ℚ)`: a defective registration. -/
private def twoWays : Array CanonicalMap := #[
  { src := .exact .int, tgt := .exact .rat, op := .intToRat,
    doc := "the fraction field of ℤ" },
  { src := .exact .int, tgt := .anyDom, op := .identity,
    doc := "a second rule that also accepts ℤ → ℚ" }
]

/-- ℤ and ℚ registered as embedding into EACH OTHER: neither is the preferred
common domain, and a join may not pick. -/
private def bothWays : Array CanonicalMap := #[
  { src := .exact .int, tgt := .exact .rat, op := .intToRat, doc := "ℤ ⊆ ℚ" },
  { src := .exact .rat, tgt := .exact .int, op := .identity,
    doc := "a bogus ℚ → ℤ" }
]

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def errOf : Except String Value → String
  | .error m => m
  | .ok v => s!"unexpectedly succeeded with {v.render}"

/-! ## The registry decides: the same coercion, with and without the rule

Each pair below is one claim — a registered edge applies, and with no rules
registered the identical call fails honestly. Delete the registry consult
from `coerceValue` and the second half of every pair breaks. -/

#guard (coerceValue std .rat (.int 3)).toOption == some (Value.rat 3)
#guard (coerceValue #[] .rat (.int 3)).toOption == none
#guard contains (errOf (coerceValue #[] .rat (.int 3)))
  "there is no preferred canonical map of 3 into ℚ"

#guard (coerceValue std (.mod 5) (.int 7)).toOption == some (Value.mod 5 2)
#guard (coerceValue #[] (.mod 5) (.int 7)).toOption == none

-- ONE rule carries ℤ into every ℤ/n (`DomainPattern.anyMod`)
#guard (coerceValue std (.mod 7) (.int 9)).toOption == some (Value.mod 7 2)

-- structural congruence bottoms out in the registry: the coefficient- and
-- entry-wise images exist exactly when the scalar embedding is registered
#guard (coerceValue std (.poly .rat) (.poly .int #[.int 1, .int (-2)])).toOption
  == some (Value.poly .rat #[.rat 1, .rat (-2)])
#guard (coerceValue #[] (.poly .rat) (.poly .int #[.int 1, .int (-2)])).toOption == none
#guard (coerceValue std (.matrix 2 .rat)
    (.mat 2 .int #[#[.int 1, .int 2], #[.int 3, .int 4]])).toOption
  == some (Value.mat 2 .rat #[#[.rat 1, .rat 2], #[.rat 3, .rat 4]])
#guard (coerceValue #[] (.matrix 2 .rat)
    (.mat 2 .int #[#[.int 1, .int 2], #[.int 3, .int 4]])).toOption == none

-- an unregistered pair is an honest error, never a "reasonable" conversion
#guard (coerceValue std .int (.rat (1/2))).toOption == none
#guard (coerceValue std (.mod 5) (.rat (1/2))).toOption == none
#guard contains (errOf (coerceValue std (.mod 5) (.rat (1/2))))
  "there is no preferred canonical map of 1/2 into ℤ/5"
-- a value with no presented domain (a truth value) embeds nowhere
#guard (coerceValue std .int (.bool true)).toOption == none

/-! ## The engine-level cases: they hold with NO rules registered

Each of these is in the engine because it is not a canonical injection
between two domains; registering nothing may not change any of them. -/

-- identity: the value already presents the target
#guard (coerceValue #[] .int (.int 3)).toOption == some (Value.int 3)
#guard (coerceValue #[] .rat (.rat (1/2))).toOption == some (Value.rat (1/2))
#guard (coerceValue #[] (.mod 5) (.mod 5 2)).toOption == some (Value.mod 5 2)
-- `ℕ ← ℤ` is a CHECK, and it is still partial
#guard (coerceValue #[] .nat (.int 3)).toOption == some (Value.int 3)
#guard (coerceValue #[] .nat (.int (-1))).toOption == none
#guard contains (errOf (coerceValue #[] .nat (.int (-1)))) "is not an element of ℕ"
-- distinct moduli are distinct rings, and the message says so
#guard (coerceValue #[] (.mod 5) (.mod 4 2)).toOption == none
#guard contains (errOf (coerceValue #[] (.mod 5) (.mod 4 2)))
  "ℤ/4 and ℤ/5 are different rings"
-- a scalar as a constant polynomial, and the matrix size check
#guard (coerceValue #[] (.poly .int) (.int 4)).toOption == some (Value.poly .int #[.int 4])
#guard (coerceValue #[] (.matrix 2 .int) (.mat 3 .int #[])).toOption == none
#guard contains (errOf (coerceValue #[] (.matrix 2 .int) (.mat 3 .int #[])))
  "a 3×3 matrix is not an element of Mat2(…)"

/-! ## Joins are rule-driven -/

#guard (domJoin std .nat .int).toOption == some (some .int)
#guard (domJoin std .int .nat).toOption == some (some .int)
#guard (domJoin std .nat .rat).toOption == some (some .rat)
#guard (domJoin std .int .rat).toOption == some (some .rat)
#guard (domJoin std .rat .int).toOption == some (some .rat)
#guard (domJoin std (.mod 5) (.mod 5)).toOption == some (some (.mod 5))
#guard (domJoin std (.mod 4) (.mod 5)).toOption == some none
-- congruence under poly/matrix, size mismatch included
#guard (domJoin std (.poly .int) (.poly .rat)).toOption == some (some (.poly .rat))
#guard (domJoin std (.matrix 2 .int) (.matrix 2 .rat)).toOption == some (some (.matrix 2 .rat))
#guard (domJoin std (.matrix 2 .int) (.matrix 3 .int)).toOption == some none
-- with nothing registered, only identical domains have a join
#guard (domJoin #[] .int .rat).toOption == some none
#guard (domJoin #[] .int .int).toOption == some (some .int)

/-! ## `D ⊆ E` is read off the same registry

SPEC.md's `assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ`. Inclusion MEANS "the preferred
canonical map exists and is one", so each claim below is a claim about the
registry — and the pivotal pair is the same one the coercions make: with no
rules registered, the chain is gone. -/

private def subs (rules : Array CanonicalMap) (a b : Domain) : Option Bool :=
  (domainSubset rules a b).toOption

-- the chain itself
#guard subs chain .int .rat == some true
#guard subs chain .rat .real == some true
#guard subs chain .real .complex == some true
#guard subs chain .nat .int == some true
-- …and it is the REGISTRY's: unregister everything and no link survives
#guard subs #[] .int .rat == some false
#guard subs #[] .rat .real == some false
-- the other direction is not registered, and is not invented
#guard subs chain .rat .int == some false
#guard subs chain .real .rat == some false
#guard subs chain .complex .real == some false
-- a registered map that is NOT an inclusion answers false: the quotient
-- ℤ → ℤ/5 exists and does not make ℤ a subset of ℤ/5
#guard subs chain .int (.mod 5) == some false
#guard (coerceValue chain (.mod 5) (.int 7)).toOption == some (Value.mod 5 2)
-- reflexivity is engine-level, exactly as the identity coercion is
#guard subs #[] .int .int == some true
#guard subs #[] (.mod 5) (.mod 5) == some true
#guard subs #[] (.funcs .real .real) (.funcs .real .real) == some true
-- structural congruence, the coercion layer's own recursion
#guard subs chain (.poly .int) (.poly .rat) == some true
#guard subs chain (.poly .rat) (.poly .int) == some false
#guard subs chain (.matrix 2 .int) (.matrix 2 .rat) == some true
#guard subs chain (.matrix 2 .int) (.matrix 3 .rat) == some false
-- …including a scalar as its own constant polynomial
#guard subs chain .int (.poly .int) == some true
#guard subs chain .int (.poly .rat) == some true
#guard subs chain (.poly .int) .rat == some false
-- a defective registry is reported, never averaged into an answer
#guard subs twoWays .int .rat == none

/-! ## Defective registrations are loud, and name the rules

The whole point: an ambiguous or contradictory registry is never resolved by
array order, so both halves of the clash appear in the message. -/

private def defect : Except String Value → String := errOf

#guard (coerceValue twoWays .rat (.int 3)).toOption == none
#guard contains (defect (coerceValue twoWays .rat (.int 3))) "defective"
#guard contains (defect (coerceValue twoWays .rat (.int 3))) "the fraction field of ℤ"
#guard contains (defect (coerceValue twoWays .rat (.int 3)))
  "a second rule that also accepts ℤ → ℚ"
-- and the ambiguity is not laundered into a join either
#guard (domJoin twoWays .int .rat).toOption == none

#guard (domJoin bothWays .int .rat).toOption == none
#guard match domJoin bothWays .int .rat with
  | .error m => contains m "defective" && contains m "ℤ ⊆ ℚ" && contains m "a bogus ℚ → ℤ"
  | .ok _ => false
-- the defect propagates out of the structural recursion rather than being
-- swallowed into "no common domain"
#guard (domJoin bothWays (.poly .int) (.poly .rat)).toOption == none

/-! ## Against the real standard universe (after the olean round trip) -/

run_cmd do
  let env ← getEnv
  let shipped := (canonicalMaps env).map fun r => (r.src, r.tgt, r.op)
  let expected : Array (DomainPattern × DomainPattern × CanonOp) :=
    chain.map fun r => (r.src, r.tgt, r.op)
  unless shipped.size == expected.size && expected.all (shipped.contains ·) do
    throwError s!"the registered embeddings are {repr shipped}, expected the \
canonical injections {repr expected}"
  -- the number-system chain is the CLOSURE, not a path: the coercion layer
  -- takes one hop, so a missing pair is a missing coercion
  for (src, tgt) in [(Domain.nat, Domain.real), (.int, .real), (.rat, .real),
      (.nat, .complex), (.int, .complex), (.rat, .complex), (.real, .complex)] do
    unless (domainSubset (canonicalMaps env) src tgt).toOption == some true do
      throwError s!"{src.render} ⊆ {tgt.render} does not hold against the \
registered canonical maps"
  -- registry data documents itself: an undocumented rule is a mistake
  if let some bad := (canonicalMaps env).find? (·.doc.isEmpty) then
    throwError s!"the registered canonical map {renderCanonicalMap bad} carries no doc"
  -- re-registering the same pair is a clash, never a silent second rule
  if (addCanonicalMapChecked env
      { src := .exact .int, tgt := .exact .rat, op := .intToRat }).toOption.isSome then
    throwError "re-registering an imported embedding was not detected as a clash"

run_cmd do
  let rules := canonicalMaps (← getEnv)
  let .elem _ pz := Std.polyZ
    | throwError "the ℤ[x] fixture is not an element"
  let .elem _ pq := Std.polyQ
    | throwError "the ℚ[x] fixture is not an element"
  -- the notebook's `map p to ℚ[x]`, through the registered ℤ ⊆ ℚ
  match coerceValue rules (.poly .rat) pz with
  | .ok v =>
      unless v == pq do
        throwError s!"map to ℚ[x] produced {v.render}, expected {pq.render}"
  | .error m => throwError s!"map to ℚ[x] failed: {m}"
  -- an integer joins with a rational, and embeds into ℤ/5
  unless (domJoin rules .int .rat).toOption == some (some .rat) do
    throwError s!"ℤ and ℚ do not join to ℚ against the registered embeddings: \
{repr (domJoin rules .int .rat).toOption}"
  unless (coerceValue rules (.mod 5) (.int 7)).toOption == some (.mod 5 2) do
    throwError "7 does not embed into ℤ/5 against the registered embeddings"
  -- and a pair nobody registered stays an honest failure
  match coerceValue rules (.mod 5) (.rat (1/2)) with
  | .ok v => throwError s!"ℚ → ℤ/5 was invented, producing {v.render}"
  | .error m =>
      unless contains m "there is no preferred canonical map of 1/2 into ℤ/5" do
        throwError s!"the unregistered ℚ → ℤ/5 failed with the wrong message: {m}"

/-! ## The surface path

`map`, a mixed-domain literal and an ascription all reach the registry
through `EvalCtx.canonMaps`; the values are asserted through the evaluator so a
coercion dropped at the surface cannot hide behind the pure guards above. -/

let p(x) := x^3 - 2x + 1 in ℤ[x]
let q := map p to ℚ[x]
let r := 7 in ℤ/5

run_cmd do
  let env ← getEnv
  let expect : List (Name × Obj) := [(`p, Std.polyZ), (`q, Std.polyQ),
    (`r, .elem (.mod 5) (.mod 5 2))]
  for (name, o) in expect do
    match binding? env name with
    | none => throwError s!"'{name}' was not bound"
    | some o' =>
        unless o' == o do
          throwError s!"'{name}' is {o'.presentation}, expected {o.presentation}"
  -- 1 + 1/2: the operands join through the registry, in ℚ
  match ← runEval env (.bin .add (.num 1) (.bin .div (.num 1) (.num 2))) with
  | .ok d =>
      unless d.render == "3/2" do
        throwError s!"1 + 1/2 evaluated to {d.render}, expected 3/2"
  | .error e => throwError s!"1 + 1/2 failed: {e.render}"
  -- ℚ[x] has no registered embedding into ℤ[x], and `map` does not invent one
  match ← runEval env (.mapTo (.ref `q) (.index (.dom .int) (.ref `x))) with
  | .ok d => throwError s!"map q to ℤ[x] was invented, producing {d.render}"
  | .error e =>
      unless contains e.render "there is no preferred canonical map" do
        throwError s!"map q to ℤ[x] failed with the wrong message: {e.render}"

end CasDslTests.CanonicalMaps
