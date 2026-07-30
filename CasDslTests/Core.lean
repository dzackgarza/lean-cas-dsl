/-
Elaboration-time tests for the pure core: the inheritance closure, the
method resolver, profile-rule instantiation, presentation patterns, and the
native backend's arithmetic and executors.

Everything here is `#guard` over pure functions — a wrong answer fails the
build. The executor table is the one `IO` surface, smoke-tested with `#eval`
(a throw fails the build too).
-/
import CasDsl

namespace CasDslTests

open Lean (Name)
open CasDsl

/-! ## Fixture registrations (plain data — no `Environment` needed) -/

/-- Chain, diamond and a deliberately cyclic pair. -/
private def cats : Array CatDecl := #[
  { name := `Sets },
  { name := `CountableSets, parents := #[`Sets] },
  { name := `FiniteSets, parents := #[`CountableSets] },
  { name := `CommRingElems },
  { name := `FactorizationElems, parents := #[`CommRingElems] },
  { name := `EuclideanElems, parents := #[`FactorizationElems] },
  { name := `A },
  { name := `B, parents := #[`A] },
  { name := `C, parents := #[`A] },
  { name := `D, parents := #[`B, `C] },
  { name := `X, parents := #[`Y] },
  { name := `Y, parents := #[`X] }
]

private def decls : Array MethodDecl := #[
  { id := `factor, receiver := `FactorizationElems },
  { id := `cardinality, receiver := `Sets },
  { id := `nth, receiver := `CountableSets, arity := 1 },
  { id := `size, receiver := `Sets },
  { id := `size, receiver := `FiniteSets },
  { id := `both, receiver := `B },
  { id := `both, receiver := `C }
]

/-! ## `parentClosure` -/

-- chain, with the inheritance path recorded (excluding the start)
#guard parentClosure cats `EuclideanElems ==
  #[(`EuclideanElems, []), (`FactorizationElems, [`FactorizationElems]),
    (`CommRingElems, [`FactorizationElems, `CommRingElems])]

-- diamond: `A` is reachable twice and appears once, by a shortest path
#guard (parentClosure cats `D).size == 4
#guard (parentClosure cats `D).find? (·.1 == `A) == some (`A, [`B, `A])

-- an unregistered name is its own closure (no crash, no invention)
#guard parentClosure cats `Nowhere == #[(`Nowhere, [])]

-- a registration cycle terminates
#guard (parentClosure cats `X).size == 2

-- specificity is antisymmetric, and mutually reachable names are incomparable
#guard strictlyBelow cats `FiniteSets `Sets
#guard !strictlyBelow cats `Sets `FiniteSets
#guard !strictlyBelow cats `X `Y

/-! ## `resolveCore` -/

private def tag : Except ResolveError Resolution → String
  | .ok _ => "ok"
  | .error (.notApplicable ..) => "notApplicable"
  | .error (.ambiguous ..) => "ambiguous"
  | .error (.unknownMethod _) => "unknownMethod"
  -- round-two failures are `CasDslTests/Transport.lean`'s subject; reaching
  -- this case from a round-one fixture would itself be the bug
  | .error (.functorTargetMismatch ..) => "functorTargetMismatch"

private def resolved (r : Except ResolveError Resolution)
    : Option (Name × List Name × CatRef) :=
  r.toOption.map fun res => (res.decl.receiver, res.via, res.profileEntry)

private def declaredOn? : Except ResolveError Resolution → Option (Array Name)
  | .error (.notApplicable _ _ ds) => some ds
  | _ => none

private def ambiguousCount : Except ResolveError Resolution → Nat
  | .error (.ambiguous _ cs) => cs.size
  | _ => 0

-- direct hit: declared on the profile entry itself
#guard resolved (resolveCore cats decls #[⟨`Sets, #[]⟩] `cardinality) ==
  some (`Sets, [], ⟨`Sets, #[]⟩)

-- inherited hit: the chain is recorded and the profile entry's params ride
-- through the inheritance edge unchanged
#guard resolved (resolveCore cats decls #[⟨`EuclideanElems, #[.dom .int]⟩] `factor) ==
  some (`FactorizationElems, [`FactorizationElems], ⟨`EuclideanElems, #[.dom .int]⟩)

-- one declaration reached from two profile entries is ONE candidate, and the
-- shortest chain wins
#guard resolved
    (resolveCore cats decls #[⟨`FiniteSets, #[]⟩, ⟨`CountableSets, #[]⟩] `cardinality) ==
  some (`Sets, [`Sets], ⟨`CountableSets, #[]⟩)

-- most specific declaration wins over the one it inherits from
#guard resolved (resolveCore cats decls #[⟨`FiniteSets, #[]⟩] `size) ==
  some (`FiniteSets, [], ⟨`FiniteSets, #[]⟩)

-- …and from further down the chain the inherited one is still reachable
#guard resolved (resolveCore cats decls #[⟨`CountableSets, #[]⟩] `size) ==
  some (`Sets, [`Sets], ⟨`CountableSets, #[]⟩)

-- incomparable receivers: a genuine ambiguity, never an order heuristic
#guard tag (resolveCore cats decls #[⟨`D, #[]⟩] `both) == "ambiguous"
#guard ambiguousCount (resolveCore cats decls #[⟨`D, #[]⟩] `both) == 2

-- declared, but not on anything this profile reaches: the error names where
-- it IS declared
#guard tag (resolveCore cats decls #[⟨`Sets, #[]⟩] `factor) == "notApplicable"
#guard declaredOn? (resolveCore cats decls #[⟨`Sets, #[]⟩] `factor) ==
  some #[`FactorizationElems]

-- not declared anywhere
#guard tag (resolveCore cats decls #[⟨`Sets, #[]⟩] `nope) == "unknownMethod"

-- an empty profile still distinguishes "no such method" from "not applicable"
#guard tag (resolveCore cats decls #[] `factor) == "notApplicable"

/-! ## Profile rules and presentation patterns -/

#guard (ProfileRule.mk (.elemOf .anyDom) `EuclideanElems #[.elemDom]).apply
    (.elem .int (.int 5)) == some ⟨`EuclideanElems, #[.dom .int]⟩

#guard (ProfileRule.mk (.elemOf (.matrixOver .anyDom)) `MatrixElems
    #[.matSize, .matEntry]).apply
    (.elem (.matrix 2 .rat) (.mat 2 .rat #[])) ==
  some ⟨`MatrixElems, #[.nat 2, .dom .rat]⟩

#guard (ProfileRule.mk .anySet `Sets #[.setDom]).apply
    (.setObj (.arithProg .int (.int 0) (.int 2) none)) == some ⟨`Sets, #[.dom .int]⟩

-- a slot that cannot be filled contributes nothing rather than crashing
#guard (ProfileRule.mk .anyObj `MatrixElems #[.matSize]).apply
    (.elem .int (.int 5)) == none

#guard (PresPattern.elemOf (.polyOver (.exact .int))).accepts
    (.elem (.poly .int) (.poly .int #[.int 1]))
#guard !(PresPattern.elemOf (.polyOver (.exact .rat))).accepts
    (.elem (.poly .int) (.poly .int #[.int 1]))
#guard PresPattern.anySet.accepts (.domainObj .int)
#guard !PresPattern.finiteSet.accepts (.domainObj .int)
#guard (PresPattern.progression (.exact .nat)).accepts
    (.setObj (.arithProg .nat (.int 0) (.int 2) none))
#guard PresPattern.cyclicMod.accepts (.cyclicModule 12)
#guard (DomainPattern.matrixOver (.exact .rat)).accepts (.matrix 3 .rat)
#guard !(DomainPattern.matrixOver (.exact .int)).accepts (.matrix 3 .rat)

/-! ## Native arithmetic helpers -/

open Native

-- `promote` names the kind two operands SHARE, and every caller matches on
-- that name. The kind is the claim: ℤ against ℚ is a rational pair, an
-- integer against ℤ/5 is a residue pair, and a pair with no shared kind is
-- `none` — never a shape that happens to compare.
#guard promote (.int 3) (.rat (mkRat 1 2)) == some (.rat 3 (mkRat 1 2))
#guard promote (.int 7) (.mod 5 3) == some (.mod 5 2 3)
#guard promote (.int 7) (.mod 0 3) == none
#guard promote (.mod 4 3) (.mod 5 3) == none
#guard promote (.int 1) (.bool true) == none
-- the surd kind: BOTH operands read in the one quadratic field one of them
-- names, a rational riding in it as `a + 0√d` — which is what keeps
-- `√2 + 1/2` inside ℚ(√2) instead of promoting it along ℤ ⊆ ℚ
#guard promote (.alg 1 2 3) (.alg 4 5 3) == some (.alg (1, 2) (4, 5) 3)
#guard promote (.int 4) (.alg 1 2 3) == some (.alg (4, 0) (1, 2) 3)
#guard promote (.alg 1 2 3) (.rat (mkRat 1 2)) == some (.alg (1, 2) (mkRat 1 2, 0) 3)
-- …and two DIFFERENT fields share no kind, which is the refusal `√2 + √5`
-- reports rather than an approximation
#guard promote (.alg 0 1 2) (.alg 0 1 5) == none
#guard promote (.alg 0 1 2) (.bool true) == none
#guard valueEq (.int 2) (.rat 2) == some true
#guard valueEq (.int 2) (.bool true) == none

/-- `t ↦ t² + 1`, the SPEC.md function, with the binder given by name. -/
private def sq1 (binder : Name) : Value :=
  .func .real .real binder (Value.mkPoly .int #[.int 1, .int 0, .int 1])

-- the binder is a BOUND name: `t ↦ t² + 1` and `s ↦ s² + 1` are one function
#guard valueEq (sq1 `t) (sq1 `s) == some true
-- …but the domains it is declared over are data
#guard valueEq (sq1 `t) (.func .nat .nat `t (Value.mkPoly .int #[.int 1, .int 0, .int 1]))
  == some false
#guard valueEq (sq1 `t) (.func .real .real `t (Value.mkPoly .int #[.int 1])) == some false
-- a function is not comparable with a scalar: `unknown`, never a false claim
#guard valueEq (sq1 `t) (.int 1) == none

#guard (scalarAdd (.int 2) (.rat (mkRat 1 2))).toOption == some (.rat (mkRat 5 2))
#guard (scalarMul (.mod 5 3) (.int 4)).toOption == some (.mod 5 2)
#guard (scalarSub (.int 2) (.int 5)).toOption == some (.int (-3))
#guard (scalarNeg (.mod 7 3)).toOption == some (.mod 7 4)
#guard (scalarPow (.int 2) (.int 10)).toOption == some (.int 1024)
#guard (scalarPow (.rat (mkRat 1 2)) (.int 0)).toOption == some (.rat 1)
#guard (scalarPow (.int 2) (.int (-1))).toOption == none
#guard (scalarDiv (.int 1) (.int 4)).toOption == some (.rat (mkRat 1 4))
#guard (scalarDiv (.int 1) (.int 0)).toOption == none
#guard (scalarDiv (.mod 5 1) (.mod 5 2)).toOption == none

-- trailing zeros are not part of a polynomial's presentation
#guard Value.mkPoly .int #[.int 1, .int 0, .int 0] == .poly .int #[.int 1]
#guard Value.mkPoly .int #[.int 0] == .poly .int #[]

/-! ### Exact algebraic numbers (`a + b√d`)

The normal form is the whole contract: `√8` IS `2√2`, a surd whose rational
part swallows its radical IS that rational, and two operands must share one
quadratic field or the operation refuses. Nothing here is ever a float. -/

private def alg (a b : Rat) (d : Int) : Option Value := (Value.mkAlg a b d).toOption

-- the square part of the radicand moves out front, so one value has one form
#guard alg 0 1 8 == some (.alg 0 2 2)
#guard alg 0 1 2 == some (.alg 0 1 2)
#guard alg 0 3 (-4) == some (.alg 0 6 (-1))
-- …and a radical that disappears leaves the RATIONAL, never a surd in disguise
#guard alg 3 0 5 == some (.int 3)
#guard alg 3 2 1 == some (.int 5)
#guard alg 3 2 0 == some (.int 3)
#guard alg (mkRat 1 2) 0 5 == some (.rat (mkRat 1 2))
-- `√q` for a rational, exactly: √8 = 2√2, √(1/2) = (1/2)√2, √(-4) = 2i
#guard (Value.sqrtOfRat 8).toOption == some (.alg 0 2 2)
#guard (Value.sqrtOfRat (mkRat 1 2)).toOption == some (.alg 0 (mkRat 1 2) 2)
#guard (Value.sqrtOfRat (-4)).toOption == some (.alg 0 2 (-1))
#guard (Value.sqrtOfRat 9).toOption == some (.int 3)
#guard (Value.sqrtOfRat 0).toOption == some (.int 0)
#guard (Value.squareFreePart 12).toOption == some (3, 2)
#guard (Value.squareFreePart (-4)).toOption == some (-1, 2)
-- a radicand whose square-free part is out of reach is a LOUD refusal, not an
-- unnormalized value that would compare unequal to its own normal form
#guard (Value.squareFreePart (1000003 * 1000003 * 5)).toOption == none

-- SPEC.md's `z · z.bar() = 8` and `|z| = 2√2`, as arithmetic
#guard (scalarMul (.alg 2 2 (-1)) (.alg 2 (-2) (-1))).toOption == some (.int 8)
#guard (scalarAdd (.int 2) (.alg 0 2 (-1))).toOption == some (.alg 2 2 (-1))
#guard (scalarSub (.int 2) (.alg 0 2 (-1))).toOption == some (.alg 2 (-2) (-1))
#guard (scalarNeg (.alg 2 2 (-1))).toOption == some (.alg (-2) (-2) (-1))
-- √2 · √2 = 2 exactly, which is what makes `q(√2) = 0` an identity
#guard (scalarMul (.alg 0 1 2) (.alg 0 1 2)).toOption == some (.int 2)
#guard (scalarPow (.alg 0 1 2) (.int 2)).toOption == some (.int 2)
#guard (scalarDiv (.int 1) (.alg 0 1 2)).toOption == some (.alg 0 (mkRat 1 2) 2)
#guard (scalarDiv (.alg 0 2 (-1)) (.alg 0 2 (-1))).toOption == some (.int 1)
-- two different quadratic fields: a loud gap, never a dropped term
#guard (scalarAdd (.alg 0 1 2) (.alg 0 1 5)).toOption == none
#guard (scalarMul (.alg 0 1 2) (.bool true)).toOption == none
-- a rational rides in every field
#guard (scalarAdd (.alg 0 1 2) (.rat (mkRat 1 2))).toOption
  == some (.alg (mkRat 1 2) 1 2)

-- equality is the normal form, and its two `false`s are theorems: a surd is
-- irrational, and different square-free radicands give different fields
#guard valueEq (.alg 0 1 2) (.alg 0 1 2) == some true
#guard valueEq (.alg 0 1 2) (.alg 0 1 5) == some false
#guard valueEq (.alg 0 1 2) (.int 1) == some false
#guard valueEq (.int 1) (.alg 0 1 2) == some false
#guard valueEq (.alg 0 1 2) (.rat (mkRat 3 2)) == some false
#guard valueEq (.alg 0 1 2) (.bool true) == none
-- exact algebraic values are UNORDERED here — the real ones too, though ℝ is
-- ordered and `nonNegSurd` already decides a sign by squaring. A documented
-- ceiling (DESIGN.md §Ceilings), not a claim that √2 and 2 are incomparable
#guard scalarCmp (.alg 0 1 2) (.int 2) == none

/-! ### The approximation certificate (SPEC.md §Exact number systems, #7)

A decimal is a CLAIM about the value it presents, and `Value.mkApprox` is
where that claim is checked — exactly, by the squaring comparison, with no
float anywhere. These guards are the claim itself: the same digits that pass
must fail one power of ten further in. -/

private def eps10 (k : Nat) : Rat := mkRat 1 (10 ^ k)

private def approx (exact : Value) (dec : String) (eps achieved : Rat) : Option Value :=
  (Value.mkApprox exact dec eps achieved).toOption

-- a decimal string denotes the rational it spells, sign and all
#guard Value.decimalToRat? "1.4142135623" == some (mkRat 14142135623 10000000000)
#guard Value.decimalToRat? "-0.5" == some (-(mkRat 1 2))
#guard Value.decimalToRat? "7" == some 7
#guard Value.decimalToRat? "0.500" == some (mkRat 1 2)
-- …and anything that is not a decimal is refused rather than read leniently
#guard Value.decimalToRat? "1/2" == none
#guard Value.decimalToRat? "1.2.3" == none
#guard Value.decimalToRat? "" == none
#guard Value.decimalToRat? "1e-10" == none
#guard Value.decimalToRat? " 1.5" == none

-- `|a + b√d| < q` by squaring: √2 - 1.4142135623 is under 10^-10 and over
-- 10^-11, which is the whole content of "ten digits of √2"
#guard Value.absLtRat (-(mkRat 14142135623 10000000000)) 1 2 (eps10 10)
#guard !Value.absLtRat (-(mkRat 14142135623 10000000000)) 1 2 (eps10 11)
-- the rational case compares strictly on its own
#guard Value.absLtRat (mkRat 1 2) 0 1 (mkRat 3 4)
#guard !Value.absLtRat (mkRat 1 2) 0 1 (mkRat 1 2)

-- SPEC.md's own line: √2 to O(1/10^{10}) is 1.4142135623, and the value keeps
-- the exact number it approximates
#guard approx (.alg 0 1 2) "1.4142135623" (eps10 10) (eps10 10)
  == some (.approx (.alg 0 1 2) "1.4142135623" (eps10 10) (eps10 10))
-- the BOUND is what is checked, not a spelling: √2 = 1.41421356237…, so the
-- rounded tenth digit satisfies the same certificate and the choice between
-- truncating and rounding stays the backend's
#guard approx (.alg 0 1 2) "1.4142135624" (eps10 10) (eps10 10)
  == some (.approx (.alg 0 1 2) "1.4142135624" (eps10 10) (eps10 10))
-- …and every way of lying about it is refused at the constructor: a digit that
-- is wrong at that bound, a bound not achieved, and a bound that does not meet
-- the request
#guard approx (.alg 0 1 2) "1.4142145623" (eps10 10) (eps10 10) == none
#guard approx (.alg 0 1 2) "1.414213562" (eps10 10) (eps10 10) == none
#guard approx (.alg 0 1 2) "1.414" (eps10 2) (eps10 10) == none
#guard approx (.alg 0 1 2) "1.414" (eps10 10) (eps10 3) == none
#guard approx (.alg 0 1 2) "1.4142135623" (eps10 10) 0 == none
-- a complex value has no decimal presentation here, and says so
#guard approx (.alg 2 2 (-1)) "2.8284271247" (eps10 10) (eps10 10) == none

-- an approximation has NO arithmetic: it carries a requested tolerance, not an
-- error term, so it shares a kind with nothing — including another one
#guard promote (.approx (.int 1) "1.0" (eps10 1) (eps10 1))
  (.approx (.int 1) "1.0" (eps10 1) (eps10 1)) == none
#guard promote (.approx (.int 1) "1.0" (eps10 1) (eps10 1)) (.int 1) == none
#guard (scalarAdd (.approx (.int 1) "1.0" (eps10 1) (eps10 1)) (.int 1)).toOption == none
#guard valueEq (.approx (.int 1) "1.0" (eps10 1) (eps10 1)) (.int 1) == none
#guard scalarCmp (.approx (.int 1) "1.0" (eps10 1) (eps10 1)) (.int 1) == none

-- the tolerance is displayed in SPEC.md's own spelling, and so is the value
#guard Value.tolText (eps10 10) == "1/10^{10}"
#guard Value.tolText (mkRat 1 3) == "1/3"
#guard Value.tolText (mkRat 3 100) == "3/100"
#guard Value.tolText 1 == "1"
#guard (Value.approx (.alg 0 1 2) "1.4142135623" (eps10 10) (eps10 10)).render
  == "1.4142135623 + O(1/10^{10})"

#guard domainCard (.mod 6) == some (.finite 6)
#guard domainCard (.mod 0) == some .countablyInfinite
#guard domainCard (.poly .rat) == some .countablyInfinite
#guard domainCard (.matrix 2 (.mod 3)) == some (.finite 81)
-- ℝ is uncountable and a function domain is not enumerated here: the slice
-- reports that it cannot state the cardinality rather than inventing ℵ₀
#guard domainCard .real == none
#guard domainCard (.funcs .real .real) == none
#guard domainCard (.poly .real) == none

#guard intEnum 0 == 0
#guard intEnum 1 == 1
#guard intEnum 2 == -1
#guard intEnum 3 == 2
#guard intEnum 4 == -2

-- the ℚ convention: 0, then the Cantor zigzag interleaved with negatives
#guard ratEnum 0 == 0
#guard ratEnum 1 == 1
#guard ratEnum 2 == -1
#guard ratEnum 3 == mkRat 1 2
#guard ratEnum 4 == -(mkRat 1 2)
#guard ratEnum 5 == 2
#guard ratEnum 6 == -2
#guard ratEnum 7 == mkRat 1 3
#guard ratEnum 9 == 3
#guard ratEnum 11 == mkRat 1 4
#guard ratEnum 13 == mkRat 2 3
#guard ratEnum 15 == mkRat 3 2
#guard ratEnum 17 == 4
-- injectivity on a prefix: no fraction repeats (reduced-skipping works)
#guard ((List.range 100).map ratEnum).eraseDups.length == 100

/-! ## Native executors -/

private def ints (vs : List Int) : Array Value := (vs.map Value.int).toArray

private def polyObj (d : Domain) (cs : Array Value) : Obj :=
  .elem (.poly d) (Value.mkPoly d cs)

private def out (opId : String) (o : Obj) (args : Array Obj) : Option Value :=
  (Native.run opId o args).toOption

-- Horner: 1 + 2x + x² at 3
#guard out "poly_eval" (polyObj .int (ints [1, 2, 1])) #[.elem .int (.int 3)] ==
  some (.int 16)

-- mixed ℤ/ℚ coefficients promote along ℤ ⊆ ℚ: 1/2 + x at 2
#guard out "poly_eval" (polyObj .rat #[.rat (mkRat 1 2), .int 1])
    #[.elem .int (.int 2)] == some (.rat (mkRat 5 2))

-- a ℤ/n coefficient domain evaluates in ℤ/n: 3 + 4x at 3 mod 5
#guard out "poly_eval" (polyObj (.mod 5) #[.mod 5 3, .mod 5 4])
    #[.elem (.mod 5) (.mod 5 3)] == some (.mod 5 0)

#guard out "poly_eval" (.elem .int (.int 3)) #[.elem .int (.int 1)] == none

-- nth: ℕ, the registered ℤ convention 0, 1, −1, 2, −2, …, and the ℚ zigzag
#guard out "nth" (.domainObj .nat) #[.elem .nat (.int 7)] == some (.int 7)
#guard out "nth" (.setObj (.domainSet .int)) #[.elem .nat (.int 4)] == some (.int (-2))
#guard out "nth" (.domainObj .rat) #[.elem .nat (.int 3)] == some (.rat (mkRat 1 2))

-- nth on a finite set is partial outside its cardinality
#guard out "nth" (.setObj (.finite .int (ints [10, 20, 30]))) #[.elem .nat (.int 1)] ==
  some (.int 20)
#guard out "nth" (.setObj (.finite .int (ints [10, 20, 30]))) #[.elem .nat (.int 3)] == none
#guard out "nth" (.setObj (.finite .int (ints [10]))) #[.elem .nat (.int (-1))] == none

-- nth on progressions, bounded and unbounded
#guard out "nth" (.setObj (.arithProg .nat (.int 0) (.int 2) none))
    #[.elem .nat (.int 4)] == some (.int 8)
#guard out "nth" (.setObj (.arithProg .nat (.int 0) (.int 2) (some (.int 8))))
    #[.elem .nat (.int 4)] == some (.int 8)
#guard out "nth" (.setObj (.arithProg .nat (.int 0) (.int 2) (some (.int 8))))
    #[.elem .nat (.int 5)] == none

-- cardinality
#guard out "cardinality" (.setObj (.finite .int (ints [1, 2, 2, 3]))) #[] ==
  some (.cardinal (.finite 3))
#guard out "cardinality" (.setObj (.arithProg .nat (.int 0) (.int 2) (some (.int 8)))) #[] ==
  some (.cardinal (.finite 5))
#guard out "cardinality" (.setObj (.arithProg .nat (.int 0) (.int 2) none)) #[] ==
  some (.cardinal .countablyInfinite)
#guard out "cardinality" (.domainObj .rat) #[] == some (.cardinal .countablyInfinite)
#guard out "cardinality" (.domainObj (.mod 6)) #[] == some (.cardinal (.finite 6))
-- a cardinality this slice cannot state is a loud failure, not a guess
#guard out "cardinality" (.domainObj .real) #[] == none
#guard out "set_eq" (.domainObj .real) #[.domainObj .real] == none

-- contains
#guard out "contains" (.setObj (.arithProg .nat (.int 0) (.int 2) none))
    #[.elem .int (.int 8)] == some (.bool true)
#guard out "contains" (.setObj (.arithProg .nat (.int 0) (.int 2) none))
    #[.elem .int (.int 9)] == some (.bool false)
#guard out "contains" (.setObj (.arithProg .nat (.int 0) (.int 2) (some (.int 8))))
    #[.elem .int (.int 10)] == some (.bool false)
#guard out "contains" (.setObj (.arithProg .int (.int 0) (.int (-3)) none))
    #[.elem .int (.int (-6))] == some (.bool true)
#guard out "contains" (.setObj (.finite .rat #[.rat (mkRat 1 2)]))
    #[.elem .rat (.rat (mkRat 2 4))] == some (.bool true)
#guard out "contains" (.domainObj .nat) #[.elem .int (.int (-1))] == some (.bool false)
-- a matrix belongs to Matₙ(e) when its SIZE agrees and its entries do; a
-- function's domain is the arrow it was declared over. Both are decided, so
-- both false cases are answers rather than refusals
#guard out "contains" (.domainObj (.matrix 2 .rat)) #[Std.mat2Q] == some (.bool true)
#guard out "contains" (.domainObj (.matrix 3 .rat)) #[Std.mat2Q] == some (.bool false)
#guard out "contains" (.domainObj (.matrix 2 (.mod 5))) #[Std.mat2Q] == some (.bool false)
#guard out "contains" (.domainObj (.funcs .nat .nat)) #[Std.doubling] == some (.bool true)
#guard out "contains" (.domainObj (.funcs .nat .int)) #[Std.doubling] == some (.bool false)
#guard out "contains" (.domainObj .int) #[.elem .rat (.rat (mkRat 1 2))] ==
  some (.bool false)

-- set equality by presentation normalization: {0, 1, 2, ...} IS ℕ as a set,
-- whatever domain tag the progression carries
#guard out "set_eq" (.setObj (.arithProg .int (.int 0) (.int 1) none))
    #[.domainObj .nat] == some (.bool true)
#guard out "set_eq" (.setObj (.arithProg .nat (.int 1) (.int 1) none))
    #[.domainObj .nat] == some (.bool false)
#guard out "set_eq" (.setObj (.arithProg .int (.int 1) (.int 1) (some (.int 4))))
    #[.setObj (.finite .int (ints [4, 3, 2, 1]))] == some (.bool true)
#guard out "set_eq" (.setObj (.finite .int (ints [1, 2, 2])))
    #[.setObj (.finite .rat #[.rat 2, .rat 1])] == some (.bool true)
#guard out "set_eq" (.domainObj .int) #[.domainObj .nat] == some (.bool false)
#guard out "set_eq" (.domainObj (.mod 3))
    #[.setObj (.finite (.mod 3) #[.mod 3 2, .mod 3 0, .mod 3 1])] == some (.bool true)
-- past the expansion cap the operation fails honestly rather than guessing
#guard out "set_eq" (.setObj (.arithProg .nat (.int 0) (.int 1) (some (.int 100000))))
    #[.domainObj .nat] == none

/-! ### SPEC.md §Finite sets: the binary operations, inclusion, and the two
DENOTED presentations

`A × B` and `𝒫(A)` are presentations rather than element lists (`Value` has
no pair and no set-as-element), so `cardinality` reads them by exact cardinal
arithmetic while every operation that would need their elements refuses. -/

private def finSet (vs : List Int) : Obj := .setObj (.finite .int (ints vs))

private def A123 : SetPresentation := .finite .int (ints [1, 2, 3])

/-- `{0, 2, 4, ...}` — the progression SPEC.md's `{2n | n ∈ ℕ}` denotes. -/
private def evens : Obj := .setObj (.arithProg .nat (.int 0) (.int 2) none)

#guard out "set_union" (finSet [1, 2, 3]) #[finSet [3, 4, 5]] ==
  some (.setV (ints [1, 2, 3, 4, 5]) .int)
#guard out "set_intersect" (finSet [1, 2, 3]) #[finSet [3, 4, 5]] ==
  some (.setV (ints [3]) .int)
#guard out "set_diff" (finSet [1, 2, 3]) #[finSet [3, 4, 5]] ==
  some (.setV (ints [1, 2]) .int)
#guard out "set_symdiff" (finSet [1, 2, 3]) #[finSet [3, 4, 5]] ==
  some (.setV (ints [1, 2, 4, 5]) .int)
-- the result is a SET: a repeated element is not a second one
#guard out "set_union" (finSet [1, 1]) #[finSet [1]] == some (.setV (ints [1]) .int)
-- mixing element domains is refused, never joined: this backend cannot read
-- the preferred-canonical-map registry the surface joins literals with
#guard out "set_union" (finSet [1])
    #[.setObj (.finite .rat #[.rat (mkRat 1 2)])] == none
-- …and an infinite ARGUMENT is refused too, though only the receiver is routed
#guard out "set_union" (finSet [1]) #[.domainObj .int] == none

#guard out "subset" (finSet [1, 2]) #[finSet [1, 2, 3]] == some (.bool true)
#guard out "subset" (finSet [1, 4]) #[finSet [1, 2, 3]] == some (.bool false)
#guard out "subset" (finSet [1, 2]) #[.domainObj .int] == some (.bool true)
#guard out "subset" (.setObj (.finite .rat #[.rat (mkRat 1 2)])) #[.domainObj .int] ==
  some (.bool false)
#guard out "subset" (.setObj (.arithProg .nat (.int 0) (.int 2) none))
    #[.domainObj .nat] == some (.bool true)
-- a progression running the other way leaves ℕ at once
#guard out "subset" (.setObj (.arithProg .int (.int 0) (.int (-2)) none))
    #[.domainObj .nat] == some (.bool false)
-- an infinite normal form is not inside a finite list — provably false
#guard out "subset" (.domainObj .int) #[finSet [1, 2]] == some (.bool false)
-- against a PROGRESSION: an explicit list is decided elementwise…
#guard out "subset" (finSet [2, 4]) #[evens] == some (.bool true)
#guard out "subset" (finSet [1, 2, 3]) #[evens] == some (.bool false)
-- …the same progression contains itself…
#guard out "subset" evens #[evens] == some (.bool true)
-- …and the two the presentations do NOT settle refuse rather than guess:
-- {0,4,8,…} ⊆ {0,2,4,…} is true and ℕ ⊆ {0,½,1,…} would be too
#guard out "subset" (.setObj (.arithProg .nat (.int 0) (.int 4) none)) #[evens] == none
#guard out "subset" (.domainObj .nat) #[evens] == none
-- …but ℕ ⊆ ℤ is the canonical-map registry's claim, and this backend refuses
-- to restate it rather than answering it twice
#guard out "subset" (.domainObj .nat) #[.domainObj .int] == none

#guard out "cardinality" (.setObj (.product A123 (.finite .int (ints [3, 4, 5])))) #[] ==
  some (.cardinal (.finite 9))
#guard out "cardinality" (.setObj (.powerset A123)) #[] == some (.cardinal (.finite 8))
-- the empty factor wins over an infinite one
#guard out "cardinality" (.setObj (.product (.finite .int #[]) (.domainSet .nat))) #[] ==
  some (.cardinal (.finite 0))
#guard out "cardinality" (.setObj (.product (.domainSet .nat) (.domainSet .nat))) #[] ==
  some (.cardinal .countablyInfinite)
-- 𝒫(ℕ) is uncountable: this slice says it cannot state that, never ℵ₀
#guard out "cardinality" (.setObj (.powerset (.domainSet .nat))) #[] == none
-- and 2^n stops being worth materializing past `powersetExpCap`: pinned at
-- the boundary ITSELF, so a `<`/`≤` slip moves one of these
#guard out "cardinality" (.setObj (.powerset (.domainSet (.mod 4096)))) #[]
  == some (.cardinal (.finite (2 ^ 4096)))
#guard out "cardinality" (.setObj (.powerset (.domainSet (.mod 4097)))) #[] == none

-- membership in a powerset IS inclusion, decided by the same procedure
#guard out "contains" (.setObj (.powerset A123)) #[finSet [1, 2]] == some (.bool true)
#guard out "contains" (.setObj (.powerset A123)) #[finSet [1, 4]] == some (.bool false)
-- a product has pairs for elements, which no `Value` presents
#guard out "contains" (.setObj (.product A123 A123)) #[.elem .int (.int 1)] == none
-- …and an ELEMENT is not a candidate for membership in a powerset, whose
-- members are sets: the argument is refused rather than read as a singleton
#guard out "contains" (.setObj (.powerset A123)) #[.elem .int (.int 1)] == none
-- neither denoted set has a canonical form to compare
#guard out "set_eq" (.setObj (.powerset A123)) #[.setObj (.powerset A123)] == none

-- SPEC.md's `|A| = 3` and `|E| = ℵ₀`: a finite cardinal answers to the
-- number counting it, and ℵ₀ answers to no integer
#guard valueEq (.cardinal (.finite 3)) (.int 3) == some true
#guard valueEq (.int 3) (.cardinal (.finite 3)) == some true
#guard valueEq (.cardinal (.finite 3)) (.int 4) == some false
#guard valueEq (.cardinal (.finite 3)) (.int (-1)) == some false
#guard valueEq (.cardinal .countablyInfinite) (.int 3) == some false
#guard valueEq (.cardinal .countablyInfinite) (.cardinal .countablyInfinite) == some true
-- …and `2^|A|` exponentiates by it, while `2^ℵ₀` has no exponent here
#guard (scalarPow (.int 2) (.cardinal (.finite 3))).toOption == some (.int 8)
#guard (scalarPow (.int 2) (.cardinal .countablyInfinite)).toOption == none

/-! ### SPEC.md §Exact number systems: the complex plane

`z.re()`, `z.im()`, `z.bar()`, `|z|` — structural reads of `a + b√d`, so the
engine decides them and no backend is asked. A REAL receiver is its own real
part, has no imaginary part, and is its own conjugate: ℝ ⊆ ℂ, spelled out. -/

private def zC : Obj := .elem .complex (.alg 2 2 (-1))
private def r2 : Obj := .elem .real (.alg 0 1 2)

#guard out "alg_re" zC #[] == some (.int 2)
#guard out "alg_im" zC #[] == some (.int 2)
#guard out "alg_conj" zC #[] == some (.alg 2 (-2) (-1))
#guard out "alg_abs" zC #[] == some (.alg 0 2 2)
-- the imaginary part is the REAL coefficient of i, and it carries the radical
-- when the radicand is not −1: im(2i√3) is 2√3
#guard out "alg_im" (.elem .complex (.alg 0 2 (-3))) #[] == some (.alg 0 2 3)
-- a real receiver, in all four
#guard out "alg_re" r2 #[] == some (.alg 0 1 2)
#guard out "alg_im" r2 #[] == some (.int 0)
#guard out "alg_conj" r2 #[] == some (.alg 0 1 2)
#guard out "alg_abs" r2 #[] == some (.alg 0 1 2)
-- …and the modulus of a real surd is exact on both sides of zero: the sign of
-- `a + b√d` is decided by squaring, never by evaluating a decimal
#guard out "alg_abs" (.elem .real (.alg 0 (-1) 2)) #[] == some (.alg 0 1 2)
#guard out "alg_abs" (.elem .real (.alg 1 (-1) 2)) #[] == some (.alg (-1) 1 2)
#guard out "alg_abs" (.elem .real (.alg 2 (-1) 2)) #[] == some (.alg 2 (-1) 2)
-- the OTHER inverted quadrant, `b > 0 > a`, where the comparison flips: the
-- sign is `a² ⋛ b²d` read the other way round, so −1 + √2 (≈ 0.41) stays and
-- −3 + 2√2 (≈ −0.17) turns over. Both decided by squaring, never by a decimal
#guard out "alg_abs" (.elem .real (.alg (-1) 1 2)) #[] == some (.alg (-1) 1 2)
#guard out "alg_abs" (.elem .real (.alg (-3) 2 2)) #[] == some (.alg 3 (-2) 2)
#guard out "alg_abs" (.elem .real (.rat (mkRat (-3) 2))) #[] == some (.rat (mkRat 3 2))
-- a receiver carrying no exact number is the loud runtime error partiality
-- inside a routed shape always gets
#guard out "alg_re" (.elem .real (.bool true)) #[] == none
#guard out "alg_re" (.domainObj .complex) #[] == none

-- membership in ℝ and ℂ, which is what SPEC.md's `√2 ∈ ℝ` and `2 + 2i ∈ ℂ` ask
#guard out "contains" (.domainObj .real) #[r2] == some (.bool true)
#guard out "contains" (.domainObj .complex) #[zC] == some (.bool true)
-- …and the two that must NOT hold: a non-real surd is not in ℝ, and no surd
-- is rational
#guard out "contains" (.domainObj .real) #[zC] == some (.bool false)
#guard out "contains" (.domainObj .rat) #[r2] == some (.bool false)
#guard out "contains" (.domainObj .complex) #[.elem .int (.int 3)] == some (.bool true)
#guard out "contains" (.domainObj .real) #[.elem (.mod 5) (Value.mkMod 5 2)]
  == some (.bool false)
-- ℝ and ℂ are uncountable, and this slice says so rather than answering ℵ₀
#guard out "cardinality" (.domainObj .complex) #[] == none

/-! ### `ℂ - ℚ` (SPEC.md §Polynomials)

A DENOTED difference of two domains: membership is decided pointwise, and
everything that would need an element list refuses. The minimal presentation
the assertion needs, and nothing wider. -/

private def cMinusQ : Obj := .setObj (.domainDiff .complex .rat)

#guard out "contains" cMinusQ #[r2] == some (.bool true)
#guard out "contains" cMinusQ #[zC] == some (.bool true)
-- a rational is in ℂ and in ℚ, so it is NOT in the difference
#guard out "contains" cMinusQ #[.elem .int (.int 1)] == some (.bool false)
#guard out "contains" cMinusQ #[.elem .rat (.rat (mkRat 1 2))] == some (.bool false)
-- …and the first domain still has to hold: a residue class is in neither
#guard out "contains" cMinusQ #[.elem (.mod 5) (Value.mkMod 5 2)] == some (.bool false)
-- SPEC.md's `q.roots() ⊆ ℂ - ℚ`, over an explicit finite set
#guard out "subset" (.setObj (.finite .complex #[.alg 0 1 2, .alg 0 (-1) 2]))
    #[cMinusQ] == some (.bool true)
#guard out "subset" (.setObj (.finite .complex #[.alg 0 1 2, .int 1]))
    #[cMinusQ] == some (.bool false)
-- everything that would need an element list of it refuses, loudly
#guard out "cardinality" cMinusQ #[] == none
#guard out "set_eq" cMinusQ #[cMinusQ] == none
#guard out "subset" cMinusQ #[cMinusQ] == none
#guard out "nth" cMinusQ #[.elem .nat (.int 0)] == none
-- a set of exact algebraic values compares as a SET: dedupe and equality are
-- order-free, because ℂ has no order this slice would be honest claiming
#guard out "set_eq" (.setObj (.finite .complex #[.alg 0 1 2, .alg 0 (-1) 2]))
    #[.setObj (.finite .complex #[.alg 0 (-1) 2, .alg 0 1 2])] == some (.bool true)
#guard out "set_eq" (.setObj (.finite .complex #[.alg 0 1 2]))
    #[.setObj (.finite .complex #[.alg 0 1 5])] == some (.bool false)
#guard out "cardinality" (.setObj (.finite .complex #[.alg 0 1 2, .alg 0 1 2])) #[]
  == some (.cardinal (.finite 1))

#guard out "annihilator_cyclic" (.cyclicModule 12) #[] ==
  some (.idealV #[.int 12] .int)
#guard out "annihilator_cyclic" (.domainObj .int) #[] == none

#guard out "no_such_op" (.domainObj .int) #[] == none

/-! ## Pattern subsumption (the op-signature order) -/

#guard DomainPattern.implies (.exact (.mod 5)) .anyMod
#guard !DomainPattern.implies .anyMod (.exact (.mod 5))
#guard DomainPattern.implies (.exact (.poly .int)) (.polyOver .anyDom)
#guard DomainPattern.implies (.polyOver (.exact .int)) (.polyOver .anyDom)
#guard !DomainPattern.implies (.polyOver .anyDom) (.polyOver (.exact .int))
#guard DomainPattern.implies .anyMod .anyDom
#guard !DomainPattern.implies .anyDom .anyMod

#guard PresPattern.implies (.elemOf (.exact .int)) (.elemOf .anyDom)
#guard PresPattern.implies (.domainIs (.exact .rat)) .anySet
#guard PresPattern.implies .finiteSet .anySet
#guard PresPattern.implies (.progression .anyDom) .anySet
#guard !PresPattern.implies .anySet (.domainIs (.exact .rat))
#guard PresPattern.implies .cyclicMod .anyObj
#guard PresPattern.implies .productSet .anySet
#guard PresPattern.implies .powersetSet .anySet
#guard !PresPattern.implies .anySet .powersetSet
#guard !PresPattern.implies .productSet .powersetSet
-- an element is not a set: no cross-shape leniency
#guard !PresPattern.implies (.elemOf .anyDom) .anySet

/-! ## Executor table (the one `IO` surface) -/

private def probe (backend : Name) (opId : String) : Route :=
  { method := `probe, pattern := .anyObj, backend, opId }

#eval show IO Unit from do
  registerExecutor `casdslTestDummy fun opId _ _ =>
    return .ok (.bool (opId == "ping"))
  let r ← execute (probe `casdslTestDummy "ping") (.domainObj .int) #[]
  unless r.toOption == some (.bool true) do
    throw <| IO.userError "registered executor did not run"
  match ← execute (probe `casdslTestNoSuchBackend "ping") (.domainObj .int) #[] with
  | .error (.backendUnavailable ..) => pure ()
  | _ => throw <| IO.userError "a missing backend was not reported as unavailable"
  -- importing `CasDsl.Native` registers the native backend
  if (← getExecutor? `native).isNone then
    throw <| IO.userError "the native executor is not registered"
  let r ← execute (probe `native "annihilator_cyclic") (.cyclicModule 12) #[]
  unless r.toOption == some (.idealV #[.int 12] .int) do
    throw <| IO.userError "the native executor did not run through `execute`"
  -- The sage executor's ARGUMENT contract, which no `OpSig` covers (those
  -- constrain receivers). Both checks reject before the adapter is reached,
  -- so nothing here starts Sage.
  -- default-deny: a nullary op handed an argument REFUSES it, never drops it
  match ← Sage.executor "factor_int" (.elem .int (.int 360)) #[.elem .int (.int 2)] with
  | .error (.badRequest _) => pure ()
  | _ => throw <| IO.userError "a nullary sage op accepted an argument"
  -- …and the one op that takes an argument checks the count itself
  match ← Sage.executor "gcd_int" (.elem .int (.int 84))
      #[.elem .int (.int 30), .elem .int (.int 5)] with
  | .error (.badRequest _) => pure ()
  | _ => throw <| IO.userError "gcd_int accepted two arguments"

/-! ## Registries

The env extensions cannot be exercised without an `Environment`, so this
runs in the command elaborator. It never commits the environment it builds:
the registrations are local to this check. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let env := addCategory env { name := `SmokeSets }
  let env := addCategory env { name := `SmokeFinite, parents := #[`SmokeSets] }
  unless (catDecl? env `SmokeFinite).map (·.parents) == some #[`SmokeSets] do
    throwError "a registered category did not read back"
  if (addCategoryChecked env { name := `SmokeSets }).toOption.isSome then
    throwError "a duplicate category registration was not detected"

  let env := addMethod env { id := `smoke, receiver := `SmokeSets }
  let env := addMethod env { id := `smoke, receiver := `SmokeFinite }
  unless (methodDecls env `smoke).size == 2 do
    throwError "the same method id on two receivers must give two declarations"
  if (addMethodChecked env { id := `smoke, receiver := `SmokeSets }).toOption.isSome then
    throwError "a duplicate (id, receiver) method registration was not detected"

  let r : Route := { method := `smoke, pattern := .anySet, backend := `native, opId := "cardinality" }
  let env := addRoute env r
  unless (routesFor env `smoke).size == 1 && (routesFor env `other).isEmpty do
    throwError "routes are not looked up by method id"
  if (addRouteChecked env r).toOption.isSome then
    throwError "a duplicate route registration was not detected"

  -- the op-signature check (the imported env carries the backends' OpSigs):
  -- a route may not name an op the backend never declared…
  let unknownOp : Route := { method := `smoke2, pattern := .anySet, backend := `native, opId := "no_such_op" }
  if (addRouteChecked env unknownOp).toOption.isSome then
    throwError "a route naming an undeclared op was not rejected"
  -- …nor a pattern wider than the op's declared signature…
  let tooWide : Route := { method := `smoke2, pattern := .anyObj, backend := `native, opId := "cardinality" }
  if (addRouteChecked env tooWide).toOption.isSome then
    throwError "a route wider than its op's signature was not rejected"
  let wrongShape : Route := { method := `smoke2, pattern := .elemOf (.polyOver (.exact .rat)), backend := `sage, opId := "factor_poly_z" }
  if (addRouteChecked env wrongShape).toOption.isSome then
    throwError "a route sending ℚ[x] elements to the ℤ[x] op was not rejected"
  -- …while a route inside the signature registers
  let inside : Route := { method := `smoke2, pattern := .finiteSet, backend := `native, opId := "cardinality" }
  unless (addRouteChecked env inside).toOption.isSome do
    throwError "a route inside its op's signature must register"
  -- and the signature itself is single-statement data
  let dupSig : OpSig := { backend := `native, opId := "cardinality", accepts := #[.anySet] }
  if (addOpSigChecked env dupSig).toOption.isSome then
    throwError "a duplicate op-signature registration was not detected"

  let env := addProfileRule env { pattern := .anySet, cat := `SmokeSets, slots := #[] }
  -- containment, not exact equality: this module's environment also carries
  -- the imported `CasDsl.Std` profile rules, which legitimately apply too
  unless (profileOf env (.domainObj .int)).contains ⟨`SmokeSets, #[]⟩ do
    throwError "a registered profile rule did not apply"
  unless (resolveMethod env (.domainObj .int) `smoke).toOption.map (·.decl.receiver)
      == some `SmokeSets do
    throwError "resolveMethod did not reach the registered declaration"

  -- rebinding shadows; a representative label is registered once
  let env := addBinding env (`x, .elem .int (.int 1))
  let env := addBinding env (`x, .elem .int (.int 2))
  unless binding? env `x == some (.elem .int (.int 2)) do
    throwError "the latest binding of a name must win"
  let env := addRepresentative env ("ℤ", .domainObj .int)
  if (addRepresentativeChecked env ("ℤ", .domainObj .nat)).toOption.isSome then
    throwError "a duplicate representative label was not detected"

end CasDslTests
