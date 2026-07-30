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

#guard promote (.int 3) (.rat (mkRat 1 2)) == some (.rat 3, .rat (mkRat 1 2))
#guard promote (.int 7) (.mod 5 3) == some (.mod 5 2, .mod 5 3)
#guard promote (.int 1) (.bool true) == none
#guard valueEq (.int 2) (.rat 2) == some true
#guard valueEq (.int 2) (.bool true) == none

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

#guard domainCard (.mod 6) == .finite 6
#guard domainCard (.mod 0) == .countablyInfinite
#guard domainCard (.poly .rat) == .countablyInfinite
#guard domainCard (.matrix 2 (.mod 3)) == .finite 81

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
