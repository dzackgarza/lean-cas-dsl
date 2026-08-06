/-
Negative guards for the elaborating registration (SPEC-REGISTRY-TYPE-PREPASS
§3.4): a profile rule claiming a membership Lean cannot discharge must be
REFUSED at registration. The positive direction needs no separate test —
`CasDsl/Std.lean` now runs the same checks on every concrete standard rule,
so the library building IS the positive proof.
-/
-- deliberately NOT the root: importing `CasDsl` would bring the DSL grammar,
-- whose set-builder `{ … }` shadows anonymous-constructor braces here
import CasDsl.Std
import CasDsl.Mathlib.Verify

namespace CasDslTests

open Lean Elab Command CasDsl

/-- Expect a registration to fail; the test fails if it commits. -/
private def mustRefuse (what : String) (act : CommandElabM Unit)
    : CommandElabM Unit := do
  let committed ← try act; pure true catch _ => pure false
  if committed then
    throwError "a false membership was registered: {what}"

-- ℤ/6 is not even a domain, so it is certainly not euclidean — and not a
-- UFD either
run_cmd do
  let asEuclidean : ProfileRule :=
    { pattern := .elemOf (.exact (.mod 6)), cat := `EuclideanElems,
      slots := #[.elemDom] }
  mustRefuse "ℤ/6 as euclidean-domain elements" (registerProfileRule! asEuclidean)
  let asUFD : ProfileRule :=
    { pattern := .elemOf (.exact (.mod 6)), cat := `FactorizationElems,
      slots := #[.elemDom] }
  mustRefuse "ℤ/6 as UFD elements" (registerProfileRule! asUFD)

-- ℝ is uncountable (Anchors.lean holds the positive Mathlib theorem), and
-- so is ℝ[x]
run_cmd do
  let realCountable : ProfileRule :=
    { pattern := .domainIs (.exact .real), cat := `CountableSets,
      slots := #[.setDom] }
  mustRefuse "ℝ as a countable set" (registerProfileRule! realCountable)
  let realPolyCountable : ProfileRule :=
    { pattern := .domainIs (.polyOver (.exact .real)), cat := `CountableSets,
      slots := #[.setDom] }
  mustRefuse "ℝ[x] as a countable set" (registerProfileRule! realPolyCountable)

-- a category may not cite a telescope entry that is not a class
run_cmd do
  let bogus : CatDecl := { name := `BogusCat, anchor := ``Nat,
                           telescope := #[`Nat.succ] }
  mustRefuse "a telescope naming a non-class" (registerCategory! bogus)
  let unanchored : CatDecl := { name := `SmallModules }
  mustRefuse "a category denoting nothing in Mathlib" (registerCategory! unanchored)

/-! ## The runtime tripwire (invariant I7)

Registration refuses false CONCRETE memberships, but the pure adders — and,
in principle, family patterns — can still put the walk and Mathlib in
disagreement. `verifyResolution` catches it at the call. Simulated drift:
the pure adder admits ℤ/6 into EuclideanElems without the semantic check;
the walk then proposes `factor`, and Mathlib refuses it. -/

run_cmd do
  let env ← getEnv
  let drifted : ProfileRule :=
    { pattern := .elemOf (.exact (.mod 6)), cat := `EuclideanElems,
      slots := #[.elemDom] }
  let env' ← match addProfileRuleChecked env drifted with
    | .ok e => pure e
    | .error msg => throwError "the pure adder refused the drift fixture: {msg}"
  let six : Obj := .elem (.mod 6) (Value.mkMod 6 5)
  let res ← match resolveMethod env' six `factor with
    | .ok r => pure r
    | .error _ => throwError "the walk did not even propose factor for ℤ/6"
  match ← verifyResolution env' res.profileEntry.name res.decl.receiver (res.concreteReceiver six) with
  | some _ => pure ()   -- the tripwire fired: Mathlib refused the drift
  | none => throwError "verifyResolution accepted a membership Mathlib refutes"

end CasDslTests
