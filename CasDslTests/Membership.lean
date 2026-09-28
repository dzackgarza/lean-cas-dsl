/-
Negative guards for the elaborating registration (SPEC-REGISTRY-TYPE-PREPASS
§3.4): a typing rule claiming a membership Lean cannot discharge must be
REFUSED at registration. The positive direction needs no separate test —
`CasDsl/Std.lean` runs the same checks on every concrete standard rule, so the
library building IS the positive proof.
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
  mustRefuse "ℤ/6 as euclidean-domain elements" <| registerTypingRule!
    { pattern := .elemOf (.exact (.mod 6)), category := "cat.euclidean_points",
      classes := #[``EuclideanDomain] }
  mustRefuse "ℤ/6 as UFD elements" <| registerTypingRule!
    { pattern := .elemOf (.exact (.mod 6)), category := "cat.ufd_points",
      classes := #[``IsDomain, ``UniqueFactorizationMonoid] }

-- ℝ is uncountable (Anchors.lean holds the positive Mathlib theorem), and
-- so is ℝ[x]: neither is an enumeration
run_cmd do
  mustRefuse "ℝ as an enumerated set" <| registerTypingRule!
    { pattern := .domainIs (.exact .real), category := "cat.enumerations",
      classes := #[``Countable] }
  mustRefuse "ℝ[x] as an enumerated set" <| registerTypingRule!
    { pattern := .domainIs (.polyOver (.exact .real)), category := "cat.enumerations",
      classes := #[``Countable] }

-- a typing rule may only name a registered category, and only classes
run_cmd do
  mustRefuse "a rule into an unregistered category" <| registerTypingRule!
    { pattern := .elemOf (.exact (.mod 7)), category := "cat.nice_posets" }
  mustRefuse "a rule citing a non-class" <| registerTypingRule!
    { pattern := .elemOf (.exact (.mod 7)), category := "cat.ring_points",
      classes := #[``Nat.succ] }

/-! ## The runtime tripwire (invariant I7)

Registration refuses false CONCRETE memberships, but the pure adders — and,
in principle, family patterns — can still put the typing and Mathlib in
disagreement. `verifyTyping` catches it at the call. Simulated drift: the pure
adder types ℤ/6 in euclidean domains without the semantic check; the call of
`factor` then fails, naming the class Mathlib refuses. -/

run_cmd do
  let env ← getEnv
  let env' ← match addTypingRuleChecked env
      { pattern := .elemOf (.exact (.mod 6)), category := "cat.euclidean_points",
        classes := #[``EuclideanDomain] } with
    | .ok e => pure e
    | .error msg => throwError "the pure adder refused the drift fixture: {msg}"
  let six : Obj := .elem (.mod 6) (Value.mkMod 6 5)
  match ← (realizationOf env' six `factor false : IO _) with
  | .error msg =>
      unless (msg.splitOn "Lean cannot synthesize EuclideanDomain").length > 1 do
        throwError "the drifted call failed for another reason: {msg}"
  | .ok _ => throwError "verifyTyping accepted a membership Mathlib refutes"

end CasDslTests
