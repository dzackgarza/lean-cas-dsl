/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.TestSuite
public meta import CasAcceptance.Standard
public meta import CasCatalogue.TestSuite

@[expose] public section

/-!
# Acceptance for `gov-leaf-authority` (`specs/leaf-registration.md`)

Statements of the suite's kind are run through `CasCatalogue.Realize.run` over probe manifests
(`CasAcceptance/Strata/registration_*.json`) naming a probe backend program
(`probe_registration.py`, test scaffolding, not a leaf):

* **Lean decides, with no manifest at all.** The catalogue's judgements (`ℤ ⊆ ℚ`, `3 ∈ ℤ/5`)
  hold with no leaf installed: their propositions are proved by decision, checked by the kernel.
  So do the element and morphism equalities of `ℤ`, `ℤ/5` and `Fin(3)`, by the catalogue's
  decidable equality of morphisms of a concrete category. A false one (`2 + 3 = 6`) is refuted
  by Lean and invalid. What Lean does not decide and no registration computes is a gap:
  cardinalities.
* **A registration computes, through the port.** Registrations of `meth.cardinality` on the
  forms `obj.sets.fin` and `obj.sets.integers_mod_power` make `|Fin(3)| = 3`, `|(ℤ/4)^3| = 64`
  and `|(ℤ/0)^2| = ℵ₀` hold. A field a registration does not have is ignored. An object with no
  registration (`ℤ`) stays a gap.
* **The kernel walks the catalogue's route (CC-TRANSPORT).** `|Fin(3) in FiniteSets| = 3` holds
  through the registration on `obj.sets.fin` alone: the catalogue's refinement row sends
  `Fin(3)` in `FiniteSets` along the forgetful functor to `Fin(3)` in `Sets`, where the
  cardinality is computed. A registration on `obj.finite_sets.fin` itself is not admitted: it
  could never be selected.
* **A registered limit is an operation on its diagram (CC-UNIV, CC-DECODE).** Registrations of
  `lim.sets.product` and `lim.sets.pullback` on the diagrams of `Sets` (`cat.sets`) receive the
  diagram in its standard form, objects as named objects and arrows as graphs, and answer the
  cone: apex and legs. `|Fin(2) × ℤ/3| = 6` holds through the product's apex `Fin(6)` and the
  cardinality registered on `obj.sets.fin`; `|pullback(f, g)| = 3` through a pullback cone whose
  commutation the kernel decides. A cone missing a leg is malformed; a cone with the wrong apex
  makes the assertion wrong. A limit registered on an object form is not admitted.
* **A wrong answer is `wrong`, and changes nothing else.** The same registrations answering the
  constant `7` turn those assertions wrong; the statements Lean decides, and the gaps, are
  unchanged.
* **An answer outside the result form is `malformed`.**
* **A backend that cannot start is `unavailable`.**
* **A registration naming a non-catalogue operation, an unregistered form, a form the operation
  does not apply to, or an undeclared backend is not admitted**, and is reported with its reason.
-/

open Lean Elab Command

namespace CasCatalogue.RegistrationProbes

open Language Realize

/-- The probe manifests' directory. -/
meta def strata : System.FilePath := "CasAcceptance" / "Strata"

/-- An outcome's kind, as the suite reports it. -/
meta def kindOf : Outcome → String
  | .holds => "holds"
  | .gap _ => "gap"
  | .unavailable _ => "unavailable"
  | .wrong _ => "wrong"
  | .malformed _ => "malformed"

/-- Run `text` and require its outcome's kind. -/
meta def expect (harness : Harness) (kind : String) (text : String) : CommandElabM Unit := do
  let (outcome, _) ← runStatement harness {} text
  unless kindOf outcome == kind do
    throwError "`{text}` is {repr outcome}, not {kind}"

/-- Run `text` after the `let`s `lets`, and require its outcome's kind. -/
meta def expectIn (harness : Harness) (lets : List String) (kind : String) (text : String) :
    CommandElabM Unit := do
  let mut scope : Scope := {}
  for binding in lets do
    scope := (← runStatement harness scope binding).2
  let (outcome, _) ← runStatement harness scope text
  unless kindOf outcome == kind do
    throwError "`{text}` is {repr outcome}, not {kind}"

/-- Run `text` and require that it is invalid: its reading fails, or Lean refutes it. -/
meta def expectInvalid (harness : Harness) (text : String) : CommandElabM Unit := do
  let valid ← try (do discard <| runStatement harness {} text; pure true) catch _ => pure false
  if valid then throwError "`{text}` is not invalid"

/-- The harness of the probe manifest `name`, with what it rejects. -/
meta def harnessOf (name : String) : CommandElabM Harness :=
  liftCoreM (Harness.load (some (strata / name)))

meta def withHarness (name : String) (k : Harness → CommandElabM Unit) : CommandElabM Unit := do
  let harness ← harnessOf name
  try k harness finally (harness.stop : IO Unit)

-- Lean decides, with no manifest at all; what it does not decide, and nothing computes, is a gap.
run_cmd do
  let harness ← (Harness.empty : IO Harness)
  for text in ["assert ℤ ⊆ ℚ and ℚ ⊆ ℝ", "assert ℕ ⊆ ℂ", "assert 3 ∈ ℤ/5", "assert -3 ∈ ℤ",
      "assert 2 + 3 = 5", "assert 2 + 3 = 0 in ℤ/5", "assert 2 · 3 = 1 in ℤ/5",
      "assert rev(3) ∘ rev(3) = id(Fin(3))", "assert gcd(84, 30) = 6"] do
    expect harness "holds" text
  -- False mathematics that Lean decides is refuted: the statement is invalid, whatever is
  -- installed.
  expectInvalid harness "assert 2 + 3 = 6"
  for text in ["assert |Fin(3)| = 3", "assert |ℤ| = ℵ₀", "assert |(ℤ/4)^3| = 64",
      "assert implemented |Fin(3)|"] do
    expect harness "gap" text

-- A registration computes cardinalities through the port.
run_cmd withHarness "registration_correct.json" fun harness => do
  unless harness.rejected.isEmpty do throwError "rejected: {harness.rejected}"
  unless harness.admitted.size == 2 do throwError "admitted {harness.admitted.size} registrations"
  for text in ["assert |Fin(3)| = 3", "assert |Fin(3) in FiniteSets| = 3",
      "assert |(ℤ/4)^3| = 64", "assert |(ℤ/0)^2| = ℵ₀", "assert |(ℤ/5)^0| = 1",
      "assert implemented |Fin(3)|", "assert implemented |Fin(3) in FiniteSets|"] do
    expect harness "holds" text
  -- The transported receiver is the base at the same parameters: `Fin(4)` in `FiniteSets` is
  -- not `Fin(3)`.
  expect harness "wrong" "assert |Fin(4) in FiniteSets| = 3"
  -- Lean still decides what it decides; what has no registration is still a gap.
  expect harness "holds" "assert ℤ ⊆ ℚ"
  expect harness "gap" "assert |ℤ| = ℵ₀"
  expect harness "holds" "assert 2 + 3 = 5"
  -- A well-typed wrong answer is not a gap: the assertion is wrong.
  expect harness "wrong" "assert |Fin(3)| = 4"

-- A registered limit is computed as an operation on its diagram, and its answer is the cone.
run_cmd withHarness "registration_limits.json" fun harness => do
  unless harness.rejected.isEmpty do throwError "rejected: {harness.rejected}"
  unless harness.admitted.size == 3 do throwError "admitted {harness.admitted.size} registrations"
  expect harness "holds" "assert |Fin(2) × ℤ/3| = 6"
  expect harness "holds" "assert implemented Fin(2) × ℤ/3"
  expect harness "wrong" "assert |Fin(2) × ℤ/3| = 5"
  -- A pullback of graphs: the apex, its legs, and their commutation decided by the kernel.
  let maps := ["let f := {0 ↦ 0, 1 ↦ 1, 2 ↦ 1} : Fin(3) → Fin(2)",
               "let g := {0 ↦ 1, 1 ↦ 0} : Fin(2) → Fin(2)"]
  expectIn harness maps "holds" "assert |pullback(f, g)| = 3"
  expectIn harness maps "wrong" "assert |pullback(f, g)| = 2"
  -- A shape with no registration is still a gap; Lean still decides what it decides.
  expect harness "gap" "assert |Fin(2) ⊔ Fin(3)| = 5"
  expect harness "holds" "assert 2 + 3 = 5"

-- A cone missing a leg is not a value of the result form.
run_cmd withHarness "registration_limit_missing_leg.json" fun harness => do
  expect harness "malformed" "assert |Fin(2) × ℤ/3| = 6"
  expect harness "holds" "assert |Fin(3)| = 3"

-- A well-formed cone with the wrong apex makes the assertion wrong.
run_cmd withHarness "registration_limit_wrong_apex.json" fun harness => do
  expect harness "wrong" "assert |Fin(2) × ℤ/3| = 6"
  expect harness "holds" "assert |Fin(2) × ℤ/3| = 7"

-- The same registrations answering the constant `7`: the affected assertions are wrong, and
-- nothing else changes.
run_cmd withHarness "registration_wrong.json" fun harness => do
  unless harness.admitted.size == 2 do throwError "admitted {harness.admitted.size} registrations"
  for text in ["assert |Fin(3)| = 3", "assert |Fin(3) in FiniteSets| = 3",
      "assert |(ℤ/4)^3| = 64", "assert |(ℤ/0)^2| = ℵ₀"] do
    expect harness "wrong" text
  expect harness "holds" "assert |Fin(7)| = 7"
  expect harness "holds" "assert ℤ ⊆ ℚ"
  expect harness "gap" "assert |ℤ| = ℵ₀"
  expect harness "holds" "assert 2 + 3 = 5"

-- An answer that is not a value of the result form is malformed.
run_cmd withHarness "registration_malformed.json" fun harness => do
  expect harness "malformed" "assert |Fin(3)| = 3"
  expect harness "holds" "assert ℤ ⊆ ℚ"

-- A backend that cannot start is unavailable.
run_cmd withHarness "registration_unavailable.json" fun harness => do
  expect harness "unavailable" "assert |Fin(3)| = 3"

-- Registrations that name nothing of the catalogue, or a form the operation does not apply to,
-- or an undeclared backend, or a form the catalogue sends elsewhere along the operation's route,
-- are not admitted.
run_cmd withHarness "registration_rejected.json" fun harness => do
  unless harness.admitted.isEmpty do throwError "a registration was admitted"
  unless harness.rejected.size == 6 do throwError "rejected: {harness.rejected}"
  for (reason, rejected) in [("is not a catalogue operation", harness.rejected[0]!),
      ("is not a registered form", harness.rejected[1]!),
      ("does not apply to the values of lit.cardinals", harness.rejected[2]!),
      ("is not declared in the manifest", harness.rejected[3]!),
      ("register it on obj.sets.fin", harness.rejected[4]!),
      ("register it on cat.sets", harness.rejected[5]!)] do
    unless (rejected.splitOn reason).length > 1 do
      throwError "{rejected} is not rejected because it {reason}"
  expect harness "gap" "assert |Fin(3)| = 3"

end CasCatalogue.RegistrationProbes
