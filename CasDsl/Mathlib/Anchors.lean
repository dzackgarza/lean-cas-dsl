/-
The anchor guards: the registry's semantic claims, discharged by Mathlib
instance synthesis at build time (SPEC-REGISTRY-TYPE-PREPASS, invariant I1).

Each `example` below IS a claim the standard universe makes — a membership
("ℤ is a Euclidean domain") or an inclusion edge ("every Euclidean domain is
a PID, every PID a UFD"). If Mathlib stops discharging one, `lake build`
fails: the registry cannot state what Lean cannot prove. The registration
layer (Step 2) reuses exactly these telescopes at the denoted types; this
file is the human-readable ledger of them.

Sharpness ("this membership is the MOST specific") is curatorial and is not
claimed here, except where Mathlib holds the negative theorem — ℝ is
genuinely uncountable, so `CountableSets` honestly excludes it.
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Logic.Denumerable
import Mathlib.Data.Rat.Denumerable
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.ZMod

namespace CasDsl.Anchors

/-! ## Inclusion edges

Quantified instance derivations: the category graph's edges are theorems.
`EuclideanDomain ≤ PID ≤ UFD` — the PID node is new (the old graph jumped
straight to UFD; Mathlib's own chain factors through PID). -/

example (R : Type*) [EuclideanDomain R] : IsDomain R := inferInstance
example (R : Type*) [EuclideanDomain R] : IsPrincipalIdealRing R := inferInstance
example (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R := inferInstance
example (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    CommRing R := inferInstance
example (α : Type*) [Fintype α] : Countable α := inferInstance
example (α : Type*) [Denumerable α] : Countable α := inferInstance

/-! ## Memberships of the standard universe

Synthesized instances at the denoted types — the claims the profile rules
currently make in prose, made real. -/

example : EuclideanDomain ℤ := inferInstance
noncomputable example : EuclideanDomain (Polynomial ℚ) := inferInstance
noncomputable example : EuclideanDomain (Polynomial ℂ) := inferInstance
-- ℤ[x] is a UFD (and, per the old comment, NOT Euclidean — that sharpness
-- claim stays curatorial; this direction is the checkable one)
example : UniqueFactorizationMonoid (Polynomial ℤ) := inferInstance
example : IsDomain (Polynomial ℤ) := inferInstance
example : CommRing (ZMod 5) := inferInstance

section
-- ℤ/5 is a field BECAUSE 5 is prime — the hypothesis is part of the claim
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
example : Field (ZMod 5) := inferInstance
end

-- the registered enumerations: ℕ, ℤ, ℚ are denumerable (enumeration is
-- DATA — Mathlib's equivalence, or a declared alternative, never a silent one)
example : Denumerable ℕ := inferInstance
example : Denumerable ℤ := inferInstance
example : Denumerable ℚ := inferInstance

-- the sharpness claim Mathlib CAN state: ℝ is not countable, so `Sets` is
-- its true strength and `nth` honestly never reaches it
example : Uncountable ℝ := inferInstance

end CasDsl.Anchors
