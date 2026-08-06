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
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.ZMod
-- anchor constants for the method catalogue (CasDsl/Std.lean): a method's
-- `anchor` must be in the environment when its registration elaborates
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- anchor constants for the category graph (CasDsl/Std.lean): each node
-- names the category it denotes where Mathlib names one; otherwise the
-- constant defining it — the class cutting a full subcategory, or the
-- object whose elements the node fibres over
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Scheme

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

/-- A polynomial ring over a countable coefficient ring is countable.
Mathlib holds this for the underlying `Finsupp` (`ℕ →₀ R`); the
`Polynomial` structure wrapper does not transport it automatically, so this
instance is the bridge — stated in full generality, a candidate upstream
contribution. It is what admits ℤ[x] and ℚ[x] into `CountableSets`. -/
instance {R : Type*} [Semiring R] [Countable R] : Countable (Polynomial R) :=
  -- two structure wrappers sit between R[x] and the Finsupp Mathlib knows
  -- to be countable; compose their coefficient injections
  have inj : Function.Injective
      (fun p : Polynomial R => (p.toFinsupp.coeff : ℕ →₀ R)) := fun _ _ h =>
    Polynomial.toFinsupp_injective (congrArg AddMonoidAlgebra.ofCoeff h)
  inj.countable

example : Countable (Polynomial ℤ) := inferInstance
example : Countable (Polynomial ℚ) := inferInstance

-- the categories themselves; the registry stores names extracted from
-- this diagram
example : CategoryTheory.Category (Type _) := CategoryTheory.types
example : CategoryTheory.Category FintypeCat := inferInstance
example : CategoryTheory.Category (ModuleCat ℚ) := inferInstance
example : CategoryTheory.Category AlgebraicGeometry.Scheme := inferInstance

-- ℤ/n is a cyclic ℤ-module: ⊤ = span ℤ {1}
example (n : ℕ) [NeZero n] : (⊤ : Submodule ℤ (ZMod n)).IsPrincipal :=
  ⟨1, le_antisymm
    (fun x _ => Submodule.mem_span_singleton.mpr
      ⟨(x.val : ℤ), by simp [zsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]⟩)
    le_top⟩

end CasDsl.Anchors
