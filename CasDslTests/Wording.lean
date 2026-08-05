/-
The wording pin for `#explain_route` (workstream B of PLAN-REGISTRY-REFOUND):
the explanation is SENTENCES built from registry data — category captions,
the Mathlib anchor and its conventions, the verified membership — never a
dump of internal record fields. This pin is the product, so a change here is
a user-facing wording change and is reviewed as one.

The banned internal idiolect ("surface", "slice", "profile entry",
"availability:", "spells") must never reappear in the rendered text.
-/
import CasDsl

namespace CasDslTests

/--
info: factor (x : R) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  ≐ UniqueFactorizationMonoid.factors — the anchor is stated up to units; the answer is normalized — positive leading unit in ℤ, monic factors over a field
x = 360 ∈ ℤ; R = ℤ : EuclideanDomain ≤ IsPrincipalIdealRing ≤ UniqueFactorizationMonoid  (synthesized)
route: sage "factor_int" — implemented for element of ℤ
source: https://github.com/dzackgarza/lean-cas-dsl/blob/main/backends/sage_adapter.py
result: a factorization: a unit and irreducible factors with multiplicity
-/
#guard_msgs in
#explain_route (360).factor()

end CasDslTests
