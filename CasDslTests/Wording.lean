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
info: `factor` — factor into irreducibles/primes with multiplicity.
It is declared on elements of a unique factorization domain.
360 ∈ ℤ is one of the elements of a euclidean domain; those are among the elements of a principal ideal domain, those are among the elements of a unique factorization domain, where the method is declared. Lean verified the membership against Mathlib at this call.
Its meaning is `UniqueFactorizationMonoid.factors` — the anchor is stated up to units; the answer is normalized — positive leading unit in ℤ, monic factors over a field.
Implementation: backend `sage`, operation "factor_int", covering element of ℤ.
The result is a factorization: a unit and irreducible factors with multiplicity.
-/
#guard_msgs in
#explain_route (360).factor()

end CasDslTests
