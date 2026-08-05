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
  ≐ UniqueFactorizationMonoid.factors — stated up to units; answers are normalized — positive leading unit in ℤ, monic factors over a field
x = 360 ∈ ℤ; R = ℤ : EuclideanDomain ≤ IsPrincipalIdealRing ≤ UniqueFactorizationMonoid  (synthesized)
route: sage "factor_int" — implemented for element of ℤ
source: https://github.com/dzackgarza/lean-cas-dsl/blob/main/backends/sage_adapter.py
result: a factorization: a unit and irreducible factors with multiplicity
-/
#guard_msgs in
#explain_route (360).factor()

/-! ## The banned-vocabulary gate (workstream B acceptance)

The banned internal idiolect is checked over REGISTRATION DATA — the doc,
conventions and advisory fields the diagnostics render — because that is
emitted text exactly as the evaluator's strings are, and it is where the
2026-08-06 audit found the survivors. `docUrl` is exempt (URLs are opaque). -/

open Lean Elab Command CasDsl in
run_cmd do
  let env ← getEnv
  let banned := #["slice", "surface", "spells", "profile entry", "availability:",
    "backlog", "tier-", "held for demand", "pinned spelling", "QQbar"]
  let check (site text : String) : CommandElabM Unit := do
    for w in banned do
      if (text.splitOn w).length > 1 then
        throwError "banned vocabulary {repr w} reaches emitted text at {site}: {text}"
  for d in methods env do
    check s!"method {d.id} doc" d.doc
    check s!"method {d.id} conventions" d.conventions
    check s!"method {d.id} advisory" d.advisory
    check s!"method {d.id} resultDoc" d.resultDoc
    check s!"method {d.id} argDoc" d.argDoc
  for c in categories env do
    check s!"category {c.name} doc" c.doc
  for s in opSigs env do
    check s!"op {s.backend}/{s.opId} doc" s.doc
    check s!"op {s.backend}/{s.opId} advisory" s.advisory
  for r in routes env do
    check s!"route {r.method}→{r.backend}/{r.opId} doc" r.doc
  for f in functors env do
    check s!"functor {f.name} doc" f.doc
  for m in canonicalMaps env do
    check s!"canonical map doc" m.doc

end CasDslTests
