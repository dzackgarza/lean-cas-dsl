# Reuse record: `cc-lift-general`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `CreatesLimit liftLimit liftedLimitMapsToOriginal` | mathlib4 `Limits/Creates.lean`, `Limits/Final.lean` |
| `createsLimitsOfShape forget GrpCat` | mathlib4 `Algebra/Category/Grp/Limits.lean` (`forget_createsLimit`, `Forget₂.createsLimit`) |
| `forget creates limits Grp` | lean-liquid only (Lean 3) |
| `IsCartesian fibration lift` | UniMath, PolyFun; Mathlib checked directly |
| `PreservesLimit isLimitOfPreserves` | downstream users of Mathlib `PreservesLimit` |

Direct checks in Mathlib: `CategoryTheory/Limits/Creates.lean` (`CreatesLimit`, `liftLimit`,
`liftedLimitIsLimit`, `liftedLimitMapsToOriginal`), `CategoryTheory/FiberedCategory/Cartesian.lean`
(`Functor.IsCartesian`), `Limits/Preserves/Basic.lean` (`PreservesLimit`, `ReflectsLimit`),
`Adjunction/Limits.lean` (right adjoints preserve limits).

## Owner
- Returning a limit computed downstairs to the source category is Mathlib's `CreatesLimit`:
  `liftLimit` (the lifted cone), `liftedLimitIsLimit`, and `liftedLimitMapsToOriginal` (its image
  is the downstairs limit). Forgetful functors of algebraic categories carry these instances.
- Cartesian lifts are Mathlib's `Functor.IsCartesian`/`IsFibered`; preservation and reflection are
  `PreservesLimit`/`ReflectsLimit`.

## New code, and why no dependency supplies it
A registry row naming the creation datum between registered functors and categories, its
validation, and the lift on presented values (the preimage of Mathlib's lifted cone), as for
`realizedLimitCone`.

### Construction checkpoint (2026-10-02)

Direct source queries: `standardCone` and `decodeFamily` in `CasCatalogue/Semantic.lean`
and `CasCatalogue/Realize.lean`; `CreatesLimit.lifts`, `liftLimit`, and
`LiftableCone.validLift` in Mathlib `CategoryTheory/Limits/Creates.lean`.

`CasCatalogue/StructuredResult.lean` packages the complete decoded cone/cocone, its diagram,
apex and original constructor response. `Realize.Wire` retains the complete response and diagram
alongside the cone, rather than retaining only the apex wire presentation. Decoding still uses
Mathlib's shape constructors and the existing dependent-field decoder; no new mathematical
constructor or semantic row is introduced. The creation helper consumes the registered creation
evidence and an independently supplied upstream presentation only when its cone is definitionally
the decoded cone. This limited helper is not completion of generic computational lifting.

The remaining creation-lift input is an independent reconstruction of `IsLimit` for an arbitrary
well-typed decoded cone. `CreatesLimit.lifts` requires that input; commutation of the legs alone
is insufficient. The existing cone response contains apex and legs, not that input, and no leaf
proof can supply trusted mathematical evidence. The positive execution obligation remains open.

Focused validation: `lake build CasCatalogue.StructuredResult` succeeds. The combined
`StructuredResult`/`Realize` build reaches the integration but fails in independently edited
question-record sections of `Realize`, outside this construction's owned sections. No execution
acceptance is established by these compilation checks.
