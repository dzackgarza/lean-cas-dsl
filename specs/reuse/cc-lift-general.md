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
validation, and the realized lift on handles (the preimage of Mathlib's lifted cone), as for
`realizedLimitCone`.
