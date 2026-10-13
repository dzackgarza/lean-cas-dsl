# Reuse record: `cc-limit-surface`

## Queries
- `formalization_corpus.py search`:
  - "limit of diagram chosen cone HasLimit limit.lift": Mathlib `CategoryTheory.Limits`;
  - "cokernel cofork colimit": Mathlib `Limits.Shapes`; agda/Rocq category-theory instances.
- This node authors no mathematics: the limits are registered rows (`cc-limits`, `cc-colimits`,
  `cc-lift-general`), and the node exposes them through a public surface.

## Owner
- Mathlib `LimitCone`, `ColimitCocone`, `IsLimit.lift` and `IsColimit.desc`, which the registered
  rows name.
- The kernel's `resolveLimit`, `realizedLimitCone`, `realizedReturnedLimitCone` and
  `realizedColimitCocone`.

## New code, and why no dependency supplies it
- The surface elaborator resolving a diagram of presented values to the registered limit or
  colimit, with its lift, and returning the cone and its apex's semantic value.
- Its stratified failures.
