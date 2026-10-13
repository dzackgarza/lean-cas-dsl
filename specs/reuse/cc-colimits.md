# Reuse record: `cc-colimits`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29: see
`cc-limits.md` and `cc-lift-faithful.md` (the dual constructions).

Direct checks: Mathlib `Limits/IsLimit.lean` (`IsColimit.ofFaithful`,
`IsColimit.precomposeHomEquiv`), `Limits/Preserves/Basic.lean` (`isColimitOfReflects`),
lean-categories `Modules/Bilinear/Valued/Cokernel.lean` (`BilWFormCat.cokernelIsColimit`,
`SymBilWFormCat.cokernelIsColimit`).

## Owner
- Colimit cocones, `IsColimit.ofFaithful` and reflection are Mathlib's; the cokernel of formed
  modules with varying values is lean-categories'.

## New code, and why no dependency supplies it
The `colimit` registry row kind and `realizedLiftedColimitCocone` (dual of
`realizedLiftedLimitCone`, with the same `MorphismRule`).
