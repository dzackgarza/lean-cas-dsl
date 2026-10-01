# Reuse record: `cc-limits`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `IsLimit lift fac uniq cone` | downstream users of Mathlib `IsLimit` (LeanFibredCategories) |
| `pullback cone isLimit mk` | downstream users of Mathlib `PullbackCone.IsLimit.mk` |
| `kernel fork IsLimit ModuleCat` | FLT, LeanCondensed: Mathlib `ModuleCat.kernelIsLimit` |
| `limits in Type explicit cone` | none relevant |
| `pushout opposite pullback unop` | TauCeti `Exact/Opposite`; Mathlib opposites of limits |
| `LimitCone ModuleCat hasLimits` | mathlib4 `ModuleCat/Presheaf/Limits.lean` |

Direct checks in Mathlib: `Limits/Types/Pullbacks.lean` (`Types.pullbackLimitCone`),
`Algebra/Category/ModuleCat/Kernels.lean` (`ModuleCat.kernelCone`, `ModuleCat.kernelIsLimit`),
`Limits/HasLimits.lean` (`IsLimit.op`, `isColimitEquivIsLimitOp`),
`Limits/Shapes/Opposites/Equalizers.lean`.

## Owner
- Diagrams are functors `J ⥤ C`; cones, limit cones, `IsLimit`, `IsLimit.lift`, `fac`, `uniq`:
  Mathlib `CategoryTheory.Limits`. Shapes (pullbacks, equalizers, kernels, products) and their
  explicit limit cones in `Type` and `ModuleCat` are Mathlib's.
- Colimits through `Op`: `Cone.op`, `IsLimit.op`, `isColimitEquivIsLimitOp`.
- A registered limit presentation is a Mathlib `LimitCone` (apex, legs, `IsLimit`); its mediator
  is `IsLimit.lift`.

## New code, and why no dependency supplies it
Registry rows naming limit presentations of registered diagrams, their reading on presented
values (apex, legs, mediator as a preimage through the fully faithful denotation of the
presentation form declared upstream), and the elaborator. The universal property is Mathlib's.
