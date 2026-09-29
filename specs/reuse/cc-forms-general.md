# Reuse record: `cc-forms-general`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `discriminant form lattice dual quotient Q/Z` | none in the corpus index |
| `bilinear form finite abelian group values Q/Z` | none |

Direct checks: lean-categories `Lattices/Valued/Discriminant.lean` (`discriminantGroup`,
`discriminantForm`, `discriminantFormModule` of an integral lattice), Mathlib
`LinearMap.BilinForm.dualSubmodule`, and the registered value-change and base-change functors of
lattices (`fun.lattice.change_value`, `fun.lattice.base_change`).

## Owner
- The discriminant form of an integral lattice is lean-categories' `discriminantForm` (values in
  `K/R`, from the dual lattice); formed modules with values in any module are `BilinModuleCat R W`.
- Change of values is the registered `fun.lattice.change_value`.

## New code, and why no dependency supplies it
Registration of the discriminant functor (lattice ↦ discriminant formed module) against
lean-categories' construction, and a leaf realizing formed modules on finite modules with values in
`ℚ/ℤ`; no new mathematics.
