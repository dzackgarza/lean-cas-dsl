# Reuse record: `cc-lift-faithful`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `faithful functor lift morphism satisfying predicate structure preserving` | none usable (descriptive-complexity, TauCeti roadmap) |
| `IsLimit.ofFaithful lift explicit mediator` | none in the index; Mathlib checked directly |
| `isofibration transport structure along isomorphism` | 1lab `Cat/Displayed/Base`, UniMath `DisplayedCats/Core` (displayed categories: a faithful functor's fibres over morphisms are propositions) |

Direct checks: Mathlib `Limits/IsLimit.lean` (`IsLimit.ofFaithful` with an explicit lift),
`Limits/Creates.lean`, `Limits/Preserves/Basic.lean` (`isLimitOfReflects`,
`fullyFaithful_reflectsLimits`); sage-categories `specs/decisions.md` D183.

## Owner
- Limit cones, `IsLimit.ofFaithful`, reflection and creation are Mathlib's; reflection is used only
  in proofs.
- The morphism rule of a faithful functor (which maps below are morphisms above, as data) is the
  displayed-category view; no Lean dependency packages it for computation.

## New code, and why no dependency supplies it
`MorphismRule F` (lift a map below known to be the image of a morphism, computably) and
`realizedLiftedLimitCone`.
