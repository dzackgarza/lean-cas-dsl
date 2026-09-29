# Reuse record: `cc-refine-registry`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `Functor.Fiber ObjectProperty ι essential image` | see `cc-refine.md`; Mathlib `FiberedCategory/Fiber.lean`, `ObjectProperty/FullSubcategory.lean` |

## Owner
- A property classifier's total is Mathlib's `P.FullSubcategory` with forgetful functor `P.ι`; its
  strict fibre (`Functor.Fiber`) over `X` is `{Y // Y.obj = X}`, inhabited iff `P X`.
- Re-typing is `CasCatalogue.refine` (`cc-refine`); deciders are registered `Decider`s.

## New code, and why no dependency supplies it
The generic `Holds ↔ P` lemma for full-subcategory classifiers, the registry link from a classifier
row to its property, and the `refine%` surface.
