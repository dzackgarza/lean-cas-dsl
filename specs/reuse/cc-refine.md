# Reuse record: `cc-refine`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `ObjectProperty FullSubcategory lift ιOfLE` | mathlib4 `ObjectProperty/FullSubcategory.lean`, `ObjectProperty/Equivalence.lean`; TauCeti `CategoryTheory/ObjectProperty.lean` |
| `ObjectProperty inf intersection full subcategory` | mathlib4 (`ObjectProperty` is a `CompleteLattice`: `P ⊓ Q`) |
| `three valued decision undecided equality` | none |
| `decidable equality morphisms category` | agda-categories, UniMath; nothing for undecided equality in Lean |

Direct checks in Mathlib: `ObjectProperty/FullSubcategory.lean` (`FullSubcategory.mk`, `ι`,
`ιOfLE : P ≤ P' → …` containment, `lift`), `ObjectProperty/Basic.lean` (lattice structure: `⊓`).

## Owner
- A refinement of a category by a property is Mathlib's full subcategory `P.FullSubcategory`
  (or a classifier total over it, `LeanCategories` `Classifier`); re-typing an object after a proof
  of `P X` is `FullSubcategory.mk X h`, the same object, data and images (`ι` of it is `X`).
- Containment of refinements is `ObjectProperty.ιOfLE`, a fully faithful monomorphism of
  categories with `ιOfLE h ⋙ ι ≅ ι`; intersection is `P ⊓ Q`.
- Three-valued decisions are the repository's `Decide.Result` (no dependency supplies an undecided
  outcome); equality of morphisms is Lean's `=`.

## New code, and why no dependency supplies it
The registry-level re-typing of an object after a proof of membership (in `lean-categories`, or
discharged by the kernel; never a leaf's answer),
the registered containment/intersection rows naming `ιOfLE`/`⊓`, and the category-owned equality
decision returning a three-valued result.
