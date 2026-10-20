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

## B0 proof-only reader construction (2026-10-20)

Corpus queries rerun against the current index: `ObjectProperty FullSubcategory mk`
(36 files, 1057 matches; existing full-subcategory constructions) and
`classifier full subcategory proof refinement` (one unrelated Rocq file; no replacement
for the registered Lean classifier interface). Direct current sources confirm
`ObjectProperty.FullSubcategory.mk`, `FintypeCat.of`, and the actual registered
classifier total/forgetful functor own the mathematics. Lean's documented metavariable
depth explains why `mkAppM` cannot assign an older constructor telescope; the existing
upstream `mkAppHere` performs current-depth application without changing the mathematics.

The kernel adds constructor elaboration and provenance only: constrain the public total
constructor by its complete registered forgetful image; fill remaining proposition fields
from existing class or Decidable instances; kernel-check them; refuse remaining chosen
nonproof data. It retains the original full object, action, identification and complete
computational source payload, and consumes only the exact checked forgetful prefix.
No category, predicate, lemma, proof procedure, or mathematical admission is authored here.
