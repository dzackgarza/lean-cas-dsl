# Reuse record: `cc-cells` (and its prerequisite `cc-realize-2cat`)

## Queries
Corpus: `python <lean-categories>/scripts/formalization_corpus.py search '<q>'`, 2026-09-29.

| query | hits used |
|---|---|
| `strict bicategory Cat whiskerLeft` | mathlib4 `Mathlib/CategoryTheory/Category/Cat.lean` (Cat is a strict bicategory, `Bicategory.Strict`) |
| `NatTrans whiskerRight functor category` | mathlib4 `NatTrans`, `Functor.whiskerLeft/whiskerRight`, `NatTrans.hcomp` (`Mathlib/CategoryTheory/Whiskering.lean`); `Functor.TwoSquare` (via sinhp/Poly) |
| `Pseudofunctor Cat strict` | mathlib4 `Pseudofunctor`; agda-categories (reference only) |
| `InfinityCosmos`, `Mathlib.CategoryTheory.Bicategory.Strict` | emilyriehl/infinity-cosmos (`ForMathlib/CategoryTheory/Bicategory/Strict/Closed.lean`, `InfinityCosmos/Basic.lean`) |
| `infinity cosmos homotopy 2-category` | none (spelling; see `InfinityCosmos`) |

Direct check: `Mathlib/CategoryTheory/CatCommSq.lean` (`CatCommSq T L R B`: an iso `T ⋙ R ≅ L ⋙ B`),
`Mathlib/CategoryTheory/Functor/TwoSquare.lean` (`TwoSquare`).

## Owner
- 2-cells, vertical/horizontal composition, whiskering, inverses: Mathlib `NatTrans`, `Iso`,
  `Functor.whiskerLeft/Right`, `NatTrans.hcomp`, `Cat` as a strict bicategory. Not reimplemented.
- A realization of `C` is a category of handles `R_C` with a functor `d_C : R_C ⥤ C`.
- A realized action of `F : C ⥤ D` is `a_F : R_C ⥤ R_D` with `CatCommSq a_F d_C d_D F`
  (`a_F ⋙ d_D ≅ d_C ⋙ F`). Composition of realized actions is Mathlib's pasting of `CatCommSq`.
- A realized cell over `α : F ⟶ G`, when the target denotation `d_D` is fully faithful, is the
  preimage under `Functor.FullyFaithful.whiskeringRight` (Mathlib `Whiskering.lean`) of
  `sq_F.hom ≫ (d_C ◁ α) ≫ sq_G.inv : a_F ⋙ d_D ⟶ a_G ⋙ d_D`: no leaf data, no new structure.
  Induced realizations are fully faithful by `fullyFaithfulInducedFunctor`, whose preimage is
  `InducedCategory.homMk`, so components compute.
- The list functor and its cells: Mathlib `ofTypeMonad List` (unit, join); reversal from
  `List.map_reverse`, `List.reverse_reverse` (lean-categories `Foundation/ListFunctor.lean`).
- infinity-cosmos: not needed for 1-categories of handles; revisit if a node needs the homotopy
  2-category of an ∞-cosmos.

## New code, and why no dependency supplies it
The registry row `cell` (a registered `NatTrans` or `Iso` between registered functor expressions),
its validation, the `cell%` elaborator composing registered cells with Mathlib's operations, and
the realizer's named full-faithfulness witness. Everything with categorical content is the
Mathlib term it names.

## Rejected
`CasCatalogue/Cell.lean` (uncommitted, deleted): a second 2-category calculus (`Composition`,
`RealizedCell.vcomp/whisker/hcomp`). `CasCatalogue/Action.lean` (committed) has the same defect for
1-cells (`Realizer`, `Denotation`, `Action`, `Realizes.comp`); `cc-realize-2cat` replaces it.
