# Reuse record: `cc-adjunctions`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `Adjunction homEquiv unit counit` | TauCeti `Adjunction/Mates.lean`, downstream users of Mathlib `Adjunction` |
| `Adjunction const lim limAdjunction` | none (spelling); direct check below |
| `Adjunction.mkOfHomEquiv` | mathlib4 order categories (`BddLat`, `PartOrd`) |
| `free forgetful adjunction MonCat` | mathlib4 `Algebra/Category/Grp/Adjunctions.lean`, `Ring/Adjunctions.lean` |

Direct checks in Mathlib: `Limits/HasLimits.lean` (`constLimAdj : const J ⊣ lim`),
`Algebra/Category/MonCat/Adjunctions.lean` (`MonCat.adj : free ⊣ forget MonCat`).

## Owner
- An adjunction is Mathlib's `Adjunction` (unit, counit, `homEquiv` = transpose and its
  inverse); `Δ ⊣ lim` is `constLimAdj`; free–forgetful adjunctions are Mathlib's.
- `Adjunctions(F, G)`, `Equivalences(C, D)` as categories: Mathlib `Equivalence` has a category
  structure; adjunctions between fixed functors are a set (subsingleton up to iso).
- Realized transposes over fully faithful realizations are preimages of `homEquiv`
  (as `realizedCell`, `realizedLimitCone`).

## New code, and why no dependency supplies it
The `adjunction` registry row (a Mathlib `Adjunction` between registered functors), its
validation, and the realized transpose on handles.
