# Reuse record: `cc-realizer-first`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `CatCommSq hComp pasting composition squares` | mathlib4 `CategoryTheory/CatCommSq.lean` (`hComp`, `hComp'`) |

## Owner
- Composition of realized actions is Mathlib's pasting of `CatCommSq`s (`RealizedAction.comp`);
  the identity action of a realizer is `CatCommSq.hId` (`RealizedAction.id`).

## New code, and why no dependency supplies it
Only the resolver's selection rule: compositions start at `RealizedAction.id` of the receiver's
realizer (no source-less mode), so each step's action is selected by the realization so far.
