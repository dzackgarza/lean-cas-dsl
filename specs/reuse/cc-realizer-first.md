# Reuse record: `cc-realizer-first`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `CatCommSq hComp pasting composition squares` | mathlib4 `CategoryTheory/CatCommSq.lean` (`hComp`, `hComp'`) |

## Owner
- Composition of the catalogue's functors, and of commuting squares between them, is Mathlib's
  (`Functor.comp`, pasting of `CatCommSq`s).

## New code, and why no dependency supplies it
Only the resolver's selection rule: a call starts from the receiver's declared input form (no
source-less mode), and each step's registered computation is selected by the form reached so far.
