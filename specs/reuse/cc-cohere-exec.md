# Reuse record: `cc-cohere-exec`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `natural isomorphism transport along functor iso app` | none relevant (PolyFun lenses) |
| `Iso.app naturality isoWhiskerLeft` | Mathlib `Iso.app`, `isoWhiskerLeft/Right` (via downstream users) |
| `coherence of routes comparison isomorphism unique` | none |
| `Functor.FullyFaithful preimageIso` | mathlib4 `Mathlib/CategoryTheory/Functor/FullyFaithful.lean` |

## Owner
- A comparison between two routes is an invertible cell (a Mathlib `Iso` between the composite
  functors), registered as a `cell` row: the comparison rows become cell rows.
- Applying it to data is its realized component (`realizedCell`, i.e.
  `FullyFaithful.whiskeringRight` preimage, and `Functor.FullyFaithful.preimageIso` for isos)
  at the receiver, composed with the method's action (`Functor.map` of the realized method on the
  component): Mathlib's `NatTrans.app`, `Functor.map`, `Iso.app`.

## New code, and why no dependency supplies it
Resolution: choosing the executed route among identified ones without order, and failing on two
distinct registered comparisons between the same pair of routes. The transport itself is Mathlib.
