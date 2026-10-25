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

## Complete literal action and parameter recovery — 2026-10-25

The upstream `Semantic.objOf` interface and Mathlib's `Functor.obj` and
`Prefunctor.obj` supply the same complete object action through two public
projections. `Semantic.compositeOfApplications` composes the original registered
applications. No mathematical construction or equality is introduced here.

`FunctorActionData.objectAction?` reads either literal projection while retaining
its exact receiver. When the complete action remains in a value, nested objects
with the same final carrier are not alternative sources. The fallback for a
genuinely reduced value continues to require a literal retained source occurrence,
all complete registered applications, and the full resulting object. Distinct
retained sources remain ambiguous; an equal cached object cannot supply data.

`registeredAction?` checks actual complete declaration applications against the
whole selected functor. It returns the original declaration application together
with its checked public action. A descriptor therefore encodes the parameters of
the application that passed, rather than the first occurrence of that declaration
inside an unrelated argument. A direct application, including one selected by
beta reduction or a public classifier projection, fixes its own parameter
presentation. Without one, distinct surviving presentations remain ambiguous.

Portable parameter data, owned parameter data and direct missing-node realization
all preserve literal action composition order. Direct realization recurses through
the selected child before reduced-presentation recovery, retaining its actual
packet and owner through the checked actions. This also handles nested actions
whose alternate public projection spelling has no exact trace key. All data
dependencies of the selected action parameters are merged with the source owner;
no fresh parameter reconstruction substitutes for the original child.

`ReducedParameterActionProbes` retains its original reduced ambiguity, distinct
full-structure, cyclic-dependency and ownership controls. Additive engineering
controls exercise both public projection spellings, nested and composed actions
without exact trace keys, and an ignored earlier parameter packet followed by the
actually selected owned parameter. These are data-flow and source-preservation
checks, not mathematical acceptance or fixed-question execution verdicts.
