# Complete selected data realization

## Queries

- `formalization_corpus.py search 'CategoryTheory TypeCat homEquiv'` locates the
  existing `TypeCat.homEquiv` in Mathlib's category of types.
- `formalization_corpus.py search 'CategoryTheory Functor obj named object'`
  checks the existing object-action and functor ownership vocabulary.
- Local searches cover `Semantic.recordNamedObject`, `parameterData`,
  `FunctorActionData.registeredAction?`, `retainedParameterAction?`,
  `realizeEndpoint`, `observeComputedPoints`, and the published forms in
  `CasContract/Port.lean`.

## Owner

The accepted mathematical declarations in `lean-categories` own every registered
object, full category dictionary, construction and functor action. Mathlib owns
`CategoryTheory.Functor.obj`, `CategoryTheory.Core`, `TypeCat.Hom`, `RingCat`,
`MonCat` and `ModuleCat`. The public contract owns descriptor and callable data
forms. This work consumes those declarations and does not add mathematical
objects, registrations, identifications or expected answers.

## New code

Execution recovers an already accepted complete object presentation only after
checking its full type and value. Literal selected declaration arguments and
actual computed dependencies retain priority. Distinct accepted presentations or
retained actions remain ambiguous; equal carriers alone select nothing. The
engineering probes exercise representation and ownership, independently of any
backend's mathematical answer. Reader interpretation and the fixed questions
remain unchanged.
