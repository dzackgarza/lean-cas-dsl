# Complete selected data realization

## Queries

- `formalization_corpus.py search 'CategoryTheory TypeCat homEquiv'` locates the
  existing `TypeCat.homEquiv` in Mathlib's category of types.
- `formalization_corpus.py search 'CategoryTheory Functor obj named object'`
  checks the existing object-action and functor ownership vocabulary.
- `formalization_corpus.py search 'CategoryTheory Bundled Cat.of'` locates
  Mathlib's complete `Bundled` and `Cat.of` structures. The query for
  `automorphismsConstruction Core` returns no corpus entry; the accepted local
  declaration in `Semantics/Algebra/Automorphisms.lean` supplies that construction.
- Local searches cover `Semantic.recordNamedObject`, `parameterData`,
  `FunctorActionData.registeredAction?`, `retainedParameterAction?`,
  `realizeEndpoint`, `observeComputedPoints`, and the published forms in
  `CasContract/Port.lean`.
- The named-parameter continuation searched `repo:mathlib RingCat.of CommRingCat.of`
  and `repo:mathlib replaceFVars forallTelescope`, and inspected Lean's pinned
  `Meta/ExprDefEq.lean`, telescope/substitution APIs, and the existing complete
  declaration recovery. All four ordinary transparency settings failed to recover
  a modulus from a reduced complete ring; changing transparency is not a repair.

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

An intermediate complete object may also retain a prefix of a route already
selected in its original trace. Every accepted action and the original complete
route result are checked before selecting a prefix; distinct source occurrences
or actions remain ambiguous. A literal construction projection may reuse a
retained construction occurrence only when its exact original receiver and full
functor agree. It reuses that occurrence's actual packet and owner, never an
arbitrary definitionally equal cache entry.

A literal object projection can also identify one accepted construction by its
entire functor type and value when no prior construction occurrence was read.
All dependent arguments must close from that comparison. Complete category
bundles use their uniquely checked registered presentation, including the whole
category dictionary. A literal core receiver is framed only after the selected
construction's complete source equals the accepted core constructor at that
same full bundle. Existing packets and trace occurrences retain priority.

Actual computed callables retain their own anonymous endpoint descriptors. A
newly recovered definitionally equal name is available to an ordinary formal
coordinate but does not replace a computed callable's selected presentation.

The continuation uses whole-family matching through an exact registered
object application already occurring inside a fixed parameter. Its published
telescope supplies fresh typed parameters; a candidate presentation must agree
as a complete structured family before those same original arguments are
restored. No natural number is guessed, no default argument is supplied, and a
coincidence at the original value or its carrier is insufficient. Actual cached
objects and source occurrences remain separate. This is execution-data recovery
only; it does not select a new mathematical interpretation or invent a registry
edge. Every recovered closed application must still pass the existing complete
type, value, closure, and kernel equality checks.

`WholeFamilyParameterDataProbes` checks two complete parameter instances, named
map endpoints, carrier agreement that fails as a family, an unrelated occurrence
inside the same object, and exact actual-versus-equal cached ownership. The
unchanged complete-named-data, reduced-action-parameter, and declared-endpoint
controls pass. Early control attempts are retained: one had local syntax errors;
another reconstructed its fixture by elaborating a closed carrier, which chose
a closed dictionary instead of retaining the full source-family dictionary.
The final fixture consumes the existing published functor's complete dictionary.
No production guard or fixed mathematical question was weakened for those tests.
