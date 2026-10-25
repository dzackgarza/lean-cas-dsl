# Reuse record: `cc-realizer-first`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `CatCommSq hComp pasting composition squares` | mathlib4 `CategoryTheory/CatCommSq.lean` (`hComp`, `hComp'`) |
| `CategoryTheory Functor obj map composition` (2026-10-25) | Existing Mathlib `Functor.obj`, `Functor.map`, `Functor.comp`; no new mathematical declaration needed |
| `mapArrowFunctor` (2026-10-25) | Mathlib `CategoryTheory/Comma/Arrow.lean`, `Functor.mapArrowFunctor`; the registered constructor already uses `Functor.mapArrow` |
| `coreComp` (2026-10-25) | Mathlib `CategoryTheory/Core.lean`, `Functor.coreComp`; the registered constructor already uses `Functor.core` |

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

## Shared executable action boundary — 2026-10-25

`FunctorEntry`, `ConstructionEntry`, `Semantic.edgeFunctor`,
`Semantic.compositeOfApplications`, `DirectConstruction`, `CellAction` and
`CategoryContext` already own selection and the complete mathematical actions.
The executor reuses them to check full category dictionaries, parameters, object
images and Hom endpoints. It introduces no mathematical functor, comparison,
categorical law or route-selection rule.

The additional code is runtime orchestration: admission of a registered
functor's map/input projections, execution of its object and whole-map ports,
and retention of actual intermediate images. The existing `ConstructionInvocation`,
`PointInvocation` and `TypedMap` forms supply the frames. The cache key includes
the complete selected action, exact actual source packets and owners, ordered
parameter dependencies and actual image endpoints. No equality of carrier types
or values selects a computational presentation.

The image-retention pattern was checked against the read-only
`sage-categories/kernel/functor_cache.py` design: object results are retained by
their actual source and map results by their already computed image endpoints
and original morphism. Its class mutation and semantic authority are not copied.
Here all authority remains in the accepted Lean declarations, while every
backend result remains untrusted data.

The executor retains an internal source/action receipt separately from the
actual output's ownership. A self-contained returned target packet can be used
by an independent target-only process. Nested opaque data retain their original
session. Registered comparison endpoints reuse their selected object actions;
they do not search equal cached objects. The existing full-field projection and
proof-refinement restoration paths remain intrinsic. A general classifier or
constructor-induced action still needs the separately identified public address
projection; the first checkpoint left that interface gap open. The derived
projection below supplies it without adding mathematical rows.

`FunctorActionExecutionProbes` launches two arbitrary protocol processes and
checks actual packets, ordered parameters, selected action identity, image
reuse, endpoint mismatch, source/result ownership, expired sessions and target
isolation. Its optional JSONL receipt contains exact requests, responses and
internal action records. It asserts no mathematical result and is separate from
the independent two-leaf experiment.

A chained control uses the same formal endomorphism endpoint with two distinct
actual representations. A bare returned owned callable retains those selected
image packets inside the existing typed-map form before the next action runs.
The original callable data and every opaque endpoint owner remain intact; the
expression-keyed result cache cannot merge the two endpoint occurrences.

## Derived registered edge actions — 2026-10-25

`Admission.edgeImageDescriptor` already supplies the recursive identity for a
functor, classifier forgetful action, or constructor-induced action. The public
`Semantic.edgeFunctor` and `applyConstructorFunctor` interfaces supply their
full selected mathematical functors. The executor now projects canonical
object/map/input addresses from that existing identity for non-functor roots.
Every constructor must already publish its functorial action. Bare functors keep
their original identifiers and ordered parameter vectors.

The derived invocation carries the complete existing action descriptor as its
single framing parameter. The object and map executors share their whole-action,
category, endpoint, owner and result checks with named functors. Strict descriptor
encoding uses the exact declaration application selected by
`FunctorActionData.registeredAction?`; an ignored earlier occurrence cannot
substitute its parameter packet or owner. Nested constructors recover their
literal inner action through the published constructor declaration before
recursively encoding it. No category-specific decoder or mathematical action is
introduced.

The existing public `coreObject` packet had an interface reconstruction path but
no corresponding port-validation branch. Validation now projects the selected
formal object's `Core.of` field using the existing checked record-projection
helper, then validates its original complete object recursively. Malformed,
missing, or unrelated child interfaces remain rejected. Nonrecursive request
helpers are outside the large realization mutual block so its normal compiler
heartbeat budget is unchanged.

`DerivedActionExecutionProbes` checks a classifier, Arrow of a registered functor,
Core of that Arrow action, and a parameterized action with an ignored earlier
parameter occurrence. Its arbitrary protocol process returns owned images and
bare owned maps. Controls retain actual source data, full nested descriptors,
exact image endpoints and owners, and reuse the actual image without replay.
Canonical admission and malformed Core inputs have independent negative checks.
These controls do not supply mathematical outcomes or close the separate
leaf-facing computational service and frozen-leaf integration experiments.
