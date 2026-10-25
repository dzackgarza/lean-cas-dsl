# Reuse record: `cc-realizer-first`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `CatCommSq hComp pasting composition squares` | mathlib4 `CategoryTheory/CatCommSq.lean` (`hComp`, `hComp'`) |
| `CategoryTheory Functor obj map composition` (2026-10-25) | Existing Mathlib `Functor.obj`, `Functor.map`, `Functor.comp`; no new mathematical declaration needed |
| `mapArrowFunctor` (2026-10-25) | Mathlib `CategoryTheory/Comma/Arrow.lean`, `Functor.mapArrowFunctor`; the registered constructor already uses `Functor.mapArrow` |
| `coreComp` (2026-10-25) | Mathlib `CategoryTheory/Core.lean`, `Functor.coreComp`; the registered constructor already uses `Functor.core` |
| `Functor obj map composition` (2026-10-25, service preparation) | Broad returned hits included TypeTopology functor composition and Mathlib polynomial functors; direct accepted-source inspection supplies the existing Mathlib actions through `Semantic`, with no new categorical declaration |

## Owner
- Composition of the catalogue's functors, and of commuting squares between them, is Mathlib's
  (`Functor.comp`, pasting of `CatCommSq`s).

## Exact retained service projections — 2026-10-25

The service decoder now routes the released `morphismEndpoint`, `arrowHom`,
`subobjectApex`, `subobjectInclusion`, and retained `constructionApex`,
`constructionField`, and `constructionLeg` envelopes to their existing owners:
the complete Hom, `StructuredProjection.ArrowPlan`, and the authoritative
`StructuredResult.Result` plus its registered data-port schema. This is runtime
data selection, with no new mathematical declaration, proof, comparison, or
route. A cone packet is never elaborated as a proof-bearing cone term.

Repeated constructor identities and original diagrams must match the exact
retained result. Independent port order and diagram-index type remain separate.
Direct fields reuse their actual returned packet; a portable field need not
inherit an opaque sibling's owner. Opaque fields keep their original live
session, and the entire parent remains in the dependency ledger. Created
packets keep their existing complete projection wrapper instead of reinterpreting
target fields as source-category maps.

Copied parent packets now require exact selected expressions and full category
contexts. Definitionally equal values do not coalesce distinct occurrences;
distinct complete action receipts remain ambiguous even when bytes and owners
agree. Explicit scoped result references continue to identify one occurrence.
Failure to construct a named operand's full category context propagates its
original error instead of silently dropping the dictionary.

`ServiceProjectionProbes` supplies three separating engineering controls through
the real runtime callbacks and a live arbitrary protocol process: asymmetric
endpoint/Arrow fields, selected-occurrence ambiguity, and complete universal
field/leg reuse. The arbitrary packets establish no mathematical answer.
Original fifteen deferred lifecycle cases pass unchanged. This increment does
not claim full descriptor coverage: unretained universal packet assembly and
formal-only universal demands, general constructor fields, nested comparison
and other data descriptors remain explicit kernel work for the next increment.

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

## Typed computational service preparation — 2026-10-25

The existing registered declarations, `DirectConstruction`, `CellAction`,
`Semantic`, `StructuredResult` and `ComputationalData` supply the formal
applications and complete data interfaces. `ServiceRequest` separates pure
request preparation from runtime dispatch. Its callbacks resolve each operand
in its declared dependent role and return an exact runtime occurrence handle;
the preparation layer has no backend or session selection capability. Result
references preserve the existing formal operand and its actual packet. Fresh
placeholders used only by response validators never become formal arguments.

The runtime retains the enclosing request's original formal result when reusing
a service node's data. A different well-framed computation is still untrusted
data for independent checking; the child node's denotation or supplier cannot
replace the enclosing request's mathematical meaning or data ownership.


## Typed deferred execution and retained occurrences — 2026-10-25

The published contract's `DeferredData` is an ordered request graph over existing
operation/input addresses. `ServiceRequest.Decoder` binds only complete typed
data operands into the existing declaration telescope. `SimpleServiceRequest`,
`StructuredServiceRequest` and `UniversalServiceRequest` cover every current
`Admission.Operation` constructor. The runtime checks the ordinary admission
predicate before preparation; no service-specific semantic registry, method
selector, supplier hint, result-type field or proof channel is introduced.

| Existing published family | Existing formal owner used by preparation |
|---|---|
| Functor, construction and derived edge object/map actions | `Semantic`, `DirectConstruction`, complete `CategoryContext` |
| Operations, morphisms, applications and binders | Accepted declaration telescope and complete selected Hom |
| Methods and properties | Existing `Semantic.methodIn` / `propertyIn`, ordinary admitted resolution and trace |
| Cell components, cartesian arrows and presentations | `CellAction`, `ReindexAction`, accepted comparison declarations |
| Limits and colimits | `Semantic.limitPresentation`, `StructuredResult.DataPlan`, original input-role interfaces |
| Lift fields and factors | `SelectedLift`, `LiftedSubobjectData`, independently retained formal conditions |

A reference indexes the exact completed Wire occurrence. Two nodes with the same
formal value and type can carry different packets and suppliers; neither a
parameter lookup nor ordinary method execution selects the latest equal value
from an expression cache. The private method trace is seeded with its one exact
receiver, while action caches retain their full actual operand keys. The shared
endpoint callback uses `true` for source and `false` for target, projects the
original typed-map fields, and otherwise retains that callable's own public
`MorphismEndpoint`. Universal preparation uses the same convention.

The runtime saves every raw reply, exact request, child Wire, parameter dependency
and supplier session. Incomplete service scopes retain completed children when
later preparation or result assembly fails. A completed self-contained target
packet is portable; opaque fields keep their original live owner. A child owner's
name is never replaced by the enclosing supplier. Mixed-owner assembly remains
unavailable without an actual bridge. Final template references are checked at
complete declared data roles before substitution, then the ordinary result
interface checks the assembled packet. The enclosing caller keeps its original
formal construction even when a child's well-framed data are mathematically wrong.

A literal nested `functorAction` or `map` is materialized by the same object/map
executor before another operation receives it. The downstream target process
gets the actual resulting target packet; it is not assigned a private source
recipe decoder. Ordinary production `realizeClaim` installs this boundary, and
public direct-Harness callers can use the same `enableService` installer.

Prior-art implications were checked against the existing immutable sources:
`sage-categories/kernel/functor_cache.py` and its composite isofibration regression
retain actual selected images and nonidentity transport, rather than substituting
an equal formal object; the new same-formal/different-packet and whole nonidentity
map controls address that historical failure mode. GATlab's explicit typed model
argument distinguishes full operation structures on a common native carrier
(AlgebraicJulia, [GATlab explicit model design](https://blog.algebraicjulia.org/post/2025/02/refactor1/index.html)).
The kernel retains the independently selected complete Lean dictionary instead
of adopting a native model as mathematical authority. CAP's existing operation
and derived-operation interfaces motivate shared admitted dependency execution;
they do not supply a second weighted mathematical selector here. Historical
source/tests and these engineering controls are not current integrated acceptance.

`DeferredServiceProbes` uses three arbitrary public-protocol processes. Its
controls cover exact occurrence reuse through ordinary methods, full dictionary
closure, original caller meaning, child ownership and session expiry, nested
reference scopes, mixed-owner refusal, malformed references and hidden fields,
forbidden backend selection, recursive requests, whole nonidentity maps, exact
image endpoint rejection, the production installer, and nested action
materialization before an independent target consumer. Returned witnesses are
not mathematical answers. `StructuredServiceRequestProbes` checks pure typed
preparation; `UniversalServiceRequestProbes` remains an explicitly built target
because it imports the independently supplied scalar/form extension fixture.

This checkpoint does not infer completion of all native workflows, the frozen
independent-leaf experiment, or independent mathematical acceptance. Public
structured data forms containing references that have no implemented typed
projection branch still report an explicit unfinished kernel preparation gap;
they are not reclassified as missing leaf implementations. A valid anonymous or
opaque packet without any retained independently derived mathematical operand
cannot invent one through an interface validator's fresh placeholder. Whole
retained result references remain the supported bridge in those cases.
