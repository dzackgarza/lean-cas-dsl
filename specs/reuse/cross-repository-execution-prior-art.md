# Cross-repository execution prior art

## Queries

The owner supplied [issue 69, Addendum IV](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6402830212)
on 2026-10-25. Its complete source was read, together with the current
`sage-categories` implementation at
`37ec1642fe19f24fb00f402fe45350341ebf6920`: `COMPLAINTS.md`, `DECISIONS.md`,
`TODO.md`, `kernel/functor_cache.py`, `cat_kernel/functor_declarations.py`, and
the Catlab and cell engine adapters. The source of `research#197`,
`sage-categories#26` and `#35` was also inspected. Constructor ownership was
checked against the [research design at d5b8b78](https://github.com/dzackgarza/research/blob/d5b8b78d2a003e10939e5490a13c52f91c686d07/docs/constructor-architecture.md).

External sources include CAP's [Managing Derived Methods](https://homalg-project.github.io/CAP_project/CAP/doc/chap8_mj.html)
and the primary [GATlab explicit-model discussion](https://blog.algebraicjulia.org/post/2025/02/refactor1/index.html).
These broaden the earlier comparison with Sage functors and CAP `ApplyFunctor`.
Local source searches cover `CategoryContext`, `CellAction`, `ReindexAction`,
`SelectedLift`, `StructuredResult`, `DirectConstruction`, `Semantic.edgeFunctor`,
and the actual action executor. The mathematical operations are the existing
Mathlib category composition and natural-transformation components; no second
categorical calculus is needed.

The bounded declaration-derived regression also inspects the live registry's
`edgesFrom`, `routes` and `isFirstOperationBindingRoute`, the exact applications
from `Semantic.routeFunctorWithApplications`, and the existing
`selectedOperationApplicationsWithSources` and `retainedActionResult?` consumers.
The 2026-10-25 formalization-corpus queries `Functor.comp` and `IsIsofibration`
could not reach the corpus endpoint in the execution sandbox. Direct searches of
the accepted catalogue at `82d1370` and its existing functor/lift controls provide
the reuse sources; no substitute mathematical definition is authored.

## Owner

`lean-categories` remains the sole mathematical authority. Its checked
declarations fix the complete categories, selected functors, comparisons,
constructors, parameters, endpoints and propositions. The kernel consumes those
declarations. The computational contract supplies typed data frames and requests;
neither a backend's implementation nor its answer supplies a mathematical owner.

Earlier projects have a different leaf-authoring regime. Their private import
firewalls and Python implementation-class restrictions do not transfer here.
Private lateral imports, shared algorithms and arbitrary implementation
dependencies are allowed. The transferable requirement is that implementation
organization cannot determine mathematical meaning, inherited availability or
acceptance. An optimized realization of an already fixed composite is compatible
with that requirement.

## Existing mechanisms and their use

| Inspected mechanism | Applicable lesson and current kernel use | What the source does not establish |
| --- | --- | --- |
| CAP derivations record prerequisites, category getters, implementation functions, saturation and derivation trees. | Computational availability can follow the dependencies of a fixed operation. The service evaluates typed requests against existing published addresses and can report the missing dependency. | Computational weights cannot choose a mathematical route or replace its proof of applicability. The new deferred graph is not a claim that CAP's full saturation machinery has been implemented. |
| GATlab makes a complete model explicit even when distinct models share native carriers. | `CategoryContext` retains the selected category dictionary; complete object and Hom checks use it. The cartesian-service control requires composition with this explicit dictionary. | A carrier type, native class, equal packet, or method name cannot identify the intended mathematical structure. |
| `FunctorImageCache` retains the actual image of a selected source; selected transport initializes target computation with actual action data. | The shared action executor retains the original action, ordered parameters, actual source occurrence, image endpoints and supplier. Equal formal endpoints with different actual packets remain separate. | Historical selected-transport tests and a surviving implementation do not establish current combined acceptance. The current upstream TODO explicitly reopens that obligation. |
| The Catlab adapter materializes identity/composite functors and executable natural-transformation composition, whiskering and horizontal composition. | The Lean runtime reuses its existing selected actions and `CellAction` component applications. Actual component computations must connect the retained images. | A retained formal natural isomorphism alone does not execute a conversion. No Catlab semantic registry is imported into the Lean kernel. |
| The `homotopy-core` adapter supplies formal cells, compositions, inverses and type checks. | Formal higher-cell structure and executable component availability remain separate. Lean continues to own the relevant mathematical declarations. | Formal invertibility is not a backend component implementation or a current integration verdict. |
| Research's `construction_owner()`, selected identity implementation, and `with_limit_lifting` retain a chosen construction and its universal data. | Existing `Semantic.limitPresentation`, `SelectedLift`, `StructuredResult` and `LiftedSubobjectData` supply the shared constructor/lift boundary. Service preparation preserves the original diagram, parameters, cone, maps and previous outputs. | A cone-shaped packet does not establish its equations or universality. The cited owner repair and templates are historical evidence, not an executed current research migration. |

Pinned implementation sources for the table are the
[functor cache](https://github.com/dzackgarza/sage-categories/blob/37ec1642fe19f24fb00f402fe45350341ebf6920/src/sage_categories/kernel/functor_cache.py),
[selected declarations](https://github.com/dzackgarza/sage-categories/blob/37ec1642fe19f24fb00f402fe45350341ebf6920/src/sage_categories/cat_kernel/functor_declarations.py),
[Catlab adapter](https://github.com/dzackgarza/sage-categories/blob/37ec1642fe19f24fb00f402fe45350341ebf6920/src/sage_categories/engines/catlab.py),
[cell adapter](https://github.com/dzackgarza/sage-categories/blob/37ec1642fe19f24fb00f402fe45350341ebf6920/src/sage_categories/engines/cells.py), and
[current execution obligations](https://github.com/dzackgarza/sage-categories/blob/37ec1642fe19f24fb00f402fe45350341ebf6920/TODO.md).

## Separating regressions

The earlier failures are inputs to the existing KM obligations, not a new semantic
registry or an alternate acceptance ledger. In addition to the unchanged fixed
questions and independently authored frozen-leaf trials, the live declaration
projection must support the following checks from Addendum IV and
[research#197](https://github.com/dzackgarza/research/issues/197).

| Historical separation | Required distinguishing behavior |
| --- | --- |
| Distinct additive and multiplicative images (`sage-categories#26`) | Shared implementation code and equal carriers do not merge selected structures, actual image data, units or operations. Selection order must not change the result. |
| Composite inheritance (`sage-categories#35`) | Retain both actual factors, including nonidentity object and map actions, and consume the formally supplied composite classification. A fresh per-leaf inheritance wrapper is not the repair. |
| Refinement after construction (`#31`, `#33`, `#27`) | Existing descendants, original inverse pairs and selected constructor data survive subsequent refinement and different construction orders in one live session. |
| Chosen universal data (`#34`, `#22`, `#23`) | Reuse the actual chosen diagram, apex, oriented legs and nonidentity factor. Check independent mathematical equations, not merely packet presence. |
| Finite/countable underlying operations (`research#197`) | Derive actual cardinality, enumeration prefixes, indexing and round trips through published selected functors where the mathematical surface provides them. Missing computation remains a gap. |
| Numerically correct semantic bypass (`research#197`, `research#428`) | A result cannot replace the original formal owner, admitted route, action or endpoints. The test targets changed mathematical provenance, not a leaf's legitimate private algorithm or a fused realization of the fixed composite. |

Case discovery must inspect the live accepted declarations. It must not create
stored per-parent route certificates or a parallel graph that can disagree with
the mathematical owner. Engineering controls of source retention and protocol
framing supplement, and do not replace, independently grounded mathematical
assertions and their independent reading review.

**Composite-isofibration interface dependency.** The inspected published
catalogue supplies structural functor flags, separate `MonoLift`/limit-creation
interfaces, and `FibrationEntry` evidence for `IsFibered` or `IsCofibered`.
It does not expose a composite-isofibration classification interface to this
consumer. Consuming that formal classification remains an upstream-interface
dependency of the composite-inheritance obligation above. Neither a structural
flag, a composed `MonoLift`, an `IsFibered` proof nor a successful computation is
substituted for it. The bounded engineering regression tests complete selected
action composition only.

## New code and current limits

The published action boundary at `4fb1aa9` supplies actual object and whole-map
execution, derived classifier/constructor action addresses, retained images and
supplier-aware data. Its focused process controls and combined consumer build
passed. These are engineering results; they are not the frozen two-leaf or full
V1 acceptance verdict.

The published contract at `9167e4c` adds ordered typed deferred calls and scoped
result references. Pure service preparation now compiles for ordinary actions,
components, cartesian maps, presentations, limits and selected lifts. The
component/cartesian/presentation controls preserve the original selected formal
application and reject changed repeated data, contexts, operations and endpoints.
The universal controls retain complete output slots, selected prefixes and the
original independently checked factor condition. These pure controls have not
executed the complete runtime service.

Runtime DAG execution, actual cross-process ownership and bridge handling,
declaration-derived regressions, the independent frozen source/target trial,
connected real-engine workflows and the full unchanged fixed-question runs are
still integration obligations. The old historical positives, the new source
checks and a source push must not be reported as satisfying those obligations.

The service adds computational orchestration around the existing owners. It
accepts no caller-selected result type, backend selector, Lean proof, equality
claim or new mathematical declaration. A well-framed wrong answer remains a
wrong computation against the original question.

`CasAcceptance.Kernel.DeclarationDerivedTransportProbes` adds an optional pure
engineering control. It discovers closed registered object and morphism
declarations and routes from the loaded registry, retains complete inferred
action parameters, separates shared-carrier monoid images and operation owners,
and checks ordered two-action framing and exact actual-data reuse keys. Its
separate cardinality control obtains its literal codec and closed source objects
from the live declarations, validates an arbitrary numerical reply at the full
published result interface, and requires ordinary result reuse to retain the
original method owner, receiver, route and accepted comparisons. It asserts no
mathematical equality between that numeral and the formal result. Its
optional report comes from the same discovered cases and is never an input.
The module fails when no separating case exists. Arbitrary packets witness
retention only; no backend is started, no packet is treated as a mathematical
answer, and neither process-level anti-bypass nor extension acceptance follows
from this control.

Formal two-action checks apply to every discovered closed case in this bounded
slice. Packet framing additionally needs the existing complete parameter data.
When a fixed parameter has no portable named presentation and requires an actual
supplier, the pure control records that explicit dependency, keeps the formal
check, and does not fabricate a replacement parameter. At least one separating
complete packet case must still succeed; missing all such cases is a failure.
