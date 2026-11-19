# Data model: retained mathematics, actual selections and computational values

**Feature:** `001-categorical-research-language` · **Current design:** 2026-11-07  
**Requirements:** [clarified scope/scenarios](spec.md) and [FR/SC obligations](spec.md). **Mathematical consumption:** [current consolidated contract](contracts/mathematical-input.md).

Names below are proposed engineering records, not new mathematical definitions or a claim that the native API is implemented. All subject meanings, laws, choice families and abstract computational obligations remain independently owned by lean-categories. This consolidation incorporates the actual-selection clarification and the existing [staged/suspension](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6684996781), [export-capture/transport-ID](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6706802517), and [observation/liveness](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6707359041) corrections. Their detailed wire transitions remain in the owning runtime/notebook contracts.

The platform remains Lean 4.33.0 with accepted lean-categories, compatible CSLib `3951377e5a3f5772737f11cd62bc5bb6a72f95d1` and PolyFun `a5895e454254a400774fa396b64d5b968f0933df`. Source compatibility is research evidence, not a build or acceptance result.

## 1. Authority and distinct identities

| Layer | Owns | Does not establish |
|---|---|---|
| Independent mathematical environment | Categories, operations, domains, structures, cells/coherence, admissible choices, abstract computational families and representation/continuation relations | That a backend returns correct data |
| Semantic program | Complete source question, context, actual selected terms and result roles | Computation availability or an execution occurrence |
| Compiled program | Faithful operational interpretation, dependent layouts, frames and prepared primitive boundaries | New mathematics or correctness of arbitrary primitives |
| Runtime value graph | Actual returned candidate data, exact chosen fields/maps/captures and completion associations | Truth from decoding, a tag or a leaf-supplied proof |
| Live resource ledger | Actual connections/generations, monotone IDs/reservations, active coordination and invalidation | A second completed-result store or restored permission to execute |

Keep mathematical term identity, compiled program identity, execution occurrence identity and returned value identity separate. Definitionally equal expressions or identical bytes may occur in distinct computations or selected roles. Restoring a snapshot or reprinting an expression does not reproduce an old execution or value.

A further distinction is essential: an allowed choice family is not an actual selected member, and a selected comparison is not evidence that every possible route/cell is equal. Its mathematical role and required data are fixed upstream; the runtime retains the actual candidate member supplied under that role.

## 2. Source environment and complete dependent context

### SourceRef / SourceSnapshot

Retain repository revision, module/declaration, exact universe application, registry reference and complete imported dependency context. Digests are integrity/provenance/cache keys, not equality proofs. Cache inputs include everything that can change elaboration, selected interpretation or compilation. Added declarations can change first bindings or introduce genuine readings; a previously successful selection record is not automatically valid for that changed query.

### ContextTelescope

Each ordered binder retains stable BindingId, parameter/definition/hypothesis/selected-structure/formal-result role, complete type/universe dependencies, binder information, prior dependencies, defining term where present and source provenance. Associate actual computational values in a separate runtime-binding map. Close persistent expressions over the full telescope; reopening creates fresh locals and an explicit bijection to stable IDs. Raw FVarIds and metavariables are not durable identities. Completed questions contain no escaping locals or unresolved expression/universe metavariables.

Hypotheses remain scoped hypotheses. A foreign reply cannot append a proved proposition or law-bearing inhabitant. Universes, instance dictionaries, formal proof arguments and selected structures stay in the semantic program even when no payload is needed. Erase only justified proof fields; a data-bearing subsingleton may contain a mediator/inverse/map and is not erased merely for being subsingleton.

### SemanticQuestion / SelectedCell / RequiredSelection

`SemanticQuestion` retains original source/span, complete context/result family, actual selected operation/route, qualifications, explicit constraints and the source-governed interpretation status. Provider manifests/results do not determine that status.

`SelectedCell` retains its actual independently accepted source term and declaration, complete functorial boundary, parameter substitution, direction, occurrence, whiskering, constructor action, components and required higher witnesses. An ordinary natural isomorphism is one case, not a closed two-dimensional taxonomy. Keep native higher terms at their actual types/dimensions/boundaries. A cell is not a Boolean path-equivalence flag. Invertibility, equality of cells, operation agreement and a selected occurrence are different source data/judgments.

`RequiredSelection` is an operational reference to a requirement already in the accepted interface: exact source role, complete dependent boundary, fixed-versus-choice status, permitted supplier, availability stage and dependent uses. It contains no new leaf-authored admissibility predicate. A formal selected route/cell must be supplied/checkable where the source requires it. A prescribed computational choice is candidate data under the already fixed family. Missing mandatory data prevent their dependent use; they are not populated from a shortest path, provider success or an invented default.

The compiled preparation distinguishes: using an already selected cell, computing a permitted choice, and comparing inherited meanings under a licensed full-family agreement rule. It has no universal all-route cover field required for every selected computation. If a particular source obligation requires a uniform comparison/coherence witness, that exact required datum remains mandatory.

## 3. Result roles and actual choice binding

| Role | Required independent input | Continuation |
|---|---|---|
| FixedResultRole | A specified source value/function at full arguments and its accepted representation interface | Candidate data represent that fixed result; actual fields/maps remain retained. Alternative presentation requires the independently fixed interpretation/comparison. |
| PermittedChoiceRole | A source-declared family actually allowing a selected result, with its exact admissibility and dependent continuation relation | Bind the actual candidate member and all dependent data. Different permitted members need not be equal or canonical. |

A Lean result type alone is not permission to choose. A fixed function using Classical.choice remains fixed. An ordinary ambiguous request is not silently converted into a choice-producing operation. When the independent computational contract assigns a route/cell/choice datum to a leaf, the leaf supplies it as data and may not omit it; the leaf neither defines the family nor proves its laws. Successful structural admission is not proof that the candidate is valid mathematics.

Formal result binders are parameters of a previously specified conditional continuation. Binding candidate data does not add an axiom or prove the source relation. Conditional preservation uses the independently stated primitive/choice relation; actual correctness evidence comes from independent assessment. Provider independence fixes the complete question/context; it does not assert that different legitimate returned choices give identical later contexts.

Result roles also retain exact/approximate qualifications, selected conventions, size/existence hypotheses and complete continuation interfaces. Finite encodings or displays do not reduce infinite/higher scope.

## 4. Computation families and different graphs

Consume `CheckedComputationDerivation` with its exact target reference/declaration, rigid universes, family expression/type, ordered distinct prerequisite references and full types, ordinary template, accepted plan and correctness equality. Validate before specialization. Equal prerequisite types do not merge identities. Compile ordinary required expression forms; a prerequisite closure selects each actual reached invocation, not every argument of a family from one registration.

| Graph | Contents | Purpose |
|---|---|---|
| Structural reading representation | Actual source-rule/constructor derivations and first-binding routes with complete contexts | Exact candidate structure; not a selected comparison, semantic quotient or computation |
| Semantic/compiled program | Native selected expressions, actual cells, required roles, accepted computation templates, layouts and closure code | Fixed mathematical question and faithful operational control, including dormant dependent calls |
| Realization dependency graph | Exact current demands and primitive/generic/fused alternatives with ordered slots | 0/1/many finite grounded computation analysis only where exact finite closure is justified |
| Runtime value/occurrence graph | Actual returned values, choices, field/capture dependencies, dispatch occurrences and completion associations | Executed result and later use, not reconstruction from the other graphs |

A result-dependent child remains code plus its actual environment until arguments exist. A unique current realization does not prove availability/uniqueness of every future invocation. Later failure never authorizes replay under another provider.

`PreparedDemand` fixes the source question/result role, full formal parameters and actual argument references, accepted data interface, source operation and route/cell data, mandatory selection gate, transaction and occurrence identity. New operations are not forced onto an input's producer merely because it has an owner; applying an existing native callable uses that actual owner.

## 5. Data interface, storage and liveness

`DataInterface` is mechanically generated from accepted computational roles. Every field retains stable slot, actual source projection, complete dependent role, preceding-field dependencies, storage kind and permitted actions. Formal laws are not reply fields. A required selected map/cell/choice datum cannot be replaced by an existence proof or omitted because several valid choices exist.

| Storage form | Actual content | Owner dependency |
|---|---|---|
| PortableData | Immutable scalar/container encoding with fixed interpretation/qualifiers | None solely from supplier; referenced dependencies retain their owners |
| DependentRecord | Exact ordered field references, roles at actual earlier fields, retained lazy continuations | Per-field and actual-use dependencies, not an unrelated blanket owner |
| ComputationalClosure | Operational code with exact captured runtime references and formal callable interface | All required captured owners and actual primitive owners when invoked |
| IndexedInterface | Full index/argument family, callable operations and retained environment | Actual captures/owner; no index enumeration implied |
| SymbolicData | An accepted representation expression with actual environment/public operations | Its actual retained dependencies; a descriptor alone is not proof of execution |
| OwnedHandle | Actual local export token, supplying connection generation, prepared interface and ordered retained captures | Supplying generation plus all transitive required capture owners |

The kernel stamps actual owners, not returned owner strings. Returning an input reference preserves its original owners. Hidden native memory grants no undeclared gateway scope; faulty provider dependencies remain computation faults, not semantic authority. Whole-reply admission validates every promised role/reference/export before any field is staged.

Separate three operations:

1. **Visibility:** locate the original committed or same-transaction staged association. No payload is reconstructed from the ledger, name or expression.
2. **Stored projection/inspection:** read an already stored field or inert metadata. It does not require an unrelated sibling's owner, run a lazy field, or revive a dead handle.
3. **Computational use:** check the complete owner closure required by this prepared demand before reservation and send. Whole-record use and every export/suspension capture retain their genuine dependencies.

These distinctions preserve both independent portable-field survival and stale-use rejection. They do not allow partial initial admission, partial cell publication, missing-value reconstruction or dropping a real dependency.

## 6. Capture records and exact scope correspondence

A native export stores the actual callable and ordered immutable `(value reference, prepared role)` captures, plus original-proxy-occurrence/capture-index correspondence resolved before the old scope expires. Both published and dependent `$cas.invoke_export` forms carry a fresh capture prefix. Context/arguments follow it without merging equal-valued distinct roles. The SDK uses an invocation-local frame; no global mutation of shared proxies, old numeric-slot interpretation or ambient expired-scope access. All supplying/captured/context/argument owners are checked before send.

An export lease may support repeated fresh invocations; a suspended continuation token has one reserved resume. `SuspensionRecord` stores actual supplying generation, originating occurrence/transaction, its explicitly retained ordered capture/role table and child group. Resume has a fresh scope with captures first and exact child results next. Invocation suspension explicitly transfers current-frame captures, not a kept-alive ambient frame. Child failure/cancellation retires the appropriate descendants; no retry or alternate provider.

Request-local discard revokes only newly introduced leases/continuations and preserves previous committed leases. Disposal does not claim native memory was freed where the engine exposes no release API. A lost cleanup reply cannot authorize resend.

## 7. Concrete source-selected lift

For selected `L : MonoLift U`, retain formal `X,K,i`, monicity, actual `L,U` and these independently defined roles:

| Field | Formal role | Runtime data |
|---|---|---|
| Object | `L.obj X i` | Actual returned object representation O |
| Defining map | `L.hom X i : L.obj X i ⟶ X` | Actual map tied to O and original X |
| Forward comparison | `(L.iso X i).hom : U.obj (L.obj X i) ⟶ K` | Actual forward map and selected image interface |
| Backward comparison | `(L.iso X i).inv : K ⟶ U.obj (L.obj X i)` | Actual inverse-direction data, not endpoint-derived identity |
| Factor callable | `L.factor X i g f hf : Y ⟶ L.obj X i` | Actual retained preceding fields and Y,g,f; hf remains formal premise |

The selected object is fixed by L; do not turn it into an arbitrary lift choice or replace its comparisons. A genuinely choice-bearing source declaration has its own independently fixed role. The first factor's actual output can become the next lift's base map, retaining identity/captures/owners. Existing `factor_comp` and computation equations justify the mathematical composite; Port order/addresses do not supply those proofs.

## 8. Publication, observation and live metadata

`StagedCompletion` exists after a whole reply is validated in the active transaction and allows same-cell reuse. `CommittedReceipt` exists only after whole-cell commit publishes the entire program/value/observation/output delta. Abort removes staged data without restoring consumed dispatch rights. Neither record is correctness evidence for opaque computation.

The live supervisor outside snapshot rollback stores nonce, monotone IDs, reservations, actual connection generations, permits, request-ID admission metadata and active coordination. It stores no completed payload/closure heap or recovery cache; settled promise payloads are removed. Completed values are accessible only through visible immutable state or active staging. A used transport-ID tombstone is not a hidden receipt.

Owner loss changes computational liveness, not mathematical meaning or immutable payload. Old snapshot selection cannot reset owners/reservations or bind old tokens to new processes. A fresh worker nonce does not resurrect old references by replay. Cooperative cancellation, forced loss and indeterminate execution retain their separate outcomes.

`ObservationDescriptor` contains immutable source-derived type/context/selected-map/choice/qualification/provenance data prepared at an authorized compilation/publication boundary. It contains no executable renderer, delaborator, proof procedure, documentation hook or lazy/provider callback. Query success and error paths use data-only lookup/formatting and never execute missing source or revive resources. Required descriptor preparation remains inside the original workload timing; useful full mathematical inspection is still required.

## 9. Compatibility and task consequences

Preserve public syntax/source spans and exact manifest triples. Wire packets remain encodings under independently fixed meanings. Generic scoped fields/callables and explicit lifecycle negotiation do not permit provider-defined schemas or subject mathematics. Delete semantic reconstruction from tags/defaults/trace endpoints/replayed source. Keep prepared recipes, retained lazy callables, actual completed values and receipts distinct.

T007 prepares roles/mandatory slots/observation data; T008–T011 preserve actual values and staging; T014–T015 justify/exercise those boundaries; T018–T023 implement actual scopes/capture/application; T053–T056 implement source-selected interpretation and its mandatory-data errors. T083–T102 implement the notebook/query/display consequences. Current task definitions incorporate those responsibilities; no new task IDs or completion markers are created by this model.

## Sources

- [Independent computation registry and consumer guide](https://github.com/dzackgarza/lean-categories/blob/fc6d3d6961223c75290c93da540c87f17a926cc7/LeanCategories/Catalogue/Registry/computation-derivations.md), with `Computation.lean` at the same pin.
- [Actual source registry roles](https://github.com/dzackgarza/lean-categories/blob/6c7f6a8f026500da30c00736580c5bd30c87331b/LeanCategories/Catalogue/Registry/Entry.lean) and [whole-operation agreement](https://github.com/dzackgarza/lean-categories/blob/6c7f6a8f026500da30c00736580c5bd30c87331b/LeanCategories/Catalogue/Registry/operation-agreement.md).
- [Lift/factor definitions and equations](https://github.com/dzackgarza/lean-categories/blob/fc6d3d6961223c75290c93da540c87f17a926cc7/LeanCategories/Catalogue/Lift.lean).
- [Released Port mechanics](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/f0431bebeb01c93cc65bb3fdc5bd23d9613e4b31/CasContract/Port.lean), not mathematical authority.
- [CSLib FreeM](https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean), [PolyFun handler](https://github.com/Verified-zkEVM/PolyFun/blob/a5895e454254a400774fa396b64d5b968f0933df/PolyFun/PFunctor/Handler/Stateful.lean).
- [Constitution](https://github.com/dzackgarza/lean-cas-dsl/blob/0db96de6cc73f02d5cefbe0eeba8183f60b7f67f/.specify/memory/constitution.md), clarified specification and current mathematical-input contract linked above.

## Required retained relationships

A retained result associates a source selection with an actual computational occurrence. Equal
formal expressions may have distinct occurrences. Projections and substitutions must preserve
the selected association. A selected morphism carries its endpoints; a universal construction
carries its diagram, cone or cocone, legs and universal operation; a lift carries its result,
defining map and comparison. A selected structure in a classifier fiber is distinct from proof
that the fiber is inhabited. Multiple justified refinements can coexist.

Dependent input relations come from the formal declaration and include actual earlier results.
These are semantic preservation requirements, not a new storage schema, mathematical IR or
registry. [C23](../../.specify/memory/constitution.md) and MM005–MM010 govern their use.

## Source uses and prepared inspection

The existing scoped role telescope indexes each mandatory datum by its complete source boundary,
permitted supplier, availability stage and dependent uses. Native type dependence and selection
of an actual value are separate uses: an argument, callable or parent record remains selected
even when a result type omits it. A projection retains its parent and original application
provenance; that provenance does not create another invocation argument list.
The producer retains the complete checked parent before exposing a projected view, together with
the declared projection path and all original native arguments, including proof arguments.
Preparation inspects the parent's complete field/action interface and retains its type and value
inputs separately. A data-bearing universal mediator remains present even when the visible result
is only an apex. These source roles do not manufacture a runtime parent value or add wire outputs.
Later aliases, field projections and stable-context transport retain this same original relation.
Admission requires the original immutable supplier references; an ambient equal-looking input
cannot replace them. Conversion validates the one retained relation after its inputs are fixed;
it does not select a parent or endpoint by searching equal candidates.

A native projection of a fixed category or type declaration remains part of the checked source
boundary. It does not by itself name a runtime occurrence. This classification follows the
original accepted declaration and its direct aliases or projections; a published computation
takes precedence even when it has no arguments or returns a type. An explicitly selected
occurrence or an already retained actual dependency keeps its required runtime reference; any
supplied declaration-key association is checked against that same reference.
An incidental argument whose native source names the same declaration does not establish such
an association. Fixed declaration uses and explicit actual dependencies remain distinct.

Constructor fields retain their exact projections and transitive preceding dependencies. Uses
inside callable fields retain the complete native binder prefix and their argument-domain or
result boundary. Each field also retains the external constructor parameters and enclosing source
bindings used by its type; its preceding-field table does not replace those references.
Native type-use sites distinguish positions and repetitions even when only
part of a dependent type is explicitly named. Only proposition-valued fields lose computational
payloads. A data-bearing subsingleton, including a universal mediator, retains its declared actions.
Named record descriptors retain the same ordered dependent-field bindings as native record
constructors; their public descriptor format does not replace those bindings.
Type-alias and original literal-lambda correspondence follow the declared native family with its
source operands held opaque. They retain the original occurrence position alongside each expanded
use, including repeated uses and inputs absent from the expanded result. Alias-input positions remain distinct
from result positions. Source-expression inspection keeps the original expression and its original
use positions. Explicit source-reference boundaries and selected operands also remain opaque when
they occur inside a native type. A bare operational mark that reuses an evaluated operand does
not establish a selected-source identity; it remains on the original term while structural
correspondence follows the original literal lambda. These inspection steps change no stored
native expression, type, context or selected reference.

Record the correspondence from a consumer's source binding to its selected supplying field when
the source is captured or constructed. Later preparation follows that correspondence and checks
the actual retained references. Equal definitions, types or payloads do not recover a missing
correspondence, and a later argument cannot erase an earlier consuming association.
Returning a child result to its parent may follow an already registered alias back to its
ancestor. The supplier must still have the same runtime value and comparable association
prefixes; incompatible sibling views remain distinct. A role-only relabel creates no alias.

Argument admission also instantiates the declared binder domain with the preceding checked source
arguments, in their original positions. Checking an operand against its own source type alone does
not enforce that domain. Where the declared domain and the operand retain actual type suppliers
at the same native use, those references must correspond. A fixed native domain preserves earlier
supplier provenance without requiring those suppliers to appear in that fixed domain.
An existing supplier cannot move from an original occurrence to a newly explicit occurrence.
Additional occurrences may repeat a supplier when its original occurrences remain in place.

A computation's result and each actual record construction receive their source identity before
dependent-interface preparation and their actual reference at completion. The result is distinct
from the callable and arguments that produced it. A bound
result's later fields retain that same selection; another invocation has its own occurrence even
when the source expressions coincide. Required references include the exact selected projection,
not an arbitrary value with a definitionally equal type.

When an executed argument enters a later native term, retain its original checked expression,
actual selected value and required type suppliers together. Structural beta and delta
substitution reuse each original actual operand across its repeated uses. The final output
address belongs to the completed application, not an intermediate callable projection.
Source wrappers retain their declaration's complete parameter positions before constructing
points, comparisons, cones or projections. The positions include implicit and proof arguments,
although proofs have no runtime payload. Each invocation binds the computational parameters
once and carries those references into stored field code. Nested wrappers retain separate scopes;
the runtime does not recover lost parameters by searching the wrapped expression for a declaration.
A compiler-owned family application retains its complete original lambda and argument table,
including inputs unused by its body, as well as the selected declaration's own argument positions.
Generated callable, type, tuple and transport uses share those exact invocation-local positions.
An authenticated native type alias keeps its original field address while the actual argument
retains every later immutable application/source association. Retaining an argument's history
does not add a dependency absent from the declared result's dependency interface.

A delayed family's wire parameters come from its original computational argument roles in
source order. Its retained captures also include selected source dependencies; those references
remain available for validation and ownership without becoming additional declaration parameters.

Both producing nodes and consuming aliases retain required selected source references. Returning
an existing input or projecting a record need not create an application, but must preserve the
consuming role's source data and each stored field's own dependent view. Ownership follows the
actual projections required by those types; an unrelated sibling's owner is not a dependency.
Stored projection reuse installs the complete prepared source references, including parent value
inputs absent from the visible type. Reusing a published source address may extend its original
association chain on the same actual node, while its original published reference remains
unchanged. A different node, shortened chain or divergent association cannot replace that reference.
A projection association retains its actual parent and original declared field address even when
the field has no selected type or context dependencies. The immutable graph validates that parent
reference's visibility; it does not add all of the parent's owners to the field's required owners.
Repeated demands reuse a published projection through that exact parent and field relation,
including each retained intermediate projection. Preparation and ordinary, deferred and
provider-requested projection execution share this retained value and its admission and
availability checks. A role-only relabeling or a matching native declaration cannot establish
this relation.
When a completed checked application changes the result's dependent type, its result view records
that declared type while retaining the complete input provenance and owners. A candidate's new
output address cannot authorize its own admission. External returned references are validated
against the original prepared environment before a new result association is installed.
Returning an already selected value checks that final value's required owners and retains it
for the atomic commit check. Projection selects the actual field before this check, so an
unrelated sibling's owner does not become a requirement of the returned field.

Prepare readable observations and their exact native source snapshot at the authorized request
boundary. The inert data retain complete contexts, stable binding identities, selected instances,
universes, field/use addresses and provenance. Reading them later requires no elaboration,
delaboration, proof procedure, provider request or lazy computation; a readable type summary
alone is insufficient when it hides required source data.
