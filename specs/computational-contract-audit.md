# Public computational contract audit — 2026-10-24

## Exact status and ownership

This source audit was refreshed for final public-contract preparation on
2026-10-24. The documented B0 request/reply families have public representations,
parameter order, complete endpoint and ownership rules, and corresponding generic
validator paths. No additional executable wire form or public-guide change was
found necessary in this pass. This is documentation and source coverage, not a
kernel-readiness, frozen-build, or mathematical-correctness conclusion.

The contract clone is `/tmp/kernel-v1-contract-completion-20261024`, clean at local
`3a5014096bc67f952f9fc444787b3a2aafe34282`, tree
`04f2f04ca8b5622f703b1bef7e7384a0bc72f66c`. The public contract is
`89de508622cff4bfd1a457844a1a3a0fccd36405`. Its `Port.lean`, Python helpers,
wire guide, API guide and dependency lock were compared byte-for-byte with that
public commit. The lock selects mathematical source
`ae3c76e7a439681ad264a3d1cf113cb55d4f8fcc`. The independent mathematical owner
reports that its added generic coordinate-linearity evidence changes no public
registration inventory or signature and introduces no wire form; no mathematical
assertion outcome or leaf implementation was read for this audit.

The generic consumer source inspected was clean kernel
`fdc3a9c7568184477a8231160131e56e5125fb54`. The five audited files remained
byte-identical at the next checkpoint
`08051c0fa4b233e70173aa6a37dd38dccadc0ab1`; their digests appear below. These
are source-review checkpoints, not an asserted final compiled producer tuple.
No Lean compilation or new API export was run in this preparation pass.

The dated boundary report used by the original audit was `DEFECTS.md` at
`2c8b9040ea68513c34817f5c7b6fa5a5ce6b1252`, blob
`e0855333b55b172a87088e7c328ea0ab7ba3969a`. Its request families are retained
below without reopening downstream source or results. Existing control references
below record earlier source inspection; they were not rerun or reinterpreted as
same-source passing evidence in this pass. Leaf self-reports establish no
mathematical correctness.

This audit belongs in kernel documentation. The leaf-visible counterpart remains
`api/wire-examples.md`, including “Compatibility with earlier boundary reports.”
The public contract contains no downstream assertion or engineering-probe names.
No permanent assertion, old leaf implementation, or executable contract source was
changed. Both the authoritative old API snapshot and the separately labelled
public candidate were left unchanged.

## Shared request and result path

The authoritative public framing is `CasContract/Port.lean` plus
`api/wire-examples.md`; declaration signatures and parameter ordering come from
the generated public API. The kernel `Admission.RegistryState.callable?` resolves
accepted callable declarations, and `inputAddresses` / `pointInputAddresses`
provide actual admission addresses. Category-wide registrations are admitted
peers, not an operation-specific fallback priority.

`Backend.PointInvocation` contains exactly operation, parameters, actual arrow,
original generalized domain, source, target, and actual argument. A named map,
operation, binder, or object application uses its complete declaration parameters
in the actual-arrow descriptor; operands belong in the argument. `valueData`
retains portable or nested computational data and `opaqueData` names native data
on its existing live connection. Neither supplies formal proof.

Production responses use `ComputationalData.validateElementAt`,
`validateEndpointPort`, or complete structured-result port validation against
the independently fixed interface. `Realize.receiveComputationalData` retains
the actual returned data, and `computationalScope` recursively detects opaque
references. `combinedPayload` / `mergeOwners` preserve the owning session across
compositions and parameters. The formal term remains separate from the answer.
The literal decoder `Codec.decode` is not a substitute for this computational
data path and is not a general proof reconstruction requirement for leaves.

## Mapping the dated missing families

### Nonintegral rational and irrational/complex values

Public path: a rational is the existing record `[integer numerator,natural denominator]`;
the denominator is positive and the pair reduced. Zero is `[0,1]`. Exact real or
complex values may remain owned opaque data or use a complete
`element(selected,point(registeredArrowOrComposition))` expression. A real-to-complex
inclusion is an ordinary accepted inclusion-row arrow. Division is the declared
morphism on `M × Units(M)`; `mor.sets.divide` is not an element-operation ID.

Implementation: `Codec.encode` / `decode` derive record data; `pointSchema`,
`validatePoint`, and `validatePort` check inline scalar representation conditions
and discard the checked literal. `validateElementExpressionAt` uses
`validateCallableAt` for point arrows, enforcing the exact selected domain and
codomain. `Realize.decodeElementData` / `decodeArrowData` support public symbolic
descriptors when actual formal decoding is requested. Production owned replies
remain computational data through `receiveComputationalData`.

Existing controls: `CasAcceptance/ComputationalContractProbes.lean` accepts the
reduced rational, rejects missing fields, zero/negative denominators, nonreduced
pairs and a string numerator; it also preserves nested owned scalar fields.
The same module checks pi, square-root composition, opaque typed points, and
hostile wrong real/complex endpoints, wrong generalized domains, unknown
intermediate composition endpoints, and changed selected ring parameters.
`CasCatalogue/ElementDataProbes.lean` rejects changed object parameters and malformed
element-expression arity. These are framing/type controls, not numerical oracles.

### Bottom-valued polynomial degree

Public path: `none()` and `some(n)` at the declared `WithBot Nat` type, not a
negative integer sentinel or JSON null. The structural codec derives the
constructor labels and arities. Production replies pass the same scalar point
validator as other fixed result types.

Existing controls: `ComputationalContractProbes` decodes both constructors and
rejects an argument on `none`. `CasAcceptance/ComputationalTransportProbes.lean`
observes actual returned `some` data under the declared natural-to-degree
inclusion; a deliberately different well-framed result stays wrong instead of
being replaced by its equal retained formal term.

### Kähler differentials

Public path: retain an owned native differential, or return
`valueData(element(exactTarget,point(compose(actualPolynomialPoint,
mor.sets.kaehler_from_coordinate(R)))))`. The selected commutative ring parameter
appears in both polynomial coordinate and differential target. The public
coordinate is computational data; no derivative equality or derivation law is
inferred from the packet.

Implementation: this is the shared registered-morphism/composition path:
`decodeArrowData`, `decodeDeclaration`, `validateCallableAt`,
`interfaceDeclaration`, and `validateElementAt`. Exact types and parameters come
from the accepted coordinate declaration. Opaque data use the common live owner.

Focused validation: `CasAcceptance/Kernel/PublicFamilyContractProbes.lean`
passes the complete coordinate-differential reply through the production
response validator and decodes the complete coordinate declaration. It rejects
a missing ring, a changed selected ring, the reversed coordinate map, and a
nonconstant coordinate map used as a global differential. This verifies the
declared framing and selected types; it supplies no derivative answer or law.

### Matrices

Public path: nested total finite callable graphs `Fin n → Fin n → K`, or owned
native matrix/callable data. `obj.sets.matrices` has parameters `[n,selected
commutative ring]`, while vectors use `[selected set,n]`. Matrix application is
the declared `<object>#application` with complete parameters and a common apply
argument retaining matrix and vector data. A dense array is not a graph codec.

Implementation: `Codec.encode` / `decode` recursively encode finite callables;
`pointSchema` / `validatePoint` validate nested function data, inventories and
opaque rows. `validateCallableAt` and declaration decoding check the complete
application signature and parameter order.

Existing controls: `ComputationalContractProbes` decodes a nested matrix, accepts
an opaque row, rejects missing/repeated outer keys and an empty nested token,
checks the complete matrix-application arrow and rejects a missing coefficient
parameter. `CasAcceptance/Kernel/DependentElaborationProbes.lean` checks rectangular
matrix/tuple dimensions at the actual dependent types. Generic finite graph
controls also reject incomplete, repeated and out-of-codomain keys. Do not equate
these controls with native matrix arithmetic correctness.

### Possibly infinite spans and subsets

Public path: owned native subset; `powerObjectMap(pow.sets,image,[X,Y,f])`; or
`powerObjectMap(pow.sets,transpose,[X,predicate])`. A subset used as an object is
`extent(powerId,ambient,subsetData)`. Infinite maps/predicates may be accepted
named maps, composites, mediators or owned callables. A finite generating list
does not enumerate an infinite span, and the protocol invents no zero extension.

Implementation: `Realize.extentData?` retains actual subset data and dependencies;
`decodeArrowData` and `validateCallableAt` select the registered power-object field
and ordered parameters. `interfaceDeclaration` checks each parameter at its
complete type. `validatePort` handles native data without enumerating carriers.

Existing controls: `CasAcceptance/Kernel/ObjectPresentationProbes.lean` checks a
membership map at a retained computed ambient object, including the actual unnamed
endpoint and sole owning session. Shared callable/point controls check incompatible
endpoints and incomplete parameters. The executed `PublicFamilyContractProbes`
also validates image replies with an exact infinite-domain identity and an
owned typed callable, decodes the declared image, and validates an owned
predicate transpose. It rejects missing parameters, swapped map types and an
undeclared field. No finite sampling or enumeration is used as evidence for
the infinite maps.

### Binder maps and requests

Public path: every binder uses the seven-field common apply packet. The complete
actual-arrow descriptor carries the binder's ordered parameters; the argument
retains the supplied map or `admittedPoint`, its selected admitted domain and the
original generalized domain. Bounds, index objects and coefficient selections
are not reconstructed from carrier equality. Infinite callables need no graph.

Implementation: the `.binder` branch of `Realize.realizeFresh` checks the declared
source against the actual admitted target, preserves all parameter wires, makes
`Backend.PointInvocation`, dispatches with complete-request admission, validates
the response at the original domain, and merges request/result owners.

Existing controls: `ComputationalContractProbes` checks complete integral callable
parameters and missing-bound rejection; `CasCatalogue/ElementDataProbes.lean`
checks the binder domain's full structured parameter descriptors;
`CasAcceptance/Kernel/BinderReaderProbes.lean` checks declared binder choices and
complete typed requests; `CasCatalogue/QuestionProbes.lean` checks preservation of
the prepared binder operation snapshot. `StructuredExecutionProbes` checks an
explicit series binder's selected parameter and original generalized domain.
These do not establish integral/limit/series numerical correctness.

### Returned symbolic product apex and its actual projections

Public path: a complete product reply is
`valueData(cone(objectProduct(X,Y),typedMap(apex,X,leftCallable),
typedMap(apex,Y,rightCallable)))`, with the exact returned apex in both sources
and the actual request factors in the corresponding targets. Factors can retain
complete previously supplied object interfaces and native data. An apex alone
is incomplete. A later use retains `constructionApex` or `constructionLeg` with
the full diagram and actual cone; a native leg remains on its owner. Later
declared operations consume the stored projection within their arguments;
the creating limit ID does not become an arbitrary-map application operation.

Implementation: `StructuredResult.dataPlan` obtains ordered data ports and
endpoint roles from the accepted constructor before reading the answer.
`validatePlannedData` with `ComputationalData.validatePlannedPort` binds leg
endpoints to earlier actual apex fields and retained input roles.
`validatePort`'s `objectProduct` branch checks both factors at their complete
independently supplied interfaces, including retained action contexts.
`Realize.computationalApexReceiver` selects a compatible inherited receiver
without discarding the complete parent construction or a residual action.

Existing controls: `CasCatalogue/ComputationalActionContextProbes.lean` exercises
returned symbolic products using retained opaque action inputs, including nested
and deliberately noncanonical apices; it rejects missing context, foreign
categories, missing factors, and wrong typed-map roles even through nested
`valueData`. `CasAcceptance/Kernel/AnonymousApexProbes.lean` checks a complete
anonymous returned apex with its own actual inventory, owned apex alternatives
and creation packets. `ApexReceiverContextProbes.lean` checks category receiver
selection, preservation of the full parent result and owner, portability of a
selected token-free apex, contradictory context rejection and residual-action
retention. These are returned-result checks, not merely callable-source checks.
They intentionally do not prove the returned product law.

### Closed points in compositions and mediators

Public path: a complete `element(selected,expression)` may occupy an arrow slot
inside `compose` or `mediator`. The expression `point(arrow)` specifies a closed
point. A product point's value uses its two ordered components; it is not a graph
over its singleton domain. Nonconstant generalized maps retain their actual domain.

Implementation: `decodeArrowData` turns a complete element into its registered
global-source point and checks shared mediator domains. `validateCallableAt`
enforces exact composition/midpoint and mediator endpoint types. The
`.productMediator` branch preserves both actual component payloads and applies
accepted endpoint presentations once. `Realize.elementExpression` reuses cached
computed operand data instead of reconstructing it from its formal expression.

Existing controls: `ComputationalContractProbes` tests element-in-composition
and rejects wrong source/target and scalar replacement of a nonconstant map;
`CasAcceptance/Kernel/ProductPointFramingProbes.lean` checks ordered component
data, ownership and exactly-once endpoint comparisons;
`PortableExecutionProbes.lean` checks actual portable replies and owned computed
operand reuse. `ComputationalTransportProbes` checks opaque map composition and
observations of actual wrong data.

## Other dated boundaries

The wholly unlabelled structured composition uses two complete `typedMap`s;
their shared intermediate descriptor is preserved. A bare graph cannot choose
that intermediate mathematical object. Kernel/cokernel/subobject/quotient results
use full `arrow(source,target,definingMap)` (the compatible `subobject` spelling
requires the declared full subcategory). A kernel's object is the source slot;
a quotient's object is the target slot. Limits/colimits use the complete declared
cone/cocone constructor; prescribed lifts retain four ordered outputs per step,
both comparison directions, selected evidence parameters, and a separate factor
request. `ComputationalReuseProbes`, `LiftedSubobjectDataProbes`,
`StructuredExecutionProbes` and `CompositeLiftProbes` contain framing and reuse
controls. Independent mathematics remains responsible for law/answer assertions.

The dated reports also identify native engine availability and unsupported
lowerings (arbitrary monoid units, polynomial presentations, foreign tokens,
coefficient callables). Those are not repaired by inventing a wire form or
reading acceptance answers. An explicit support list is not a total function on
all natural numbers; an opaque value is not accessible from a foreign session.

## Actual fixes and evidence from this contract assignment

Published executable/export source `7abe31a85ac03e8b5ce13887fc7c1d6efdc54051`
has the exact tree of local `8397df15042598f5ce9a75cdb22675c65b06fc89`:

- Admission export now includes declared cartesian operation/input addresses,
  and every input form carries its complete category expression with a nullable
  named category ID. The finite export is not claimed to enumerate the infinite
  constructor-path component family.
- `tools/export_api.py` rejects a declared concrete lift/construction/cell/functor
  port absent from actual operation/input inventories, and rejects incomplete
  category contexts. The complete candidate and three hostile deletions were
  checked. This is export consistency, not mathematical acceptance.
- `Backend.PortError.disconnected` distinguishes interrupted connection exchanges
  from complete malformed replies. Eleven actual child-process protocol cases
  passed: five unavailable, five malformed, one noImplementation. The earlier
  contract fails the closed-connection case. Sources were supplied to root as
  `/tmp/kernel-contract-port-strata-20261024.lean` and
  `/tmp/kernel-contract-port-fixture-20261024.py`.

Metadata commits `55ae64f` and `469f5d9` add reproducible published math locks,
producer/publication revision guidance and explicit returned-product reuse
documentation. They change no executable Port code.

## Final-preparation source reconciliation

The public source now covers the generic families introduced after the original
boundary report, in addition to every family mapped above:

| Generic family | Public reference and exact framing | Generic consumer or validator |
| --- | --- | --- |
| Ordinary, whole-domain and terminal-point invocations | Seven ordered `apply` fields; whole map uses the original source and `identity(X,X)`; a nullary operation retains its actual terminal-source comparison | `Backend.PointInvocation.decode`; `Admission.pointInputAddresses`; `Realize` common invocations; `validateElementAt` or `validateEndpointPort` according to the original domain |
| Full element expressions and selected parameters | `element`, `operationExpression`, `point`, `operationPoint`, `pointView`; a declaration arrow contains parameters, while an expression also contains operands | `interfaceDeclaration`, `interfaceArgument`, `validateCallableAt`, `validateElementExpressionAt`; exact selected-owner checks remain in the generic operation branch |
| Complete admissions and constrained data | `admittedPoint` has six ordered fields; `constrainedPoint` has five and retains the exact constructor, data type, target and domain | Public Lean/Python framing helpers; `admissionInterface`, `ConstrainedPoint.schema?`, `validateCallableAt` |
| Selected category, constructor, functor and core data | `category`, `constructedCategory`, `functor`, `coreObject`, complete two-direction `coreIso`, direct object request and `#map` invocation | `interfaceArgument`, `interfaceAction`, `validateAction`, `validatePort`, `validateCallableAt`; complete selected dictionaries precede dispatch |
| Ordinary and constructor-induced natural components | `cellComponent`; `constructedCellComponent` with an outermost-first path; parameters `[declarationParameters,receiver,inverse]`; canonical dynamic address grammar | Public helpers; `Admission.component?` and `componentForm?`; `CellAction.assemble` and exact endpoint checks in `validateCallableAt` |
| Family reindexing and cartesian maps | `cartesianMap(reindex,functorParameters,receiver)`; common parameters `[functorParameters,receiver]` | `Backend.CartesianMap.decode`, `Admission.cartesianForm?`, registered family action and callable validation |
| Group/module hom objects, monoid/additive operations and direct image | Ordinary complete declarations, existing admission/application and operation packets; direct image is the ordinary `mor.sets.direct_image` arrow | Existing declaration/object-field/application/operation paths; no new tag, proof packet or private map-evaluation address |
| Truth-value observations and stratified failures | JSON boolean at the public truth target for the registered global-point domain; full callable for other domains; distinct unsupported, error, malformed and connection-loss outcomes | `Codec`/`PointSchema`, `validateElementAt`/`validateEndpointPort`, `Backend.PortError.stratum`; no answer becomes formal evidence |
| Returned structured data and source/target selection | Complete Arrow, cone/cocone, retained `constructionField`/`constructionLeg`, `morphismEndpoint`, four lift fields and separate factor; source diagrams remain attached through creation | `StructuredResult.dataPlan` and `validatePlannedData`; `validatePlannedPort`, `validateConstructionData`, `validateConstructionProjection`; existing lift execution and projection paths |
| Actual result reuse and sessions | Computed inline values remain actual results; nested opaque dependencies retain their original live connection | `Realize.computedPayload`, `forwardPayload`, `combinedPayload`, `containsOpaqueData`, `computationalScope`, `receiveComputationalData`, `mergeOwners` |

The former explicit-inventory follow-up is resolved in the public description.
There are two different interfaces. A function-valued record field with no fixed
primitive inventory may supply its own `finiteGraph` inventory; `validatePoint`
checks point shapes, distinctness and exact graph coverage. A complete structured
map instead has already selected actual source and target descriptors;
`validateEndpointPort` requires the source inventory, normally via `finiteData`
when no primitive codec supplies one. An inner `finiteGraph` must agree with
that source inventory. It cannot choose a different source. An owned or symbolic
callable covers a source without usable finite inventory. The matrix section of
the public guide states this distinction, and the inspected source implements it.
No relaxation of endpoint validation is required by this clarified contract.

The public guide already says that returned symbolic `objectProduct(X,Y)` is
an actual apex with both complete typed projections. Its coverage is not limited
to a callable-source annotation. `validatePort` validates both retained factor
interfaces; constructor-port validation ties both projection sources to the
actual earlier apex field and each target to its retained request role.

### Checks performed in this preparation pass

- Parsed all 27 public Python code blocks and all seven JSON values across five
  JSON code blocks. Schematic variables remain explicit supplied inputs; this is
  syntax/framing validation, not execution of mathematical examples.
- Parsed the complete square-root request through the public helper, checked
  whole-map identity retention and the documented map/endpoint/comparison helper
  envelopes, and rejected three incomplete or mistyped envelopes. These checks
  use only the public protocol and no mathematical answers.
- Verified that all eight binder IDs in the existing public candidate occur in
  the guide's parameter-order table.
- Re-ran the Python address-consistency validator on the existing candidate:
  607 entries, 326 operation addresses and 566 input forms. Every concrete
  lift/construction/cell/cartesian port has its exported operation and input,
  with complete category context. Dynamic constructor-path components remain
  governed by the published grammar.
- Verified the public contract files named above against public `89de508`, and
  confirmed the authoring clone remains clean. No executable file changed.

The unchanged candidate is
`/tmp/kernel-mvp-public-api-candidate-546cffae-20261024.json`, SHA-256
`eecf444f9a3f007684c2c494085b02cbe6945b1add5ea90db2da5ad9a33c7612`.
Its actual producers remain kernel
`546cffae249e1d53c66cc7d62aeba74e426c6592`, mathematical catalogue
`4acd7aff0350c5a84ce695e42eaadfd583ac343d`, and protocol
`a131843a8c4cd8222814ca3949a27dc41dd7a29e`. The later contract documentation
and dependency lock do not relabel that candidate as a new export or final API.

### Reviewed source digests

| Source at kernel `08051c0` (unchanged from `fdc3a9c`) | SHA-256 |
| --- | --- |
| `CasCatalogue/Admission.lean` | `14af9de07036bd0f11000e2bd88a6dfed7edc6bf47690b1fa49b3f97e00d19c3` |
| `CasCatalogue/Codec.lean` | `b58ae05563beebd24b19faaea7d5b8af098f9972cc02ec696252b979b642d27b` |
| `CasCatalogue/ComputationalData.lean` | `3ac2f4910591c7dc8d0a598c65d93fab8fc9fc628efa033981a9b6551af720f9` |
| `CasCatalogue/StructuredResult.lean` | `75e493d48a4408588a6f0dcdd4879955d485013e77538cfd782f20312c099442` |
| `CasCatalogue/Realize.lean` | `4adbaa97339bb74b4fdeb04c0d1a777838a55dc16180e4a47e505d1f46b9e73a` |

Contract `CasContract/Port.lean` SHA-256 is
`1d2093178736f4c8c76bb578e8ee1ab5846da0f916f4b5e50d11752903266be3`;
`python/cas_port.py` is
`5f2c330047725cd429eec42ac0dbf0ca6f5933b723857d44859f1954a7e98e19`.
The authoritative stored `api/declared-ports.json` was left at SHA-256
`f3a17fd1d2fa98d72513fbe9ac333834f64b6b160a9ccd5206b97a5991802b19`.

## Remaining release actions, with evidence limits preserved

1. The integration owner must attach the final same-source build and execution
   evidence. No compile, connected mathematical workflow, frozen extension trial,
   or assertion outcome was examined or rerun in this preparation pass.
2. Coordinate-differential and infinite image/transpose response branches have
   inspected generic source coverage. This audit still supplies no dedicated
   newly executed family-specific validator result for them. The final evidence
   must retain that limit or attach the owner's concrete focused validation.
3. Final `api/declared-ports.json` awaits the owner's exact coherent frozen
   producer tuple. Reuse the documented export procedure with clean committed
   producer checkouts, exact package overrides, already compiled matching source,
   both declaration/admission probes, the same five extension imports, source
   and configuration checks, and atomic output. Producer and later publication
   revisions remain distinct; never write a self-referential producer revision.

The public documentation and framing portion is ready for that release step.
This conclusion does not substitute for integration or mathematical acceptance.

## Earlier focused integration evidence

The focused checks above used core modules compiled from local kernel
`85396b7c014c4f276b09f6ea1260d64081573951`, mathematics
`2dbf2f576ef5a4a406294d083fc52666c0010282` and contract
`aa8477de4aebc83823b88ac4885225e8fc13d9c5`. Probe syntax corrections are
recorded in `747c8a7`. Both dedicated public-family cases and the full
computational-contract probe completed successfully. Their raw logs are
`PublicFamilyContractProbes-baseline2.log` and
`CasAcceptance.ComputationalContractProbes.log` in the focused integration
evidence directory. Later reader/runtime changes require a final coherent rerun.

## Explicit graph inventories — integration correction

The function-field and structured-endpoint paths have different independently supplied inputs. A function-valued record field can use its own explicit `finiteGraph` inventory when no independent keys exist. A structured map has an actual selected source object; its graph must agree with that object’s existing inventory (for example, `finiteData(source,keys)`). An endpoint wrapper alone supplies no inventory, so it requires an owned or symbolic callable. The public matrix section now states this distinction explicitly.

A concrete bug in the nested function-field validator allowed `finiteGraph` to replace an independently fixed `Fin n` inventory. The integration patch rejects that replacement whenever keys are already fixed, while accepting a permutation of the complete inventory. The updated computational-contract probe passed, including partial outer and inner matrix inventories. This is validation evidence for the declared matrix representation, separate from native matrix arithmetic.
