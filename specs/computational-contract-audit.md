# Public computational contract audit — 2026-10-24

## Exact status and ownership

This is the kernel-side source audit of the dated downstream contract gaps.
It is not a completed validation report or an acceptance claim. The source
inspection below was completed; no additional Lean compile was run in this
contract-release turn. Final family-specific validation and the generated API
remain with the integration owner after the kernel and mathematics freeze.

The contract clone is `/tmp/kernel-v1-contract-completion-20261024`, branch
`work/kernel-v1-contract-release-20261024`, at local commit `469f5d9`.
The integration owner reports its exact tree published as `235eb7f`.
Its dependency lock pins the independently published mathematics commit
`2efe6e546d6932882d8e19242e567074aa0598fb`, including the public
`CommutativeRings` name repair. The executable `CasContract/Port.lean` is unchanged
from the published `7abe31a85ac03e8b5ce13887fc7c1d6efdc54051` source.

The dated leaf report inspected was `lean-cas-dsl-leaves/DEFECTS.md` at checkout
`2c8b9040ea68513c34817f5c7b6fa5a5ce6b1252`, blob
`e0855333b55b172a87088e7c328ea0ab7ba3969a`. Its active request-family questions
are under the 2026-10-20 review and the 2026-10-21 number-system/polynomial/binder
section. Leaf checks and self-reports provide no mathematical correctness evidence.

This document belongs in the kernel repository, not the public contract package:
the latter must not name downstream acceptance or engineering probes to leaf authors.
The leaf-visible counterpart is already `api/wire-examples.md`, especially
“Compatibility with earlier boundary reports.” No permanent assertion or old leaf
implementation was changed.

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

Evidence limit: generic declared-arrow, point-composition and changed-endpoint
hostile controls were located and inspected. No dedicated coordinate-differential
response-validator case was located or newly executed in this turn. The final
audit must keep that distinction or attach the integration owner's actual focused
validation; it cannot claim family-specific execution from a tag inventory.

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
endpoints and incomplete parameters. Evidence limit: no dedicated infinite
`image`/`transpose` response-validator execution was located or newly run in this
turn. Final evidence must state that limit or include a concrete focused run.

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

## Outstanding followup, stated precisely

1. The integration owner must attach final same-source build and focused-run
   evidence. This audit turn did not rerun Lean or claim all modules passed.
2. Dedicated coordinate-differential and infinite image/transpose response paths
   have source-level generic coverage but no newly executed family-specific check
   in this turn. Preserve that distinction in the final audit.
3. The inventory distinction has now been resolved against both validators and
   the public endpoint specification: a function-valued record field may supply
   its otherwise unknown inventory, whereas a structured map must agree with
   its actual source object's existing inventory. The matrix section now states
   this explicitly. The nested-field validator's separate bug allowing an
   explicit inventory to omit known indices was corrected; its new hostile
   probes await the integrated batch described below.
4. Final `api/declared-ports.json` has not been regenerated. The extension snapshot
   `/tmp/kernel-mvp-public-extension-api-20261024.json` previously validated
   318 operation addresses and 558 input forms; it is not the final frozen API.
   Generate only after final kernel/math inputs settle. `api/README.md` records
   the procedure: clean committed producer checkouts, exact package overrides,
   existing compiled dependencies, source/digest verification, atomic output.
   The snapshot records those producer commits. A later commit containing the
   snapshot is its publication revision and must not be substituted back into
   its own recorded producer tuple.

No additional review, build or API export was performed after root requested
this immediate checkpoint. The detailed audit still needs incorporation into
the owning kernel documentation and final evidence reconciliation.

## Explicit graph inventories — integration correction

The function-field and structured-endpoint paths have different independently supplied inputs. A function-valued record field can use its own explicit `finiteGraph` inventory when no independent keys exist. A structured map has an actual selected source object; its graph must agree with that object’s existing inventory (for example, `finiteData(source,keys)`). An endpoint wrapper alone supplies no inventory, so it requires an owned or symbolic callable. The public matrix section now states this distinction explicitly.

A concrete bug in the nested function-field validator allowed `finiteGraph` to replace an independently fixed `Fin n` inventory. The integration patch rejects that replacement whenever keys are already fixed, while accepting a permutation of the complete inventory. The focused contract probe includes partial outer and inner matrix inventories. This paragraph records the implemented correction; execution of the updated probe is pending the integrated batch.
