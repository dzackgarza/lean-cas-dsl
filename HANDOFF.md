# V1 kernel MVP: authoritative integration handoff

## 1. The task

Finish the usable V1 kernel of `dzackgarza/lean-cas-dsl`, including the mathematical interfaces and computational contracts it needs. Deliver a working computer algebra system whose supported extension mechanisms let a new leaf author implement registered operations through the public contract. Ordinary leaf work must not require repeated repairs to generic kernel infrastructure.

The assignment includes implementation, integration, actual computation, independent extension experiments, and delivery. Continue beyond the interrupted build and beyond passing isolated probes. The completion conditions below define the whole task.

**Owner clarification, 2026-10-27:** do not focus myopically on making the existing
implementation pass. At each change, ask whether the mechanism itself is correct
against the mathematical interface and public computational contract. Existing
behavior and successful examples are evidence to inspect, not requirements to
preserve when they expose missing kernel work. Keep independently fixed
mathematical expectations unchanged.

Source conversation: [Finish Kernel MVP Work](https://chatgpt.com/c/6adc8d51-f270-83ea-ac4d-bcb9911c54d8). The original 2026-10-25 continuation and its purity-probe interruption are historical inputs. Current branch source, committed dependency selections and completed CI results govern continuation. No usable-V1 completion has been established.

Work primarily in the Pro cloud container. The rack connector's home-directory access is available for necessary supporting material. It is not authorization to move the entire build and execution workload to the user's server. Save and push coherent source changes throughout the work. Verify published source by fetching it back and comparing the complete tree. Preserve evidence separately from source so a container restart does not destroy the only copy.

## Current continuation state — 2026-10-27

### Resumed integration — 2026-10-28

The active source remains PR #67, `work/kernel-v1-20261023`; the older
`b0/kernel` references in the plan identify source inputs, not a branch to
restart. Issue #69 and all five addenda preserve existing action execution and
permit typed deferred plans; they do not require lateral-import prohibitions or
a synchronous callback topology. Implementation and completion obligations are
unchanged.

Latest completed candidate: `22d6eaf`, run `40552183732`, job `122358583354`.
It failed in `ComputationalData` before `Realize`, with a scoped callback arity
error and the unchanged 200000-heartbeat LCNF compiler limit. The current source
corrects the application and compiles the three existing dispatcher bodies
outside their recursive interface group. Independent source comparison preserves
all branches, validation order, defaults and scopes; Lean verification remains
required. Artifact `12757680219` has SHA-256
`4b7e7265fb366a04f6726a01f1b40c82e9c6dc03a0d84eca16f27a96f4806396`.
The ordinary-method, complete-result and other invocation work below remains
open; this compiler repair does not replace it.

### Retained comparisons and complete result roles

This integrated source retains complete forward/backward comparison Wires and
the exact image endpoints chosen by their enclosing actions. Computational
framing observes the required directions and records them separately from the
original source/target occurrences. Replaying a frame retains those same maps,
including their actual session owners. A proof of an Iso and an endpoint
interface do not establish that either map has executed.

Captured construction projections now have their own object, map or value
result interface. A scalar, dependent family or whole transformation keeps its
fixed expected type, without inheriting the constructor's category. Current
completed packets take precedence over pending invocation metadata, even when
the bytes happen to match. Complete projected maps consume their validated
endpoint framing once. Private prospective inspection follows the canonical
invocation occurrence and the complete declared field schema; known input
fields retain their original suppliers.

Direct construction receiver framing and prospective admission share the
schema-selected apex binder. It is fixed on the symbolic registered constructor
before formal unification can identify distinct binder roles. Actual results
use their authoritative retained presentation; private future results supply
an authenticated selected schema. Projected fields remain distinct from their
complete parent construction.

Created source results retain their full public creation interface. The
unproved shortcut from a lower apex packet to the creating functor's image has
been removed: the selected creating functor executes through its ordinary
registered object-action boundary. Reuse of the already returned lower apex as
that image requires an independently retained executable creation comparison.
Diagram standardization alone does not provide it. No per-shape fallback or
new mathematical row is introduced here.

The endpoint-comparison engineering control is additive. It requires the
mapped comparisons to reuse the enclosing action's exact opaque image and
session. The thirteen candidate controls, five component-baseline controls and
baseline compilation remain guarded by exact source bytes. The baseline shares
the reviewed optional schema/validator interfaces; it is not a historical
whole-kernel build. All mathematical assertions and prior frozen controls are
unchanged. These changes have bounded source reviews and patch checks; Lean
compilation and execution remain required.

The root's ordinary-method capture and selected point-comparison demand are
separate unfinished drafts. Method result fields need their declared input
versus output roles. Prospective comparison demand and recursively scoped
semantic/actual endpoint validation remain implementation work. They must not
be replaced with a whole-result future or a global equal-JSON identity rule.
Fresh application, binder, specialized composition and prescribed-lift capture,
plus service trace re-entry, remain in the common execution work.

Candidate `de03ac04ae9bf75fd5660f4cd4cadda3a6f79e47`, run
[40526889267](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40526889267),
failed before `Realize` at the same non-partial wrapper inside the partial
`ComputationalData` block. Its failure supplies no execution evidence. The
wrapper fix and explicit full-context identity helper were already published
in `0d9a4fd858f4092399ade477c05e793a0a70b59f`; its run
[40528619206](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40528619206)
reached `Realize` and failed compiling it. The first errors were multiline
record/branch layout, reserved local identifiers, unchecked Wire-array indexing,
and callback arguments whose optional defaults concealed required parameters.
The next source corrects those errors and retains the explicit two-endpoint
condition. Bounded source review found no change to mathematical requests,
dispatch or failure policy. The candidate runner pins the corrected bytes;
compiler/purity budgets, permanent assertions and prior controls are unchanged.
The uploaded failure artifact has SHA-256
`d077c2e9445884d59bcd544a5f36e755baccf2da86a0ecd0951c4a678e60e9c1`.
No native, semantic-export, workflow or extension result follows from that run.

The preceding integrated comparison/result-role source is published as
`e35b01cebae1bdff14c4099ba315166f018f1815` (all 472 remote blobs verified),
with candidate run
[40532153871](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40532153871).
That run reached `Realize` and failed on the same layout defects plus local
names `map` and `view`, reserved by the imported language, and unchecked product
leg-template indexing. The current correction renames those locals without
changing constructors, descriptor strings or public fields, and destructures
the required two leg templates explicitly. Its uploaded failure artifact has
SHA-256 `9abbe2113451a7c244f8f74621e57182169dffbb5414beed6791a9f8e3136166`.
The first compiler-correction checkpoint is `69e2193156de6db0bfb70e11684abc90cf8d6f72`
(all 472 remote blobs verified); run
[40533778055](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40533778055)
was building when this follow-up was prepared. It predates these additional
reserved-name and template-index corrections.

The `69e2193` consumer build failed in `Realize`; its exact artifact is
`b681661cd204fd1afe8fc7280cc83a98de50df3f7eaea244b1dbaded7683ea1f`.
Checkpoint `918c32b6c985d90a8532d392fe1a0515d0920e19` corrected reserved
names and exact product-template indexing, with all 472 remote blobs verified.
Run [40536839700](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40536839700)
was still building when this update was prepared. The additional source fixes
repair the remaining callback arities, branch layout, unchecked retained-array
access and two incorrectly escaping branch returns. No budget or assertion is
changed.

`DeclaredApplication` now shares the full typed declaration matcher with its
existing `Realize` wrapper. `RoutedResultPlan` selects an ordered public result
schema on fresh declaration and receiver variables. Retained receiver/parameter
fields, newly returned fields and record assemblies remain distinct even when
their closed values coincide. Ordinary algebraic objects stay atomic; public
Arrow, refinement and Core records retain their declared fields. The existing
record assembler is shared without changing the wire encoding. A source review
caught and corrected three branch returns which would otherwise skip the final
rebuilt-action check.

These modules and the additive `RoutedResultSchemaProbes` control are now part
of the candidate build/control closure. Fourteen candidate controls, five
component-baseline controls and baseline compilation are pinned. New helper
dependencies require both absence at the published baseline and exact reviewed
current bytes; existing compatibility pairs retain their before/after guards.
The schema control uses equal endpoint values and equal packet bytes with
different owners to check the retained ambient position and field order.
It is engineering evidence to run, not a mathematical acceptance result.

Checkpoint `53028b1c43809a1a2181a205cc5b7bd13433fce6` published the pure
schema and control modules; all 475 remote blobs match the reviewed local tree.
Its run [40539209268](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40539209268)
failed in `ComputationalData`: the local pattern name `arrow` resolved to the
codec constructor. This correction uses `arrowData`, repairs the preceding
`Realize` branch continuation, and renames the control helper `opaque` to
`opaquePacket` because `opaque` is a Lean keyword. It preserves all schema
checks, assertions and budgets. The failure artifact has SHA-256
`2261ea12343fcc67d903e9ebb4fa81b82dd422fba07ec9e0330f3913c23ca5bf`.
The prior `918c32b` run also failed in `Realize`; its retained artifact is
`00549ab9f6f45db575aaac74543a685aba9f4459511aee8a97da143bee1e90d7`.
None of these failed builds supplies downstream computational or semantic evidence.

The parser correction is published at `db082f597682be5aedeeb38002240c20524de941`
with all 475 remote blobs verified. The next integrated source adds positioned
computational-interface scopes and the shared comparison reader. Exact declaration
positions retain full category dictionaries, logical parameter roles and accepted
actual Hom views, including graph-backed comparisons. Neutral new result roots
cannot gain trusted object/value bindings before their independent validation.
Record validation shares the existing codecs and representation constraints while
preserving distinct transparent parent/child roles.

Capture, private admission and actual request rebuilding now retain the original
argument template and every declaration parameter template. Private references
remain in one reader for the whole comparison/request traversal; an actual or
byte-unchanged owner no longer skips required argument/comparison demand. Nonpoint
whole maps retain their existing representation, and exact typed receipts control
whether a frame was already consumed. The additive positioned-scope control is
pinned beside the prior controls (15 candidate, 5 baseline, baseline compilation).
Two bounded source reviews found no introduced blocker in the reviewed paths;
this source integration still requires Lean and runtime verification. It does not
complete ordinary routed-method capture, positioned result reuse or all native
point transport.

Checkpoint `b314639df859c00c2276f5fa8395fb6cd8d9cbad` published the
combined comparison and positioned-interface source; all 476 remote blobs were
verified. The preceding `db082f` candidate run
[40543598724](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40543598724)
failed compiling the new pure result plan because `variables` and `variable`
are reserved Lean tokens. They are renamed to ordinary binder names. Existing
construction probes also exposed fresh category-instance synthesis while
selecting a symbolic apex: `mkProjection` now uses the symbolic constructor's
own complete parameters before formal unification. This preserves the selected
category context and apex position. Its failure artifact is
`b68fa1a7cc79cbc0cfecab44982168e8833d567856787aa7122ae0c68bb4c3f1`.
No failed build supplies downstream execution or independent semantic evidence.

The pure result plan also fixes each registered field-comparison action before
closing its distinct receiver and parameter roots. Every explicit computational
parameter retains an exact original input/public projection, or an independently
fixed portable scalar accepted by the existing codec. Missing parameter data
cannot break a mathematical tie between actions. Missing or ambiguous unused
field actions remain inert until that field needs comparison transport. The
plan records these outcomes; it does not execute a leaf or create new mathematics.
This source has an independent bounded review; computational reuse still depends
on the actual and prospective consumers under integration.

Checkpoint `fce463174b1097b32cb0d9b1690b717c111601b1` contains the
symbolic apex and positioned projection-parameter plan; all 476 remote blobs
were verified. The direct projection selector is sound for an available named
registered functor; it does not yet establish closure over composite, classifier
and constructor-induced projection routes. That remains generic implementation
work, rather than a reason to add per-field cases.

The preceding `b314639` run
[40546547645](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40546547645)
stopped in `ComputationalData`. This narrow compiler correction fixes one scoped
callback continuation, renames four reserved `scoped` locals, and gives a codec
recognition flag its intended Boolean type. Its exact failure artifact is
`2650804a7ff1a76bfa2962e5126431bf1e9b5356216e9f07efa85b367baf74d5`.
It supplies no runtime, independent-question or extension evidence. Assertions,
control counts and compiler budgets are unchanged.

Ordinary-method capture, its actual/prospective result consumers and generic
positioned field-Wire reuse are still being integrated. The shared comparison
reader and recursively scoped validators now have a combined source candidate;
full compiler and computational verification remain open. The pure result schema
alone does not complete those execution and reuse paths.

The selected dependency commits are construction integration branches. A
2026-10-27 read of upstream main found mathematical main `8782c22` diverged
from the selected `3bd4d3d` (the latter has 30 integration commits absent main),
contract main `3382e4e` 30 commits behind selected `3f7a22e`, and leaves main
`0030ccc` four commits behind the original diagnostic `2c8b904`. Do not describe
this candidate tuple as the latest-main integrated release or replace required
interfaces with the older main state. Ordinary dependency integration and the
final coherent latest-main build remain necessary before V1 delivery; source
publication does not accept that integration.


### Actual action boundaries still require implementation

The recovered successful 17-assertion workflow report contains two concrete
counterexamples to a claim that generic action execution is already complete:

- `op.rings.neg / cat.rings` receives an unexecuted
  `fun.commutative_rings.ring` action as its selected owner, both in the parameter
  array and in the complete callable descriptor.
- Reusing the finite pullback sends `pair(F,F)` to
  `lim.sets.product / cat.sets`, where `F` is the unexecuted finite-classifier
  forgetful action on the retained created cone. A later
  `meth.cardinality / cat.sets` request receives `objectProduct(F,F)`.

Those are category-wide target registrations, not registrations for an entire
source composite. The old diagnostic implementations happen to interpret those
recipes. Their successful arithmetic/cardinality answers do not establish the
shared executor boundary required by the current contract and issue #69.
Descriptors within an admitted element or selected context remain legitimate;
the repair must follow typed executable occurrences, not reject every JSON
occurrence of `functorAction`.

The current source diagnosis identifies inert operation-owner preparation and
unobserved children in `realizeLimitWith`; top-level observation alone does not
materialize a nested Arrow or diagram. Implement selected execution, retain the
actual returned packets and exact suppliers, and rebuild all affected parameter,
map and endpoint occurrences. Candidate preparation must stay inert: an
unselected candidate's absent action cannot block a different valid candidate.
Provisional admission must retain unrelated actual argument owners, and actual
execution must not select a different registration after an action or reply
fails. The new `OperationOwnerExecutionProbes` control is engineering evidence,
not a mathematical assertion or a leaf-supplied answer.

The unchanged original workflows remain a regression input. Replaying them is
separate from the primitive-action, complete defining-map, two-leaf, and frozen
extension obligations. A correct missing-action outcome is a request for the
independently implemented registered primitive, not grounds to restore recipe
interpretation in the target consumer.

Preparation must also retain *which runtime occurrences* it selected. Source
inspection found that the object and map observers reconstruct their source
through the expression-keyed cache, and their action encoders can reread
parameters there. Replacing an equal formal cache entry after preparation can
therefore substitute an actual packet or endpoint presentation. Preserve the
original typed input, ordered full actions and positioned parameter occurrences;
do not recover them by equal JSON, formal-value lookup, or broad cache removal.
In particular, the proposed global invalidation of recipe entries during owner
rebinding was rejected in review and is being replaced by explicit retained
operation arguments and owner-parameter slots.

New engineering controls distinguish these mechanisms before integration:
`ActionOccurrenceProbes` changes source, callable/endpoint and scalar-parameter
cache entries only after inert preparation; `ArrowFramingReuseProbes` preserves
an independently selected nonidentity endpoint comparison through an unchanged
Arrow map. `NestedArrowActionProbes` and `DiagramActionExecutionProbes` require
their typed children to execute at the common target boundary. None supplies a
mathematical answer. These controls are currently source fixtures, not completed
Lean runs. Retaining an outer Arrow's fields alone is insufficient: its pending
map must retain its own source and parameter occurrences too. An actual returned
whole callable must retain the endpoint packets at which its invocation was
validated, including when the reply itself is opaque.

Published checkpoint `112dc2a63a8051b240bc6286e7525bec6430a406` integrates the selected-owner
admission, explicit recipe-versus-result origin, retained `EdgeRef` action
occurrences, and callable reply-interface changes. Action capture checks its
complete formal and positioned data anchors before observing the original input
and ordered parameter occurrences. The service preparers retain the result role
and endpoints before dispatch; transparent `valueData` wrappers preserve their
exact ownership projections. Product comparisons now consume the accepted
product cones and their universal properties. The compiler and purity budgets,
mathematical assertions, and existing CI workflow are unchanged in this
checkpoint; its publication was for a coherent compilation check, not a claim
that these mechanisms or the V1 programme are complete.

Published checkpoint `9dbdd4bcb9a946266cd6b2cc3c961d02841320de`
additionally retains children of intrinsic compositions and
records, direct `ConstructionId` map plans, typed continuations for projected
action endpoints, and complete diagram occurrences through construction
dispatch. Complete callable replies and nested services retain original endpoint
Wires and their comparisons. Transparent aliases keep an original framed map as
a typed child rather than rewriting its historical frame or relaxing occurrence
identity. These integrations are not yet verified by a complete Lean build.
The additional engineering controls are preserved as separate source files.
Their guarded component-baseline runner and the expanded workflow are included
at this source freeze. No local Lean result is available for these new
changes. Existing successful workflow assertions do not close these omissions.

Candidate run `40515420488`, job `122228012508`, failed at the
`ComputationalData` function mutual block because the new endpoint-origin type
declarations were nested inside it. The next source moves those two unchanged
types before that block. This failure occurred before compiling `Realize`;
native tools, API export, fixed readings and execution did not run.
The earlier `112dc2a` run failed parsing two continued structure-field
applications in `ComputationalData`; it did not compile the new `Realize` source.
The `9dbdd4b` checkpoint contains the syntax correction. No result from that
earlier run verifies the new executor. Published `5933af3525658016651a11f1c2f6c0b82536d152` retains
prospective nested owners without erasing known suppliers and captures direct
construction and functor object actions at the same deferred boundary.
The additional `NestedOwnerAdmissionProbes` fixture checks private prospective
inspection without dispatch or live-cache mutation. Its coherent build, run
`40520161523`, job `122244754532`, failed before `Realize` at
`ComputationalData.lean:2293`: the data-only endpoint wrapper was an ordinary
definition inside the all-`partial` mutually recursive validator block. The
wrapper is now declared `partial`, preserving its body and public interface.
The uploaded artifact SHA-256 is
`8a8017bc412b79f914cd8b3427b2aadee27a41a35518e5af42c6f862bf8f4246`.
No native, API, semantic-reading or execution result follows from this run.

Published `de03ac04ae9bf75fd5660f4cd4cadda3a6f79e47` integrates one typed invocation lifecycle for registered whole
callables, complete universal constructions and their projections. The harness
keeps the canonical input, immutable occurrence identity and optional actual
result. Parameters, full category contexts, endpoint Wires, diagram inputs,
accepted creation comparisons and result schemas are fixed by producers.
Completion does not discard construction provenance: later defining maps use
that same accepted schema and actual result. Direct defining legs compile the
existing `DataProjection` algebra into retained fields, inputs, intrinsic maps
and registered actions. The public universal preparer and captured executor
share the same typed materialization/completion factory.

Scalar wrappers now retain a separate expected value type rather than an
invented object/map category. Point conversion retains its exact pending map;
the presence of a point interface no longer means computation has completed.
Changed-owner point reassembly uses producer-owned element/product inputs and
positioned encodings, without replaying the trace or replacing expression-cache
entries. Named and contextual identities share one intrinsic producer which
uses the retained category dictionary explicitly. Subsequent review found and
corrected the same dictionary-resynthesis defect in the complete callable's
identity argument: both now share `identityAtContext` and the same intrinsic
producer. Known-context identity service inputs and reflexive component
presentations use their supplied full dictionaries too. Registered generators and map
literals retain their original endpoints without inferring a map role for an
ordinary object literal.

The original WholeFunction cache-mutation controls were stale engineering
expectations. Both mutation packets are preserved and now require reuse of the
captured original occurrence. New negative companions explicitly substitute
the retained endpoint inventory or its supplier and require rejection at that
boundary. Mathematical assertions and the existing frozen action controls are
unchanged. The additive `IntrinsicValueOccurrenceProbes` exercises pending
map-to-point-to-scalar reuse with opaque ownership. The twelve controls at that checkpoint remained guarded by their exact source bytes. The combined source has
bounded source reviews but no Lean execution result; this is not V1 closure.

The remaining capture boundary includes fresh application, binder, method,
specialized composition and prescribed-lift dispatch, and `Prepared.trace`
still restarts execution through an expression cache. Prospective admission
must also consume the new invocation result interfaces. Extend the common
typed lifecycle and project only genuinely future output slots while retaining
known siblings and suppliers. A closure hiding inputs, a cache snapshot, or
whole-construction owner erasure does not supply that mechanism.

The independent reading addendum resolves exactly two source-intent
uncertainties from the pre-existing mathematical specifications at `a6311e1`:
`numbers.integers.sum` and `numbers.gcd` use integer operands and results. The
original 294-record ledger and its source snapshots remain unchanged. The
addendum SHA-256 is
`13215e41399be90367e4de456b9c097343da0f6eb70a11703ef66efec64ec417`.
No candidate export was read; the original RX08 ambiguity remains unresolved.

### Integrated compiler failure and repair

The restored source was based on published kernel
`09d52994ab08380bf88c9b0a05fc166325bd81bf`, tree
`a13671f7bd2ba5e578c5075f687dc634e54f4cff`. Candidate CI
[40390087707](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40390087707)
has already run and failed: `CasCatalogue/Realize.lean:5425` exceeds the unchanged
200000-heartbeat LCNF compiler limit. Later noncomputable messages are fallout;
the native tools, notebook and axiom audit were not reached. Do not restart the
old purity-import diagnosis or treat that failed attempt as a completed build.

The source now extracts the unchanged `realizeFresh` body into the existing
explicit-callback compilation pattern. Its recursive wrapper supplies the same
operations; no execution branch or budget changes. See
[the owning realization record](specs/reuse/cc-realizer-first.md#realization-compiler-boundary--2026-10-27).
The compiler-only candidate is published as
`f65f3e9bed748ee8bc699e16ff43d29fb8fbce79`; its coherent candidate run is
[40490647326](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40490647326).
That candidate completed on 2026-10-27. `Realize` compiles under the unchanged
200000-heartbeat compiler limit, and the remaining consumer build reaches its
gates. The build still fails: `CasGates.KernelPurity` rejects
`operationProductIso`'s direct use of `Equiv.prodCongr` from
`Mathlib.Logic.Equiv.Prod`. Native tools, the axiom audit and reader preflight did
not run. The purity gate remains unchanged; obtain the induced product
comparison from accepted mathematical construction data instead of weakening
the gate or choosing another concrete product in the kernel.

The exact failed candidate artifact is retained as
`evidence/ci/kernel-v1-candidate-f65f3e9-evidence.zip`, SHA-256
`ff6570112c75f24f7acddebfaaf6dd6615771f900d2667cfb4e2acfb2b595303`.
Its source tuple, logs and result are distinct from the subsequent action
execution work. Clearing the compiler obstruction does not establish that the
original generic mechanisms meet their mathematical and public-contract
requirements; complete execution and independent interpretation checks remain
required.

The next published candidate, `112dc2a63a8051b240bc6286e7525bec6430a406`, ran in
[40511418670](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40511418670).
Its build failed before `Realize`: `ComputationalData.lean:2258:72` reports an
unexpected parenthesis in a continued structure-field expression. The following
unknown-identifier diagnostics are downstream of that parse failure. Both
affected field applications are now parenthesized. This attempt supplies no
new `Realize`, native-tool, axiom-audit, or reader-preflight result. Its uploaded
artifact has SHA-256
`07705db0e9d60364ebbab2dc3c0d25f04b2d964593d0237baa624550956ec99c`.

The local recovery verified all 451 source blobs and reconstructed the exact
published source tree and commit. The latest recoverable saved evidence archive
is version 45; later local checkpoints are not present. In particular its two
RX-LIFT factor-sample records lack nonempty canonical questions. Preserve the
original fixed questions and independently assess fresh complete readings; do
not generate a historical reference from candidate output or claim the missing
byte comparison ran.

### Closed source repairs ready for the coherent build

Whole-function commit `9bc2baf64339ed770f48991450b7a462756ba917` is
three-way integrated with the product, complete-object, composition and reader
repairs. Every added and removed production-source line matches the closed
component patch; the independent changes are retained. The exact passing whole-
function fixture joins the existing engineering aggregate. See
[the closed integration review](specs/reviews/whole-function-inputs-20261027.md).
Both compiler stages, the focused control and five unchanged controls passed,
with every source/input/artifact guard stable. No Lean process or component
guard remains active at this source checkpoint.

The next dependency is a corrected published, coherent 57-target build with mathematics
`3bd4d3d` and current contract `3f7a22e`. Run the exact two original reader
cases on that built combination before API export. Then publish the fresh API,
pin its contract revision, publish/build that final tuple, and rerun the fixed
execution, notebook, public primitive, two-leaf and complete pure-reading
consumers. Source integration and isolated controls do not establish those
final results or independent mathematical acceptance.

### Measured reader repair integrated

The complete source of clean reader commit
`3e27780bfbacd293996094cea49b5cd06582f344` is integrated without source changes.
Its new closed/open route control joins the existing kernel aggregate.
Within one transport call, a successful route trial may retain its actual
closed image and complete ordered edge applications; the original final
type checks, comparison classification and trace recording still run.
Open terms use the original construction. No cross-call cache or trace
precondition changes. See [the owning reader record](specs/reuse/cc-dsl-language.md).

The earlier isolated records report passing compilation, seven unchanged
protected controls and the additive control with stable guards. Both original
RX-LIFT factor samples reached the existing `mor.sets.tuple_cons` implementation
gap with no dispatch. The claimed historical byte comparison cannot be recovered
from the saved archive; its available canonical-question fields are empty. Do not
count that comparison as verified. The isolated timings were approximately
198281 and 198788 of the unchanged
200000-heartbeat limit. This tight margin requires the exact two-case preflight
on the combined built source before public API export; the final original
26-question execution remains required. The isolated results do not establish
the final combined tuple. Whole-function source closure is now integrated as
described above; the coherent build and final consumers remain required.

### Complete module comparison diagnosis

The additive handwritten module fixture's failure is now explained by its
original input: the open receiver has type `ModuleCat.{?u,0} ℚ`, with one
unresolved module universe. The comparison retains that same universe ID and
has no residual term metavariable. Complete-category reconstruction independently
rejects this incomplete input. Separate closed and open `ModuleCat.{0} ℚ`
receivers retain the full supplied category and produce closed comparisons.
The unchanged-source diagnostic passed in 6.971 seconds with stable guards;
its full expressions and provenance are preserved in
`module-comparison-baseline-diagnosis-v3.json`, SHA-256
`d18734ddac7485a46d66c8fdaa3a8bb4861cc15d45178913ae58c84eb3aa7683`.
No universe default was assigned to the original input. This closes the
previously recorded uncertainty without changing an accepted comparison.

### Complete operation product presentations and real workflow reuse

The exact reviewed V21 source is integrated from clean local
`1e9a5c1c2e54decb0a0281e390154d63d18643eb`, based on `5e948913`.
Original complete endpoint occurrences, ordered product contexts, actual
comparison directions, scoped suppliers and dependency provenance survive
operation preparation. An independently chosen computational presentation is
consumed from its validated occurrence; it is not reconstructed by rereading
the formal Hom endpoints. See
[the owning reuse record](specs/reuse/operation-point-presentations.md).

All ten isolated stages passed with unchanged guards, including the original
four-registration primitive observer and all 17 original connected workflow
assertions across 73 engine dispatches. The primitive observer executed
`fun.rings.semiring`, `op.monoids.mul` and `mor.sets.equality`; both accepted
dependency derivations completed without a direct ring-multiplication dispatch.
The exact passing product control is part of the existing kernel aggregate.
These runs identify the old native base with V21, mathematics `ac9bb80` and
contract `3f7a22e`; they are not final combined-tuple results. The source merged
cleanly with the separately validated composition and complete-object changes;
the two JOURNAL entries were retained verbatim. Whole-function and measured
reader repairs are now integrated. The coherent build/API and fresh full
validation remain.

### Complete original objects and published module products

The generic complete-object repair is integrated after five closed passing runs,
including the actual new upstream module product at two different complete ring
structures on one carrier. Named and universal recovery retain every selected
parameter and the original complete object; unresolved parameters and competing
presentations remain failures. Already computed packets and suppliers retain
priority. See [the closed source review](specs/reviews/complete-object-parameters-20261027.md).
The mathematics pin is now the freshly fetched public product revision
`3bd4d3d9695f288749c860368174462c4d689b7c`. The native producer and active
dependency artifacts remain unchanged until all running guards close. This is
source integration; final tuple/API/build/execution and independent acceptance
remain pending.

### Integrated complete-owner reader repair

Published composition checkpoint `7d3589234b25b79636c809bf8c3ebec24c905310`
is full-tree equal to local `da9801c`. The next source increment integrates
Language V3 and its exact focused ambiguity control. All 13 original RX05 and
17 original F9 questions now read, in original order and at original budgets;
the original dependent-reader and numeral controls pass. All seven closed runs
have stable guards. See [the selected-owner review](specs/reviews/selected-owner-reading-20261027.md).
This does not claim computational success or replace the final independent
interpretation review. Whole-function/admission handling and the measured
RX-LIFT reading cost remain under active engineering work. Product and complete
module source repairs are integrated as described above; the frozen native
producer remains 8f until every active guard closes.

### Owner action: trusted review input retrieval

The exact minimal correction is prepared and published as draft
[PR 70](https://github.com/dzackgarza/lean-cas-dsl/pull/70), head
`6d25e260fc718c273f9a3cbd55df7a511b09d495`, based on main
`95de265e5a6d61909703a3193f0a1c952e12131f`. It changes only the trusted fetch's
`--update-shallow` option and adds a depth-one/stale-SHA regression test; both
current-main retrieval tests pass. Its fetched full tree is
`e5574a94fec5f64d383a5c1f7de0471a34a06bd5`. The appropriate independent
maintainer must review and install this trusted-source correction before the
trusted review can consume it. The author has not installed its own judge or
changed main. The latest 897 review run `40385505483`, job `121792579582`,
again stopped before any verdict:
`REVIEW NOT COMPLETED (inputs unavailable)` at the private base
`FETCH_HEAD^{commit}` lookup. There was no verdict artifact. Main and PR 70
were checked again and remain unchanged/open respectively. Unaffected kernel
construction and validation continue.


### Integrated composition context repair

Finite-graph repair `c6c66aefc294fcced75e5ea273f1a6c492d9c112` is published and
freshly fetched with exact full-tree equality to local `a88f5aa`. The next source
increment carries the independently recorded full category through composition
framing. Its compile and two unchanged control groups pass; the original complete
14-ID RX03 file retains identical pure questions. Its two previous internal errors
now reach the declared callable boundary. Outcomes remain 11 gap and 3 unavailable;
no all-question computational success is claimed. The closed evidence and scope
are recorded in [the composition review](specs/reviews/composition-context-20261026.md).
The frozen native producer remains 8f. Language and product-presentation repairs,
final publication, full build/API and final fixed executions are still pending.

### Newly integrated finite-graph source repair

The latest published checkpoint is `cb1688b9bd9f6400be9fccab440619e4619e2d2a`,
which includes the reviewed main merge. The source now additionally repairs the
released explicit `finiteGraph` inventory path in both endpoint validators.
Actual descriptor parameters determine its data shape; retained formal-apex
associations cannot replace those parameters or supply point inventories.
Known inventories, complete graph coverage, scalar constraints and all original
codomain checks remain in force. See
[the bounded source and validation record](specs/reviews/finite-graph-inventory-20261026.md).

The repair compiled and passed its additive inventory controls and three unchanged
original framing/control modules, with all guards stable. These are isolated
engineering results. The shared native producer remains the configured 8f build;
no active run consumes a silently changed source or compiled closure. The combined
producer still requires the complete 57-target build, current API publication,
fresh fixed executions and final independent pure interpretation comparison.

The 8f GitHub candidate run `40348409967` has now completed successfully, including
all consumer and native builds, the existing axiom audit, and final source stability.
The cb1688b trusted review again stopped before a verdict: run `40361244876` reports
`REVIEW NOT COMPLETED (inputs unavailable)` at the trusted private base's
`FETCH_HEAD^{commit}` lookup. No independent authority result is inferred from CI.

### Latest integrated preparation and closed interim evidence

Published kernel `8f454d6b56445eb3fb22c28aa281de973b9be4b7`, tree
`a6f6f3569c1b6386c9ee5a4a158ac2ed27dc2eb8`, is tree-identical to local
`5e948913`. Its selected native build passed 7,801 jobs in 595.442 seconds
with unchanged sources. That first launcher had an environment-source-path
error; the complete same target selection was then rerun under the configured
engine environment and passed in 13.385 seconds. Only the configured receipt
was selected for subsequent exports. This selection does not cover every
explicit CI consumer target: the next combined build uses the exact union of
51 current CI consumer targets and six native/notebook targets.

This closes the native check of the preceding actual-point refinement repair.
It validates fixed data fields of actual endpoint points without reconstructing
reference membership proofs, while nested scalar literal constraints and
ordinary finite-set uniqueness remain checked. The earlier 7462a36 failed build,
all diagnostic attempts and the independently reviewed focused controls remain
preserved. No original assertion, answer, import scope or budget changed.

The complete pure permanent export on configured 8f passed in 450.425 seconds:
all 153 fixed IDs, exactly once, across the original 17 files, with zero unreadable
IDs or diagnostics and unchanged sources, inputs and selected artifacts. The
separate complete preceding-binding/context export passed in 60.062 seconds,
retaining 48 bindings, 12,292 typed occurrences, 1,442 operation records and
568 registry rows. A failed helper launch used the wrong monad lift; the
mechanically corrected, versioned helper retained every observation field.
An independent reviewer has now compared every ID and all 48 bindings using
only normative mathematics, complete pure readings/contexts, format definitions
and typed administrative declarations. The frozen interim report finds no
mathematical meaning defect or remaining pure-input gap. Its main assessment
has SHA-256 `6b85d2a79db0d8015180d273e3e1ba9d4fab1ba58c4501d6b691a22ced23f68b`;
the complete per-ID record is `0d04bc53fe87d56250933653767cd8948f8fe9045c6f420b8f78538bb25d8968`.
The finding concerns the supplied pure meanings, with omitted proof-body and
exporter-faithfulness limits. It is not an execution/availability or acceptance
verdict, and does not transfer automatically to a later producer.

This checkpoint incorporates upstream main
`95de265e5a6d61909703a3193f0a1c952e12131f`,
retaining its zero-family rigid-target guard together with the candidate's full
selected-owner, ambiguity, nullary, dependent-parameter and callable-address
logic. Independent source review found the focused resolution correct. Its
isolated Language compile passed in 98.860 seconds and the unchanged original
dependent-reader control passed in 97.053 seconds, with source and frozen
artifact guards intact. Remote publication retains main as an additional
parent; a resolved tree alone would not record the merge. The combined source
still requires its own full build; the interim 8f build is not relabeled.

The public-only primitive leaf remains frozen at
`a68a52e24d54da21aacc0c4f96ed0160d61ae1d3`, tree
`d244727a4a1434a65618ae9173bb906823784b42`. Its four registrations and fixed
observer are unchanged. The earlier ba3/Mac9/C3f7 trial retained the actual
monoid but exposed inconsistent outer and nested endpoint presentations; the
leaf correctly refused the whole-callable mismatch. A declaration-relative
kernel repair compiles in isolation. The V8 trial passed the former recipe
framing boundary but rejected product inputs whose components retained route
history without a current comparison action. Closed diagnostics distinguished
that history from `objectIso` and `endpointPresentation`; neither current
comparison field was present in the fixed primitive specimen.

The isolated V9 history-retention increment, source SHA-256
`cc90792c45aeeb82dbb4c4b75684a9744a67805b771a4ce69090b9d0e73ccdad`,
compiled in 59.235 seconds. Its unchanged primitive observer then passed in
8.672 seconds with all guards stable. Actual dispatches were the semiring
action, monoid multiplication and set equality; the ring multiplication and
multiplicative-monoid computations used the registered proved derivations.
The complete supplied monoid, its actual packet and every opaque supplier
remain recorded. This is an isolated specimen result, not a published or
final-tuple acceptance result.

Independent source review found a remaining V9 context-identity omission:
equal aggregate product packets can have different ordered child histories,
but service selection does not compare those histories when they survive only
as dependency handles. The review records a concrete source-level call path,
not an executed wrong-answer observation. Publication of this increment is
held while exact product context selection and actual current product
comparison actions are completed. The report has SHA-256
`f05423801d347526be2f71ff8f89803ba910001da9dd0af5d8725d16e8bf928b`.
Failed attempts and all observations are preserved. No outcome or kernel
implementation was disclosed to the public-only author.

The independent reviewer has also frozen the normative comparison matrix for
all 134 positive extension questions, with 169 mathematical declaration
references. Its SHA-256 is
`ba68abc523f54d2751d0dbe1609752cf25ac10abff3baeef7b1bf42780ddf9ed`.
Every candidate extension-interpretation verdict remains pending until the
fresh complete pure package is supplied.

The original connected notebook has now actually executed on the clean,
configured 8f producer in 107.511 seconds. Its single code cell executed with
zero error outputs, all 17 assertions held, and the existing strict checker
recorded 73 dispatches across the four original workflows. Source, input and
artifact guards remained stable. The executed notebook has SHA-256
`3370be703ac9f9fa7ff2316a2f8ed74ef5b548689107b91a18bed76205f3c215`;
the raw computational report is
`d91fb63c8e42f56151999efcb6a7a784aa49c4f9880075f818ef8866c083fccf`.
Only external execution paths were adapted; no notebook feature or example
expectation changed. It will be rerun on the final combination.

A separate interim run of the unchanged 17-question F9 extension group closed
in 33.149 seconds with all guards stable. Every fixed ID is present, but none
held: four reader ambiguities, two malformed graph replies, three unavailable
leaf evaluations and eight implementation gaps were reported. These remain
failed observations. Engineering diagnosis identifies an ordinary F9 element
decoder omission in the leaf's complete-owner handling; the finite-graph
public-contract boundary and the numeric-left reader ambiguity require
separate diagnosis. No answer, source question, import or budget was changed,
and the kernel must not discard selected owners to satisfy a leaf decoder.

The remaining 134 pure readings and their independent complete meaning review,
the complete final 134-question execution, RX controls, two-leaf consumer,
connected workflows, executed notebook and fresh API publication still require
the combined final published and built tuple. Interim results do not transfer
to that producer. Prepared commands without a closed result are not evidence.

Evidence checkpoint 49 is frozen locally at 159,483,042 bytes, SHA-256
`551aa5aea7160eb80e4e0dba5e411a8e332a978ebf0d92ed300781df1855afd9`.
It retains all 4,126 preceding non-index entries byte-for-byte and adds 255
closed entries, including V8/V9 diagnostics, the independent permanent
assessment and extension preparation, the notebook and failed F9 execution.
All 305 selected files were verified. Exact checkpoints 48, 47 and blocked 46
ZIPs are separately retained. Later active source, execution and review
records remain excluded and require a subsequent append-only checkpoint.
Version 45 remains the last confirmed durable save.
Two automatic approval reviews blocked the previous concrete upload before
execution. No alternate upload or further retry is attempted without the
required explicit approval; all unaffected implementation work continues.

### Earlier repair evidence (retained history)

The preceding published kernel is `e4a1fd065f038e7c02c6cebedbb8d00746b2e92b`,
tree `83d01175a78909b1965ca49d68cb433a38f82694`, on
`work/kernel-v1-20261023`, tree-identical to local `b18eb094`. Its complete
native build passed all 7,797 jobs in 918.449 seconds with unchanged sources,
including the gates, language, realizer, test suite, question exporter, native
tools, notebook worker and all six selected mathematical imports. This is a
build result; the frozen computation and complete interpretation review remain
separate. The older `72d10e3` and `9af2a50` failures and all interrupted/environment
records remain preserved.

Independent diagnosis isolated the purity crash to loading the truncated private
part, before any gate judgment. Its header pointed beyond EOF; the other 66
selected private parts had valid ranges. Only the damaged part, its hash and
module trace were invalidated, preserving lossless originals. Ordinary Lake
regenerated Language from unchanged source in 104.324 seconds. No purity rule,
import, assertion or budget changed.

This source repairs a further opaque-composite record failure exposed by adapting
the original engineering caller to the validated executor's required receiver.
Atomic scalar schemas remain atomic; composite schemas retain actual constructor
slots. Plain composite data reach the literal decoder only when wholly inline.
The original Nat × (Nat × Nat) packets, equal bytes with distinct suppliers,
ULift controls and all assertions remain. The isolated record, literal/callable
and explicit-codec controls pass in 3.234, 8.161 and 4.403 seconds. The complete
e4 native build subsequently passed those original controls too.

A separate source audit then found an older recursive scalar validation gap:
inline rational data inside finite graphs reached their field-shape checks but
not their complete literal constraints. On the unchanged e4 native build, six
malformed graph/list/nested-graph cases were accepted in a thirteen-case diagnostic.
This source retains each scalar subtree's independently fixed complete type and
applies the existing literal decoder only when that subtree is wholly inline.
Opaque whole values and opaque fields keep the existing data-only path; graph
and actual-key schemas cannot acquire the scalar wrapper. No new public wire
form, mathematical rule or proof from an opaque value is introduced. The exact
thirteen cases now pass in 3.242 seconds; the unchanged original record and
literal/callable controls pass in 3.063 and 7.863 seconds. The new engineering
probe is added without changing existing assertions. Independent read-only
source review found no blocking boundary issue. This subsequent source needs
its own complete native build and final frozen executions.

This source also incorporates the complete declared numeral-owner repair,
completed-point metadata forwarding, and the direct and nested record-codec
corrections. Each structural step retains its existing field declaration and
codec at the independently fixed full receiver. Exact Core and Arrow fields
keep their supplying occurrences. Whole descriptors and opaque records cannot
be mistaken for ordered fields; assembled Core and Arrow results retain their
existing envelopes. The selected output still requires its original interface.
No new mathematical row, wire tag, evaluator or interpretation priority exists.

Original reuse, transport, derived-action and service-projection controls now
pass without changes to their assertions. The added nested controls also pass,
including Core(Core(Type)), opaque inner records, refined Arrow projection,
identical endpoint bytes with different suppliers, and Core construction around
an actual opaque field. Independent read-only review closes the direct and nested
record findings at frozen `7045feb`; the committed and separate exact-field and
assembly controls pass in 5.199 and 4.761 seconds with all 1,046 copied artifacts
unchanged. This bounded engineering review is distinct from whole-candidate
acceptance.

Created-apex projection now distinguishes a successful checked base image from
an ordinary computational receiver. The receiver keeps its exact original
formal occurrence and actual data suppliers. Only the exact selected creating
action consumes the checked image, and failed extraction cannot be reused as a
completed image. The unchanged anonymous-apex, full-context and transport
controls pass in 3.774, 3.780 and 9.455 seconds. Independent source review of
`ba3b7a6` found no blocking defect in this separation. Earlier compile and runner
configuration failures remain in the evidence records.

The reader reuses only fully closed actual comparison evidence within one claim,
keyed by the complete supplied source and ordered witness array. Every target
trial, full route search, coherence classification, selected-action check and
trace operation remains in place. The three original RX-LIFT readings at lines
22, 73 and 76 complete all seven pure-export stages with the original full scope,
six imports and ordinary 200000 option. The counters include subsequent export
work and are not all below that option; no timeout occurs. Controls cover full
context distinctions, trace rollback/retry, unresolved-target ambiguity, and
refusal to cache evidence containing a local class hypothesis. Complete parameter
collection also retains the original registered declaration identity instead of
adding an anonymous copy of the same named parameter. All original witnesses
remain present; independently supplied competing owners remain ambiguous. The
full original dependent-reader probe now passes in 107.057 seconds, along with
all original parameter, selected-carrier, context and numeral-owner controls.
The three RX-LIFT readings and three composed consumers pass again on this final
reader source with unchanged budgets and complete scope.

The original four connected real-engine workflows have a closed isolated run:
17/17 assertions hold with 73 dispatches in 155.424 seconds (arithmetic 8,
finite construction/reuse 2, matrix 3, presentation 4). The exact assertions,
source/artifact hashes and failed earlier prototypes are retained. The complete
final tuple and executed notebook still require their own run.

The selected mathematics is
`ac9bb80be1e55c43f4104d4fe8486e7715ea7cc5`, tree
`ec0fc569dee02b4cdb72c68c6dcb35a802fda8db`, and contract source is
`3f7a22e0b6afc3e745f3aa60a9ceecf6740948d5`, tree
`3f1b3a79e1fada93c4d69557d0f9876f075dc2e4`. Both were published, fetched and
compared by complete tree. The mathematics includes the independently reviewed
comparison-direction/import-scope correction and Monic admission normalization.
Original Monic binding and three observations read at unchanged budgets.
Ordinary Lean declaration checking, not Evidence.establish alone, checks the
resulting proofs. Those reviews do not accept all candidate interpretations.

The public primitive leaf is published at
`e855951e557080ac744763e917262047f6e3326b`, tree
`be34476fac2c500155294e58a374996973b23b49`, with the same four registrations:
two object actions, monoid multiplication and Set equality. Its public-only
codec increment retains exact producing requests, selected parameters, point
fragments and native field operands while keeping whole-callable endpoints
strict. All V1/extension manifests remain unchanged. Publication was fetched
and compared by complete tree to clean author `bdcbd611`; a detached execution
checkout is frozen separately. The earlier `3176e43` and e855 actual trials'
complete callable-target mismatch remain failed results; e855 completed in
13.424 seconds with two dispatches and no equality observation. A later clean
public-only author source `939dea0e50e4d7f2d84f20414b14e7fe38b9d0f9` is prepared
for publication and a new frozen trial. Its own controls carry no acceptance weight. The
author accessed only its source, released contract/API and supplied engine.

### Fixed evidence and remaining completion work

All 17 permanent files retain their recorded hashes and 153 questions; all 14
extension files retain 134 positive questions. Historical baseline exports read 146/153
and 131/134 respectively. The configured 8f permanent export now reads all
153/153; the extension repairs retain their focused evidence pending the fresh
134 export. Complete exports at the final producer and independent assessment
of every typed meaning remain mandatory. No assertion, expected answer, import
inventory or heartbeat budget has been weakened. Genuine competing supplied
owners and paths must remain ambiguous in either order.

The current evidence archive is version 45 of
`libfile_94b086b3c1308191b67e0c34e0d4c364`, 79,250,338 bytes, SHA-256
`cb4b501dbe4bed8f7a10d86946892a69a8e585af0bb92b4e12b0db0a2b7d5d06`.
Every previous member was preserved byte-for-byte. Newer closed native, reader,
record, workflow and independent review records must be appended without
replacing failed results. Runtime remains Lean 4.33.0, the recorded 14 packages,
PassageMath 10.8.13, GAP 4.16.1 and the restored notebook environment in the Pro
cloud container. No rack build is used.

The locally assembled checkpoint 46 retains every prior entry and has SHA-256
`c08427e27a77d5a7636743aa1eb4ca6a4c2f726888077e42b2af2fbe8f8093ef`,
86,681,632 bytes. Automatic approval review blocked its guarded replacement of
version 45 before upload, including after checking the original preservation
instruction and native destination. It requires explicit user authorization for
that concrete payload and replacement; no alternate transfer was attempted.
Version 45 remains the last confirmed saved checkpoint. Later closed records
must also be retained before any final evidence delivery.

The shallow exact-source retrieval repair is integrated as `077c9ce`. It preserves
all expected-SHA and no-execution extraction protections. Existing controls and
real depth-one positive/moved-reference negative controls pass, with independent
source review. Publishing construction source does not install a replacement
judge. The independent CI review at `72d10e3` still has no verdict: its trusted base
`6e67b1e` runs the older materializer without the published shallow-root fix.
A source-only depth-one fixture reproduces the empty FETCH_HEAD failure and
confirms that the already published repair preserves the exact selected source.
The 8f review, run `40348415982`, job `121661516365`, likewise reports
`REVIEW NOT COMPLETED (inputs unavailable)` at trusted main `95de265`:
its private base `FETCH_HEAD^{commit}` lookup exits 128, and no verdict artifact
is produced. Exact candidate retrieval and chain checkout succeeded beforehand.
No trusted deployment, reviewer or approval was replaced.

The complete 153/134 assertion exporters, unchanged binding control, RX05/RX09
and RX10 commands are prepared. Additive pure companion drivers retain every
successful binding's full public Value/context and typed Expr table, exact
source scopes and operation snapshots. Their definitions-only helper now
typechecks in 4.294 seconds on the unchanged e4 build. Compiler-directed scope,
list-type and grouping repairs preserve every encoded field and handler body;
all fixed source inputs remain unchanged. The 8f permanent assertion and complete context exports have now passed;
the remaining stages are deferred to the combined final producer. Counts alone
do not satisfy the independent typed-meaning review.

Publish this coherent source and build it before exporting the public API. Publish that unchanged export as an artifact
with its actual producer; then select the artifact-bearing contract and record
that its code is unchanged. The final build explicitly includes CasGates,
CasCatalogue.TestSuite, all native tools/axiom checks, notebook worker, and the
six fixed imports. Run all fixed computation, RX05/RX09/RX10 and binding controls,
153/134 complete typed exports, independent full meaning review, the original
17 connected assertions and notebook, and the frozen public-only primitive trial.
No advertised generic interface defect may be deferred as an absent leaf.

The following dated checkpoints preserve historical requirements and producer
observations. Their earlier statuses do not supersede this current section.

### Latest owner steering: constructor-centric computational service

The later attachments `Pasted text(20261025-193945).txt` and
`Pasted text(20261025-200835).txt` clarify and extend the active computational
requirement. A leaf must be able to invoke any published constructor or computation
through the kernel, without selecting its supplier or depending on its installation.
Callbacks or typed deferred requests are permitted implementation choices. The
shared executor owns their admission, composition and actual results. A producer
can construct its target image through an existing target-category constructor,
retaining the selected comparison and coherent morphism action, rather than
requiring another implementation to interpret private source representations.

Optional lateral leaf imports and shared private code are permitted and have no
semantic standing. The one-way restriction concerns mathematical authority and
evidence, not runtime call direction. The frozen-target diagnostic below tests
the absence of a required implementation dependency; it is not a ban on imports
and does not discharge the broader service requirement. Existing single-owner
payloads and isolated request/reply serving do not yet supply that service.
The architectural owning documents now record this explicit clarification.

Closed shared-action checkpoints `766b268` and `25d00a0` are integrated here,
including actual object images, whole maps, exact image endpoints and returned
ownership. Their clean author builds and guarded process controls pass; final
combined execution remains separate. Complete reader cache/context checkpoints
`cc563705` and `237666f` are also integrated. The first full pairing now reads in
152825 heartbeats at the unchanged limit; later final/factor readings remain open.
The independent public module action specimen is published as `2f352448` on the
leaf work branch, preserving all original source and manifests. It has public
interface checks only, no mathematical or two-leaf acceptance claim.

The intermediate RX05 independent review at `841091d` assesses all 13 readings:
12 match and one remains qualified. The formerly missing complete comparison
context is retained; the fixed designated multiplicative source still differs
from the protected directed-chain representative U3. Neither requirement was
changed. The current narrow schema documentation is supplied separately without
rewriting the assessed payload or historical receipt.

### Current owner steering: executable functor-action isolation

The owner supplied `Pasted text(20261025-190504).txt` during this continuation.
The remaining computational transport work now prioritizes a shared executor for
the already registered object and morphism actions, including deferred materialization,
retained images, complete defining maps and actual session ownership. An unrelated
operation on the target category must receive its declared computational form;
it must not learn a new source category, source functor or private representation
tag. Reuse the existing action registration/port machinery and the Sage/CAP and
sage-categories prior art. A contract extension requires an actual missing primitive.
Do not duplicate the mathematical categorical machinery or treat category-specific
consumer wrapper repairs as independent kernel features.

The decisive integration is a frozen two-leaf experiment: source leaf A supplies
only the newly selected category's primitive actions, while target leaf B remains
byte-identical. Execute object images, a complete mapped morphism, composition and
the defining map of a constructed result through the same boundary. Preserve formal
meaning under wrong/malformed replacement actions and report an explicit gap for
an unavailable cross-process representation bridge. The attached architectural
assessment is direction for this work, not evidence that its source claims have
already been verified against the final candidate. Reader/admission/identity repairs
and all earlier fixed MVP obligations remain active.

### Latest checked continuation checkpoints

The published `d7cfafccefb069c92cca1b04030fcbfd81ef43c9` tree integrates the
complete construction, proof-source and declared-context repairs below. Its
selected native consumer build passed in 423.334 seconds with unchanged sources,
including Language, Realize, question tools, original endpoint/parameter controls,
cas-harness, the notebook worker and all six fixed mathematical imports. This is
not a replacement for the final full aggregate build.

The four original workflows and actual notebook were then run against the public
leaf `865df49ad0b0b133d5bcfd282f380aa213eb5fff`. Both finite-pullback assertions
hold; arithmetic/matrix requests stop at complete callable endpoint checks and
presentation transport reports competing complete object presentations. A read-only
trace preserves the cause: an outer integer-set endpoint contains an element whose
actual target is still a deferred functorAction. The unchanged RX10 controls also
stop at complete scalar-target checks in holds/wrong conditions. All guards remain
unchanged. These failures are preserved and do not close the execution obligations.

This source retains every already-validated method/property route comparison in
the trace, complete snapshot and independent question comparator. Execution checks
those original contexts and typed terms before dispatch. The corrected source at
`0300c4aebb81adcf6df139f0da9f627ae72e2f10` passes its scoped consumers, new
missing/changed-context/changed-term controls, unchanged resolution controls and
purity targets. The first probe syntax failure and a later mistyped-target invocation
remain failed records. The directed route-selection algorithm is unchanged; the
independent RX05 designated-source qualification is not declared resolved.

Reader checkpoint `15ee9264a4b0d6dea591b97eb192a6ae3b0c9a27` is also integrated.
It reuses fully closed bound readings and retains the already selected full
member-family target. Its unchanged first-pairing binding and complete production
question read in 144910 and 172662 heartbeats at the original 200000 limit. The
focused endpoint/context and purity controls pass. Later factor/final-pairing
questions remain assigned work. The combined source needs its own build.

The minimal general functor-map contract is published as
`b805eda94aec95a7962da486c8eaeec14d34f2b2`, tree
`d87ca1ed7e18cf81373ba835a8a1e54c926f6236`. Its library, audit, framing controls
and declaration-export adapter pass. It reuses existing wire forms and derives
`#map`/`#input` addresses; compatible admission export and the final exact-built API
inventory are still pending. Existing target consumer sage-set-limits and its
90d contract dependency were frozen before a separate public-only source-action
leaf author started. Shared action execution, actual endpoint images, construction
maps and the two-leaf isolation run remain active work.

### Existing producer evidence

The last completely built implementation is `cedfad6664a2301b7b360e17055523a47e479bd5`,
tree `15cb779812f162e16f21e452bcb7eaa3403832e3`, fetched back and compared as a
complete tree. Named-object recovery was subsequently published as
`825fa63f8fb40b1b88f73c6d7f6bf61c4407d3ae`, tree
`df3cd29437c5342c7a0309b6c375d67d5d2e90d6`. Its combined build failed after
343.644 seconds: the original ObjectPresentationProbes exposed loss of an opaque
selected ambient endpoint, and disk exhaustion corrupted several generated
artifacts. The failure record is retained. Superseded generated linker temporaries
were removed only after confirming that no process held them open; the installed
Sage and GAP engines still load. The endpoint regression is repaired in this
checkpoint against the unchanged probe. Historical producers below are not relabeled.

This checkpoint also integrates the exact-proof-source identity repair from
`e2aadb0aecb10f0077de984e6ec4fe585707c655`. Exact Lean syntax now compares
reflexively within a complete source context, without erasing propositions,
lexical scopes, or Type-valued data. The focused controls, selected-carrier,
exporter and purity build passed in 59.861 seconds at that author source. The
original RX05 file then exported all 13 complete questions in 14.865 seconds with
zero diagnostics and the unchanged 200000-heartbeat per-statement budget.
The integrated source still requires its own successful build and fixed reruns.

The subsequent reader checkpoint `72ed3e14dd5350d45db9664a0b19c5a5860363b1`
retains the original complete point at a constrained data field and exposes every
field of a full selected family structure before comparing its receiver. The
original lifted-point admission and first nonidentity-coordinate question now read
within the ordinary budget. The later pairing/factor readings still time out;
normal-budget interpretation performance remains active work.

Retained construction/action prefixes and unique complete literal construction
recovery are integrated from `0122f7fb6b4ecb377461fd653bad81d38395f511` and
`361ae61d37f541b2bf0da335eaf751c6fce13151`. The complete supplied functor type,
value, category dictionary and ordered arguments select the action, never equality
at one receiver. Actual computed callables retain their opaque selected endpoints.
The matching clean author build passed in 10.506 seconds with Language, Realize,
TestSuite, both unchanged endpoint/parameter regressions, all focused recovery
controls and all six fixed mathematical imports. The integration differs from
that checked source only in JOURNAL.md and this handoff; native/fixed execution
still requires a newly verified producer.

The unchanged first RX03 assertion at `361ae61` then closed in 31.437 seconds
against the original public leaf `51e`: its generic automorphism-object recovery
failure is gone. The actual construction returns an opaque object and the next
request retains that exact packet and live owner. Two dispatches reach the ordinary
absent routine mor.groups.automorphism_backward. The complete question and
proposition are unchanged from the earlier exports; every source/artifact/input
guard remained stable. This is one focused execution, not the full RX03 trial.

The complete consumer build at `cedfad6` passed in 731.420 seconds with every
selected source unchanged. It includes the original RegisteredMapAdmissionProbes,
the new declared-parameter and callable-coordinate controls, the kernel aggregate,
purity gates, language/tools and all six fixed mathematical imports. The subsequent
native build passed in 34.965 seconds at the same unchanged source tuple. It builds
cas-registry-export, cas-axiom-audit, cas-harness, cas-question-export, nbdsl_worker,
CasDsl.Notebook and the fixed suite/imports. These are build results, not mathematical
acceptance or completion of the remaining execution obligations.

The published implementation retains the earlier inclusion/carrier, typed binding,
reader reuse, literal owned action and completed-lift parameter/source-context work.
Its most recent integrated repairs preserve exact scoped file bindings, exclude
macro-scoped syntax from the printed-source cache, recover actual projected point
endpoints, and frame symbolic callable coordinates using the existing typedMap form.
The unchanged admission probe and the focused endpoint, product, context and purity
controls pass. No protected question, expected answer, registry row or resource
budget was changed. The earlier full build failure at `7c87f0c` is retained separately.

Complete named-object recovery now shares the existing parameter-presentation
selection with execution. It checks the full object type and value, keeps literal
ordered parameters, preserves actual cached packets and owners, and gives retained
action provenance priority. Separate callables at the same exact named coordinate
therefore retain a common endpoint descriptor. CompleteNamedDataProbes, existing
reduced-action controls and the matching scoped consumers pass at the author source.
The unchanged first arithmetic question confirms that the conflicting endpoint
wrappers are repaired; its later adapter scalar-owner mismatch is retained as a
separate failed intermediate result. The complete typed question is unchanged.

At `7c87f0c310a4ee70de8cd908d54bf4ab992406dd`, all 153 permanent readings exported
with unchanged source, artifact and input guards. Independent assessment has now
matched every complete reading to its required mathematics. Of the full encodings,
135 are unchanged from the earlier assessed export; 18 were assessed explicitly:
11 parameter-comparison proof propositions, five Type-valued inverse witnesses,
and two containments retaining their canonical inclusion maps and ordered composites.
The inverse witnesses were assessed using their exact types and subsingleton result,
not discarded as proposition proofs. The assessment supplies no computational,
admission, migration or release verdict. A final producer export and review remain
required after the active generic repairs.

The complete 134-question extension export at `7c87f0c` closed in 1541.279 seconds:
124 complete readings and ten unreadable IDs. The missing readings involve a lifted
point's selected carrier, complete receiver selection and deterministic 200000-
heartbeat failures in lifted-factor/pairing and additive-map interpretation. All
original inputs, diagnostics and producer guards are preserved. The general suite
executed all 113 fixed IDs in one shared harness, closing in 1577.866 seconds with
10 holds, 86 gaps, 12 internal failures and five unavailable outcomes; three binding
failures are separately retained. No IDs were dropped or duplicated. These results
do not close the kernel: required generic representability and interpretation defects
remain active repair work. Missing ordinary leaf registrations are tracked separately.

Independent mathematical review of that exact 134-row export is now complete:
123 complete readings match their fixed requirements; one is qualified; ten
unreadable entries remain unassessed. All 25 complete lift readings preserve their
fixed selected data, maps and directions. For complete.rx05.inherited_cardinality,
the cardinality equation matches, but the exported operation context omits the
required comparison routes and selects the third additive-monoid route rather
than cmp.rings.carrier's designated multiplicative source. Its complete record
and the public cells' orientations are retained in the independent review.
Do not resolve this qualification by altering a fixed requirement or silently
changing the separately protected global directed-chain resolution behavior.

All four inheritance and all 17 F9 questions were also executed at `7c87f0c`; each
is recorded as a gap. Competing implementation selections in those original manifests
are preserved in the reports. A prepared explicit selection keeps the existing Fin
cardinality implementation without the competing generic row, and uses the connected
demo's existing 21-registration selector for F9. This is a computational configuration,
not a registry priority rule or a change to the questions. Do not shard the 113-question
general run by file: its one production harness deliberately shares actual returned
data, backend connections and failure/session state across the sorted files.

The unchanged observation controls at `7c87f0c` establish:

- RX05: both coherent registry orders preserve the complete typed requests and
  resolution metadata. Both comparison-absent orders retain all four actual routes,
  including the additive-commutative-monoid route, with their actual components.
- RX09: four prerequisites elaborate, then the original constant-one family is
  invalid at admission. Its actual closed Summable obligation matches the independently
  supplied proposition, with zero backend dispatches.
- Original RX08: eight prerequisites succeed; projection.ker() remains ambiguous
  between module and inherited group kernels. The independently assessed .kernel()
  positive is a separate unchanged input.

The isolated coordinate-framing repair removed RX10's original mapped-source
descriptor mismatch. Its unchanged fixed question then reaches an equality
NoImplementation gap after three dispatches, retaining the returned callable and
complete question. Gap, unavailable, malformed and internal conditions have their
expected strata; holds/wrong and session controls are not complete. The later failure
is in consumption of function-valued element data by the selected adapter. Preserve
this failed attempt; do not claim the successful failure strata establish RX10.

The later unchanged RX10 run at `cedfad6` with published leaf `4382c4c` closed in
115.751 seconds with all guards unchanged. Holds and wrong both stop after one
dispatch at an element-callable target descriptor check, before callable reuse.
Gap, EOF-unavailable, malformed and zero-budget internal conditions retain their
expected strata; session controls are not complete. This is a distinct failed
attempt, not confirmation of the earlier three-dispatch behavior. No downstream
findings from either attempt were supplied to the public-only leaf author.

The real native workflows and the actual notebook were rerun at `cedfad6` with the
published public leaf `1c41aa80993cc4b799893bd3165ddb64d9f80939`. The two finite-
pullback assertions hold; fifteen of seventeen stop at a complete-callable-target
check. The notebook code cell executed and the unchanged report checker failed.
Both runs retain unchanged source/artifact guards. A read-only exception trace of
the original first arithmetic question records different morphismEndpoint descriptors
for the same formal intermediate carrier. Complete endpoint recovery is being repaired
in an isolated kernel worktree; the original scalar owner and actual data must survive.

The latest public leaf is 4382c4c50e617c47ece8be4a745360b84c4a7e18, tree
59002c0549bc9b8315f466f5b6d3097f787b38c0, fetched back and tree-verified. The
public-only author preserved all seven manifests and existing native algorithms.
The closed source-matched runs contain 1,486 request/reply pairs across all 66
existing extension pairs, focused forms, framing, retained-data/ownership reuse,
existing engineering examples, eight verbatim public examples and directly affected
V1 controls. The public examples independently exposed and closed the selected-ring
versus supplied-carrier reader defect. Illustrative unissued opaque tokens correctly
remain unavailable; the kernel functor's native morphism action remains an explicit
ordinary unsupported routine. These are interface assertions, not mathematical
answers. The author received no fixed questions, expected answers, kernel source,
execution findings or other authors' work. Final fixed execution at this leaf is
still required; prior runs selected earlier published leaves.

Active isolated kernel work owns (1) the remaining ordinary-budget lift/factor
reading failures and (2) whole-callable observation and the anonymous constructed
module parameter. Complete interpretation-record retention is being inspected
separately from route choice. Exact source identity, complete family binding and
construction recovery are integrated above. Generic required behavior is not
deferred as a leaf gap.
Publish coherent checked repairs, fetch them back and compare the complete trees,
integrate them, then rerun affected fixed trials at a new coherent freeze.

The source-grounded composition account is refreshed through `cedfad6`. It preserves
its hypotheses about complete actions and ordered parameters, accepted comparison
and refinement evidence, actual-data ownership, recoverable structured schemas and
the declared simple-route enclosure. It does not certify arbitrary backend behavior.
The committed API snapshot and the da6af543-generated export remain intermediate;
generate and publish the final API from the final published, built source combination.

The selected mathematical/contract/Mathlib/notebook revisions and hash-pinned real
engines remain unchanged. Base candidate CI 40194280154 at 691f94f passed its builds
and axiom audit. The cedfad6 candidate CI 40217953880 has completed successfully.
Its Custodian review 40217955626 returned inputs unavailable: rev-parse
FETCH_HEAD^{commit} failed while materializing its isolated base snapshot. This is
not a semantic verdict; no independent review is replaced or self-approved.

Evidence is preserved separately under libfile_94b086b3c1308191b67e0c34e0d4c364.
The last confirmed replacement is version36, 47786058 bytes, SHA256
ff33439da0d0154c6b47c2649b832ad7b5babda0af1f052a9e7fdd9bd5eee1b9.
It preserves every earlier attempt plus the closed full exports, computational
reports, native/notebook runs, independent 153-reading assessment and composition
account. The full task below remains active. This checkpoint is not MVP completion.


## 2. Completion conditions

All rows must be discharged at a coherent final source combination. Earlier observations identify what to preserve and rerun; they do not establish results for the latest candidate.

| Required result | Acceptance condition | Current evidence and open work |
| --- | --- | --- |
| Integrated kernel | Kernel, contract, mathematical dependencies, relevant probes, gates, tools, native executables, and notebook surface build together. Preserve applicable PR #63/#64 behavior within the PR #65-derived implementation. | Complete cedfad6 consumer and native/tool/notebook-worker builds pass at unchanged sources. Active generic repairs will require new integrated verification. |
| Registry-derived interpretation | Mathematical choices come from accepted declarations. Dependent parameters, selected structures, tuple/destructured binders, closed maps, refinements, and admission use generic paths. Preserve genuine ambiguity. | The full cedfad6 consumers pass. The 7c87f0c extension export has 124/134 complete readings; ten remaining interpretation failures are under generic repair. |
| Compositional resolution | New objects acquire old applicable operations; new generic operations reach old objects. Object and morphism actions preserve comparisons, actual parameters, reindexing, and refinements. | Generic machinery exists. Final independent trials and compositional arguments remain required. |
| Computational transport | Nonidentity transport, symbolic and opaque callables, successive computations, exact endpoints, and session ownership work with actual returned data. | Earlier connected runs passed. Latest candidate requires reruns, including RX10. |
| Complete structured results | Computed kernels, cokernels, subobjects, limits, and lifts expose their required defining maps and permit later operations. Creation comparisons work through accepted general data. | Prescribed-lift action-data repair is integrated. Its scoped checks pass in the record. Full fixed structured-result and successive-lift trials remain open. |
| Stable public contract | Every advertised V1 form has complete requests, replies, dependent parameters, validators, ownership rules, and worked examples. A leaf author can implement it from public material alone. | The complete public-form audit and independent public-only adapter work are recorded; final built-source API publication and fixed execution remain required. |
| Permanent mathematical meaning | Independently compare every admitted question's complete typed meaning. Keep revision provenance separate from meaning. Preserve protected assertions and the independent migration/admission boundary. | All 153 complete 7c87f0c readings are independently assessed, including 18 changed encodings. The final producer needs a fresh complete export and assessment. |
| Correct failures | Distinguish invalid mathematics, ambiguity, absent implementation, unavailable backend, malformed reply, well-formed wrong answer, and internal/resource failure. A change of leaf must not change the question. | Earlier RX10 exposed real defects. Final fixed-question conditions, successful callable return, and session/reuse controls remain open. |
| Useful CAS | Run connected real-engine workflows through the existing execution surface. Reuse intermediate values and structured outputs; include nonidentity transport and inherited operations. Verify notebook execution where used. | The cedfad6 native binaries and actual notebook were exercised with leaf1c41. Two pullback assertions hold; fifteen callable-target failures remain. All four workflows require a final successful rerun. |
| Independent extensibility | Freeze kernel and contract; execute every required extension trial against independently fixed mathematics and questions. Extend only through permitted public interfaces. Any required generic patch demands a new freeze and rerun. | Not complete. Partial readings, bindings, and protocol checks do not close this condition. |
| Delivery | Publish integrated source, reproducible examples and evidence, a current public contract/API, and exact source provenance. State genuine limits of V1 while preserving full-B0 obligations. | Pending final integration and execution. |

| Fixed scope quantity | Requirement or recorded inventory |
| --- | --- |
| Useful connected workflows | At least 4, spanning at least 3 mathematical areas |
| Mandatory workflow mechanisms | Structured output followed by reuse; nonidentity transport or comparison |
| Permanent assertion inventory | 153 admitted questions |
| Fixed positive extension inventory | 134 questions in 14 files: 105 original and 29 completion questions |
| Independent extension trials | RX-01 through RX-10, with the additional RX-LIFT obligations |
| Permitted completion stubs | None for required generic V1 behavior; precisely reported absent leaf implementations remain permitted |

## 3. Next work, in order

### A. Integrate current source and verify the final build

The binding, complete-object, product, composition and whole-function source
repairs are integrated at `09d52994`. Its actual first CI failure and the compiler
extraction are recorded above. Preserve newer branch work when publishing, then
fetch back and compare the complete tree. Build all affected consumers,
the unchanged stable aggregates and protected controls, and all four native tools
plus the notebook worker/surface at one exact source combination. Use the explicit
selected contract path for the purity gate; an absent historical fallback path is
an environment failure, not permission to weaken the gate. Keep build sources
unchanged while a provenance-recorded run is active.

### B. Run the unchanged bindings and complete interpretation exports

Use the fixed inputs and reconstructed drivers described below. Read their reports, not just their process exit status. A diagnostic may exit successfully after writing failed bindings.

The `da6af543` binding failures are historical diagnostics, superseded by the
source-specific repairs and reviews above. Select new repairs from actual current
results, not those obsolete first-failure lists. After the coherent build, run
the exact original RX-LIFT factor samples, with all 32 preceding bindings, complete
six-module scope and unchanged 200000-heartbeat limit, before public API export.
Retain full question strings and stage-specific outcomes. Then rerun all fixed
bindings and assertions; neither raising budgets nor changing questions closes
an interpretation or execution defect.

Export complete typed readings for the fixed extension inputs and the permanent corpus. Separate original RX08 spelling from its independently assessed positive clarification. The original `projection.ker()` remains an ambiguity control. The additive positive selects `kernel()` under the published clarification, with the same mathematical questions. It does not authorize changing the original source or approving an interpretation migration.

Obtain independent interpretation assessment for every completed reading, including newly readable statements. Check the full typed terms, selected structures, parameters, maps, relations, and comparison components. Equal printed expressions or equal scalar answers do not establish equal questions.

### C. Execute the fixed extension questions and failure controls

Run RX10 early after the repaired consumers build. It reaches the actual public callable/session path and has exposed remaining integration defects. Use the independently repaired leaf at `fa0856d`, with unchanged registrations and fixed expected outcomes. Verify all execution conditions and subsequent callable use. Then run the complete fixed positive extension inventory, RX05 environment/order controls, RX09 exact admission rejection, and the structured/lift observations.

Repair a missing public encoding in the kernel/contract. Repair an implementation that fails an already complete public encoding in the leaf, with independent public-only authorship where required. Keep a well-formed wrong result distinct from a malformed packet. Never turn an answer into a proof or replace returned computational data with a canonical formal plan.

### D. Complete the public API and useful user session

Generate the contract API from the final published, built source combination. The existing preparatory exporter requires an explicit published kernel SHA and a successful matching build record. Inspect and update stale runtime paths before use; do not reuse the old API's provenance for new output.

Audit each dated leaf-contract complaint against current encoding, decoding, validation, and actual consumers. Demonstrate existing adequate forms instead of reimplementing them. Publish worked request/reply and malformed-reply examples for the advertised forms.

Rebuild the actual executables and run the existing connected demonstration and notebook surface with real engines. Cover the structured defining-map and universal-data obligations through the fixed extension tests as well; pullback cardinality alone does not establish complete result reuse.

### E. Freeze, finish independent trials, and deliver

Freeze the kernel, contract, public API, mathematical inputs, and selected computational registrations. Complete the independent extension requirements and the compositional correctness argument for each supported generic mechanism. Preserve the one-way information boundary when assigning independent authors/reviewers.

Any needed generic repair invalidates the affected frozen-trial result. Repair its owner, publish a new candidate, and rerun affected trials with the fixed questions and expectations preserved. Complete final integrated checks on the delivered source combination. Publish the source, usable examples, contract, and evidence. The final report should give exact revisions and actual outcomes, with any remaining functionality outside V1 clearly identified.

## 4. Source combination and owning repositories

All repositories below are under `https://github.com/dzackgarza/`.

| Repository / role | Branch | Selected source or labelled provenance |
| --- | --- | --- |
| `lean-cas-dsl`: kernel, language, runtime, assertions, tools | `work/kernel-v1-20261023` | This checkpoint; published predecessor `09d52994ab08380bf88c9b0a05fc166325bd81bf` |
| `lean-categories`: historical base-interface provenance; not the selected package | `work/kernel-v1-interfaces-20261023` | `9508da173de86670c4e0c8a4632e2df7d2335949` |
| `lean-categories`: current mathematical dependency | See committed package manifest | `3bd4d3d9695f288749c860368174462c4d689b7c` |
| `lean-cas-dsl-leaf-contracts`: current protocol | `work/kernel-v1-contract-20261023` | `3f7a22e0b6afc3e745f3aa60a9ceecf6740948d5`; generated API still requires final regeneration |
| `lean-cas-dsl-leaves`: existing workflow specimen | `work/v1-contract-diagnostic-20261023` | `2c8b9040ea68513c34817f5c7b6fa5a5ce6b1252` |
| `lean-cas-dsl-leaves`: independent source-action specimen | `work/kernel-v1-independent-leaf-20261024` | `2f35244884649c9268567bb9968840a34559a11c`; earlier sources remain separately scoped |
| `lean-cas-dsl-leaves`: frozen target specimen | Same work branch, fixed historical checkout | `865df49ad0b0b133d5bcfd282f380aa213eb5fff`; original target hashes retained |
| `lean-jupyter-kernel`: existing notebook worker | Read selected package lock and runtime override | `4c6c2a77abcc717513a65ca35723ed428647e1bd` (`worker`) |

Every run records its exact selected source commits, complete trees and unchanged working state. The committed manifest selects mathematics `3bd4d3d`, protocol `3f7a22e`, and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. The specimen rows retain their particular historical experiment roles; each fresh run must identify its actual selected manifest and specimen revision. Source publication does not install an independently accepted mathematical release.

`lean-cas-dsl/main` is `95de265e5a6d61909703a3193f0a1c952e12131f` at this inspection. The active work branch contains the substantive implementation and has integrated that main, retaining the PR #65 architecture and the applicable PR #63/#64 obligations. Do not start again from main or replay old branches wholesale. Issue #69 and all five owner addenda apply: implementation irrelevance permits optional private lateral leaf reuse; shared actions, typed computational constructor access and formally justified dependency closure remain kernel responsibilities. Issues #68 and the historical parity backlogs do not expand this assignment.

Recent source that must survive integration:

| Source area | Existing change to retain |
| --- | --- |
| Admission presentation | Preserve forwarding through the same structure projection using Lean's structure name and field index. Expose actual fields supplied through different structures. Keep original complete obligations and one registered evidence invocation. |
| Generic proof refinement | Expose closed non-proposition type inputs before existing class/Decidable acquisition. Retain the original source/result and final kernel check. The public helper visibility repair is already present. |
| Prescribed-lift action execution | Use the existing realized action encoder. Retain cached computational parameter data and merge dependency owners before field dispatch. |
| Member applicability | Check the full dependent application before constructing competing results; preserve real ambiguity and existing budgets. |
| Complete callable materialization | Retain selected external domain and target, actual packets, and their owners. |
| Residual decision | Expose only the kernel-owned `operationResult` marker at the registered evaluator's residual proposition. Keep the original question and final proof check. |
| Strict purity | `29d3d605` uses `Lean.Core.transform` for marker traversal, removing the tactic dependency. Keep complete callable application spines. |
| Engineering fixtures | Domain fixtures moved into `CasAcceptance.Kernel`; retain aggregate and axiom-audit coverage. Use their current module names. |

## 5. Full mechanism scope

The implementation queue is KM1–KM9 in `specs/computational-core-plan.md`. K1–K14 are regression assertions, not a replacement implementation queue.

| Mechanism | Required behavior to finish or verify |
| --- | --- |
| KM1: compatible implementation | One coherent kernel, contract, mathematical API, tools, probes, and runtime. Preserve generic binder behavior and full creation-lift/defining-map behavior. |
| KM2: mathematical choices | Resolve terminal/global-point, quotient, power-object, literal-domain, equality/observation, and diagram constructions through applicable unique registry data. Verify second presentations/structures, reordered rows, missing rows, and competing rows. |
| KM3: dependent reading | Generic typed parameters, family application, elements, multi-variable/destructured maps, selected vectors and base rings, closed operands, binding operators, and actual admission evidence. |
| KM4: closure and comparisons | Consume `Resolve.completeRoutes` and `ProofRefinement.construct`. Preserve complete functor actions, constructor-induced comparison actions, refinements, selected structures, and reindexing through execution. |
| KM5: point/map transport | Support nonidentity transport, symbolic/opaque callables, exact generalized-point domains, endpoint checks, and ownership. Demonstrate successive operations on actual returned data. |
| KM6: structured reuse | Complete computational projections, defining maps, universal data, creation comparisons beyond a special shape, and successive prescribed lifts. A formal apex or copied downstairs plan is insufficient. |
| KM7: public forms | Resolve every relevant contract complaint: rational/irrational points, bottom-valued degree, differentials, matrices, infinite subsets/spans, binder callables, product apices/projections, and points in composition/mediators. |
| KM8: question permanence | Preserve typed semantic identity independently of implementation, incidental proof terms, and mathematical revision labels. Keep every failure stage distinct. Repair measured runtime obstructions to required operations. |
| KM9: independent extension | Finish frozen extension trials and mechanism-specific compositional arguments. New ordinary extensions must not require edits to frozen kernel/contract or existing mathematical objects/leaves. |

The already formalized power-series object's registration and constructor-induced comparison-cell actions belong to `lean-categories`. Their independent mathematical interfaces are consumed by the kernel. Preserve `completeRoutes`, `ProofRefinement.construct`, and `executePrescribedLift`; complete their consumers rather than replacing them.

## 6. Independent questions and observers

Set `P = tests/acceptance/proposals/independent-extension-reconstruction-20261024/` in the kernel checkout when reading the paths below.

Start with `P/questions.md`, `P/observation-controls.md`, and `P/completion/README.md`. Read the completion coverage, interface derivations, expected-fact sources, coordinate presentations, selected-lift requirements, and clarification assessment. These define mathematical requirements independently of execution.

| Trial | Mathematical question / required observation |
| --- | --- |
| RX-01 | New selected finite order inherits existing cardinality; preserve distinct selected order structures. |
| RX-02 | Two-subsets of an existing finite set; include the complete core-action requirements. |
| RX-03 | Actual automorphism group of a cyclic quotient; include complete automorphism arrows, not only its cardinality. |
| RX-04 | Finite square-bound comprehension and its classifier/refinement. |
| RX-05 | Actual ring-carrier diamond at `PrimeResidues(5, proof)`; retain actual comparison components and complete routes under registration permutation and comparison omission. |
| RX-06 | Regular residue module reindexed along the actual quotient; retain complete selected module action and map. |
| RX-07 | F9 transport in both directions, followed by successive computations. |
| RX-08 | Ordinary projection with restricted form `[3]`; preserve its complete kernel question and defining maps. Keep original ambiguity and clarified positive separate. |
| RX-09 | Entire successor family with genuine series admission; separately reject the exact constant-one nonsummable family. |
| RX-10 | One fixed true question under successful, wrong, missing, unavailable, malformed, and internal execution conditions; preserve the question and check returned-data/session reuse. |
| RX-LIFT | Separate genuine formed-arrow example with successive prescribed lifts and nonzero factorization at each stage. Do not substitute it for RX-08. |

Concrete owners:

- `CasAcceptance/Kernel/FrozenObservationControls.lean`: RX05 and RX09 observations.
- `CasAcceptance/Kernel/FixedQuestionExecutionControls.lean`: RX10 execution observations.
- `specs/reuse/frozen-observation-controls.md`: runner variables, report schema, and interpretation of the observations.
- `P/completion/clarifications/rx08-module-kernel-name-assessment.md` and `rx08-ordinary-module-kernel.cas.proposal`: independently assessed positive spelling.
- `P/completion/permanent-interpretation-assessment.md`, `initial-extension-interpretation-assessment.md`, and the RX05/RX09 assessments: earlier independently reviewed meanings, scoped to their recorded producers.

RX05 must use each environment's own actual resolution. The comparison-absent environments preserve other accepted rows and the additional additive-commutative-monoid route; do not simplify the candidate set to an invented two-route model. Compare complete typed requests, including actual comparison components and designated source, allowing only enumeration-order differences where specified.

RX09 must reach the intended admission obligation after its prerequisites elaborate. Its typed rejected `Summable` proposition must match the independently specified theorem. A parser error, unrelated type error, missing implementation, or internal exception does not satisfy the negative.

The proposal and leaf records disclose an incidental agent-inventory exposure during earlier independent work. Preserve that disclosure and use a fresh suitably isolated reviewer for independence or acceptance judgments. A public-only leaf author must not receive this implementation handoff, kernel source, fixed answers, or runtime acceptance results. Give that author only the authorized public API/contract, specimen subtree, and runtime information.

## 7. Runtime and recovery

These paths are from the interrupted Pro container. Their existence was recorded in the source conversation, not verified on the machine preparing this handoff. A new Pro container may have a different root.

```text
old root: /workspace/scratch/08e8d69f9eb1

lean-cas-dsl/
kernel-integrated-20261025/
kernel-runtime-20261025/
  lean-4.33.0-linux/
  lake.sh
  packages.json
  run_coordinated_build.py
  run_focused_diagnostic.py
  run_current_rx10.py
  kernel-build-binding.json
kernel-dependencies-20261025/
  lean_categories/
  cas_leaf_contracts/
kernel-computational-runtime-20261025/engines.sh
kernel-verification-20261025/
kernel-mvp-frozen-trials-20261025/
kernel-fixed-execution-prep-20261025/
kernel-public-api-20261025/
kernel-mvp-evidence-restored-20261025/
kernel-mvp-verification-evidence-20261024.zip
```

Read the build binding and package overrides to locate the actual build producer; do not assume every listed worktree is the same source. Preserve dirty work and source from isolated repair worktrees before integration.

The evidence archive was saved in ChatGPT Library under:

```text
file: kernel-mvp-verification-evidence-20261024.zip
library_file_id: libfile_94b086b3c1308191b67e0c34e0d4c364
last observed version receipt: 25
```

Retrieve the latest available version through the Library connector if it is absent locally. Inspect `members.json`, recorded hashes, original paths, and producer records. Version 25 was associated with preserving the closed integrated-consumer build, strict-purity finding, and published structural traversal repair. It does not establish that the still-running final consumer build later succeeded. Older archive hashes in the conversation refer to older versions.

| Runtime component | Recorded version |
| --- | --- |
| Lean | 4.33.0 |
| Mathlib | v4.33.0, with exact selected dependency data in the package records |
| Computational Python | CPython 3.12 |
| Sage/passagemath | 10.8.13 |
| Native GAP | 4.16.1 |

Restore engines from `examples/kernel-v1/requirements-passagemath-py312-linux-x86_64.txt` when needed. This is the existing hash-pinned package input. `CAS_SAGE_PYTHON` is an executable interpreter path, not a shell command.

Keep local dependency overrides outside committed source and use the same selection for build and execution. Check exact revisions and trees rather than trusting `@ main` declarations or an old native binary. The earlier workspace had generated-artifact synchronization problems; retain isolated, coherent build outputs and verify source/artifact ownership. Reuse valid caches instead of repeatedly rebuilding unrelated dependencies.

Prepared fixed drivers in `kernel-verification-20261025/`:

```text
KernelFixedBindingReconstructed20261025.lean
FrozenQuestionReadingsReconstructed20261025.lean
reconstructed-diagnostics-preparation-20261025.json
permanent-fixed-inputs.json
```

The recorded binding and extension-reading invocation shape was:

```bash
bash /workspace/scratch/08e8d69f9eb1/kernel-runtime-20261025/lake.sh \
  env lean /workspace/scratch/08e8d69f9eb1/kernel-verification-20261025/KernelFixedBindingReconstructed20261025.lean

bash /workspace/scratch/08e8d69f9eb1/kernel-runtime-20261025/lake.sh \
  env lean /workspace/scratch/08e8d69f9eb1/kernel-verification-20261025/FrozenQuestionReadingsReconstructed20261025.lean
```

Inspect the drivers and current project recipes before execution. Select fresh report paths and preserve their inputs. `CAS_FIXED_BINDING_INPUTS` and `CAS_FIXED_BINDING_REPORT` select the original-input diagnostic variant. The preparation record explicitly says a zero exit can mean that failure data was written. Check every failure field.

The restored fixed-input directory contains `inventory.json`, `positive-original-inputs.json`, `positive-clarified-inputs.json`, and runtime manifests. Recorded manifest names include `manifest-f9.json`, `manifest-general-public-callables-fa0856d.json`, and `manifest-inheritance-public-callables-fa0856d.json`. Path rebinding may change executable locations only; retain selected registrations and all fixed mathematical inputs.

`run_current_rx10.py` was reconstructed from the archived `kernel-mvp-rx10-parameter-recovery-20261024/run-current-closure.py` and its `next-public-endpoints-run-plan.json`. Check those references and current paths before running. Preparation or script compilation alone is not an executed trial.

If the Library archive cannot be obtained, recover the published source and fixed proposal files, then reconstruct the missing runners from their documented contracts. Mark reconstructed material accurately and rerun it. Do not claim that absent historical patch bodies, diagnostics, or outputs have been recovered.

## 8. Evidence limits and final execution surface

The record already contains useful results. Preserve them with their producer revisions and use them to avoid reopening solved problems. They require fresh confirmation where the final source or dependency closure has changed.

| Recorded evidence | Scope and remaining requirement |
| --- | --- |
| Connected real-engine demonstration | Earlier run: 17/17 assertions and 54 dispatches. Reexecute on the final candidate. |
| Permanent interpretation | Earlier export/review: 153 questions; review includes 11 previously unreadable statements and agreement for 142 retained historical meanings. Final producer export and assessment remain required. |
| Complete extension export at `5f7f5a2` | 94 complete readings and 40 empty records from 134 questions. Completed readings were assessed; this remains an incomplete export. |
| Binding diagnostic at local `95227b8` | 182 bindings across 14 files; retained 4 failures. Its zero exit was report production, not success. |
| Consumer build at published `8ea95e6` | Selected consumers passed, before later repairs. It does not establish current native or full-suite results. |
| Admission correction | Focused original limits, reindexed-map obligations, whole bilinear map, and polynomial unit/nonunit controls have recorded outcomes. Finish their integrated consumers and fixed questions. |
| Prescribed-lift correction | Recorded action-data and owner checks pass. Mathematical frozen lift questions remain separate. |
| Latest purity result | `CasGates.KernelPurity` built at the final recorded consumer run; `KernelPurityProbes` failed as described above. |

Existing demonstration files:

```text
examples/kernel-v1.md
examples/kernel-v1/01-selected-arithmetic.cas
examples/kernel-v1/02-finite-pullback.cas
examples/kernel-v1/03-matrix-iteration.cas
examples/kernel-v1/04-presentation-transport.cas
scripts/run_kernel_v1_demo.py
notebooks/kernel-v1.ipynb
```

The workflows exercise exact integer/rational/modular arithmetic, finite pullback/product reuse, successive matrix applications, and F9 presentation transport. Keep their independently fixed expectations. Complete projection, whole-map, universal-property, and lift observations through their owning tests rather than inferring them from counts or sample evaluations.

Use `examples/kernel-v1.md` for the actual runner contract. Its build consumers include `cas-harness` and `CasDsl.Notebook`. The runner supports explicit `--packages`, `--contract`, `--sage-python`, `--lake`, and leaf manifest selections. Read the current arguments before invocation. Run the existing notebook integration as a connected user session; a notebook without executed outputs is only a prepared artifact.

## 9. Authority, scope, and delivery rules

`lean-categories` owns mathematical definitions, structures, functors, comparisons, admissions, and formal properties. The kernel interprets and executes against those accepted interfaces. Leaves provide computational implementations with no mathematical authority. Returned data may be invalid or wrong; it cannot determine meaning or certify itself.

The original assignment permits necessary cross-repository fixes and parallel kernel work. It supersedes earlier procedural limits on kernel delegation, upstream edits, and work selection exclusively by K1–K14. It preserves mathematical correctness, protected assertions, independent acceptance, and public-only leaf authorship. Delegate only with information boundaries suitable to each role.

Preserve exact selected structures, complete maps and parameters, comparison directions, generalized-point domains, actual returned values, and their session owners. Equal underlying carriers or Hom types do not identify different structures. Registration order is not a semantic priority rule. A real unresolved ambiguity stays ambiguous.

Use existing Mathlib and project mathematics. Submit necessary mathematical work to its owner with independent justification. Keep independent mathematical admission and interpretation-migration decisions separate from implementation authorship. Do not rewrite protected baselines to approve the new implementation.

Scope excludes bulk production-leaf registration, backend parity campaigns, unrelated notebook features, unrelated repository backlogs, and broad performance or style work. Fix measured runtime defects that prevent required V1 behavior. No substantial generic defect in an advertised V1 mechanism can be deferred as a leaf gap.

Keep all user-authored and previously existing work. Do not reset, clean, discard, or overwrite it. Commit and push coherent changes periodically; preserve source and diagnostic records before container interruption. Keep exact source-tree verification distinct from successful mathematical execution.

Deliver the working system and its runnable examples, not another assessment or plan. Stop only when the completion conditions are established, or when a genuine external decision or unavailable input prevents further authorized work. Keep the remaining required work in the authoritative handoff if such a boundary is reached.

## Source links

- [Conversation](https://chatgpt.com/c/6adc8d51-f270-83ea-ac4d-bcb9911c54d8)
- [Verified kernel checkpoint](https://github.com/dzackgarza/lean-cas-dsl/commit/29d3d60500cf1e4d2b49de0355ec8017eaa836bd)
- [Computational-core plan at that checkpoint](https://github.com/dzackgarza/lean-cas-dsl/blob/29d3d60500cf1e4d2b49de0355ec8017eaa836bd/specs/computational-core-plan.md)
- [Repository handoff inspected for earlier evidence](https://github.com/dzackgarza/lean-cas-dsl/blob/29d3d60500cf1e4d2b49de0355ec8017eaa836bd/HANDOFF.md)
- [Fixed extension questions](https://github.com/dzackgarza/lean-cas-dsl/blob/29d3d60500cf1e4d2b49de0355ec8017eaa836bd/tests/acceptance/proposals/independent-extension-reconstruction-20261024/questions.md)
- [Frozen observation controls](https://github.com/dzackgarza/lean-cas-dsl/blob/29d3d60500cf1e4d2b49de0355ec8017eaa836bd/specs/reuse/frozen-observation-controls.md)
- [Connected demonstration](https://github.com/dzackgarza/lean-cas-dsl/blob/29d3d60500cf1e4d2b49de0355ec8017eaa836bd/examples/kernel-v1.md)


## Noticed, not worked

- `operationProductRow` still rejects creation-lift resolutions, and
  `operationProductCone` requires the selected apex to be definitionally the
  operation's literal `Prod` domain. The supplied direct Sets cone satisfies
  that check; this does not establish comparison against a differently
  presented product. The consumer must retain an independently supplied apex
  comparison when needed, rather than select a concrete product or weaken the
  complete-endpoint check. The accepted constructor comparison-cell actions
  concern functors on constructed categories and do not by themselves identify
  this operation's chosen product domain.
- Inert preparation is not yet a global invariant: fresh application, binder,
  method, specialized composition and prescribed-lift branches still dispatch;
  `Prepared.trace` still seeds an expression cache and reruns realization.
  The common callable/universal/projection lifecycle does not yet cover those
  producers or general prospective admission of their future result ports.
  Retain explicit typed operands and all already known owners; passing scoped
  action controls does not close this defect.
- `EndpointPresentation` still retains comparison expressions and packets
  without their complete executable map Wires. Mapped comparisons must also
  retain the exact image endpoints chosen by the outer object action; an
  independently repeated object action can return a different opaque occurrence.
  A formal comparison alone cannot mark either map computationally complete.
- The `f3545ac` custodian review did not produce a verdict. Run `40197923885`,
  job `121182701288`, reports `REVIEW NOT COMPLETED (inputs unavailable)` because
  `git -c core.hooksPath=/dev/null -C /tmp/custodian-review-ct_kwx98/base rev-parse
  FETCH_HEAD^{commit}` exited 128. This is an unavailable review input, not a
  semantic rejection or approval. No authority check has been bypassed or
  self-approved; unaffected construction continues under the existing mandate.
- The unchanged original leaf manifest contains overlapping exact/category and
  own-request/source registrations. These correctly remain ambiguous. Runtime
  demonstrations use an explicit configuration selecting registrations; the
  kernel does not introduce a priority rule.
- Missing ordinary leaf operations are not kernel infrastructure defects. Bulk
  registration, broad backend parity, and unrelated notebook development remain
  outside this assignment.


## Independent acceptance boundary

The protected question baseline uses an earlier identity format. This work adds
an independent typed structural comparison and removes the mathematical revision
from semantic identity while retaining it as provenance. Source authors must not
rewrite the protected baseline to approve their own interpretation migration or
claim acceptance from source publication. The applicable independent assessment
remains distinct from implementation and engineering readiness evidence.
