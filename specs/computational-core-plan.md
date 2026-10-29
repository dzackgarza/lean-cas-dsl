# Computational core: execution plan

Architecture (controls this plan and the requirements): [architecture.md](architecture.md).
Requirements: [computational-core.md](computational-core.md) (identifiers `CC-*`).
Mathematical denotations: [FOUNDATIONS.md](https://github.com/dzackgarza/lean-categories/blob/main/FOUNDATIONS.md) (in `lean-categories`), Parts I–IX.
Upstream issues: [#53](https://github.com/dzackgarza/lean-categories/issues/53),
[#54](https://github.com/dzackgarza/lean-categories/issues/54).

This plan is tracked in the repository deliberately: `.agents/plans/` resolves only in a
local checkout, and this work must be readable wherever the repository is.


> **Governing owner directions.** [The 2026-09-30 convergence process](owner/convergence-process.md)
> supplies the bounded extension and independent-acceptance requirements. The 2026-10-01 B0
> directive and the [2026-10-23 V1 assignment](https://github.com/dzackgarza/lean-cas-dsl/blob/work/kernel-v1-20261023/HANDOFF.md#1-the-task) specify the usable
> product and positive capabilities to deliver. Read the earlier coverage freeze under those
> later assignments: unrelated expansion remains deferred; required computations, execution
> surfaces and independent extension trials remain implementation work.
> The legacy custodian seal (`e3cf7a8`, boundary `0ba53dab`) and
> `proposal/sealed-kernel-pin-mismatch` are historical construction inputs, not an accepted B0
> tuple or a veto on authorized replacement. Construction authority does not authorize
> changing mathematical requirements or accepting or installing one's own authoritative judge.


The mathematical scope includes **CC-HIGHER/#82**: retain the full coherent data required by each promised construction, with no universal dimension-two ceiling. Its interpretation belongs to the existing KM2–KM8 obligations and independent KM9 validation; missing required higher data remains named and open. The 2026-10-29 operative rewrite makes these mathematical obligations the current work order; it changes neither the fixed mathematical questions nor the acceptance inventory.

## B0: the extensible computational baseline (owner directive, 2026-10-01)

**This section controls the plan.** It replaces the open-ended improvement process with one bounded
construction programme. Where an older section, node or rule below conflicts with it, this section
wins and the older text is superseded. The owner's convergence process
([`owner/convergence-process.md`](owner/convergence-process.md)) still governs; B0 is its fixed
positive target. No new requirements repository, policy hierarchy, reviewer service, certificate
system or progress ledger is introduced: this table, Git history, review discussion and generated
test results are the whole record.

### Definition

B0 is complete only when all of the following hold at one compatible revision tuple
(`lean_categories`, `cas_leaf_contracts`, kernel, specimen leaves, acceptance corpus and
interpretations, evaluator and controlling requirements):

1. **The mathematical interface is upstream and complete** for every extension mechanism B0 claims:
   definitions, operations, constructors, classifiers, structural maps, comparison cells, admission
   conditions and presentation meanings are `lean-categories`'. A leaf contributes none of them.
2. **The kernel derives the interface generically.** A newly formalized object receives every
   existing applicable operation without forwarding; a newly formalized generic operation reaches
   existing applicable objects without editing them. Parameters, selected structures, actual
   structural routes, defining maps and prescribed result lifts are retained.
3. **The computational path is usable.** The required computational assertions below execute
   through real registered backends, return the declared result forms, and meet their independent
   assertions. A Lean proof of an assertion does not discharge a requirement that a registered
   implementation execute it.
4. **The acceptance boundary is independent.** Neither the implementation author nor the
   orchestrator can change the mathematical question, its expected answer, its required
   implementation status or the rules judging the change, and then accept the change.
5. **Independent extensions succeed after the kernel is fixed** (exit trials below), with the
   kernel and old leaves unchanged except where a failed trial exposed a genuine deficiency that was
   repaired before the trial was restarted.

**The orchestrator cannot reduce this table, move a row beyond B0, or redefine a row's acceptance.**
A change to a row needs a decision of the authority that owns the requirement.

### Kernel MVP: proved readiness for substantial leaf development (owner instruction, 2026-10-23)

**The implementation target is an extensible kernel, not a collection of leaves.**
A leaf author implementing any registered operation over a B0-supported request/result
form must need only the released mathematical API, computational contract, and an
existing engine. Leaf work must not routinely uncover a missing interpreter case,
undocumented wire type, transport/lift algorithm, or mathematically unsupported
operation that must be patched upstream to keep that leaf functioning.

This is a *bounded statement about the extension mechanisms B0 already claims*:
dependent operation/object declarations, structural functors and their actions,
classifiers/refinements, comparisons, presentations, binders, parameter/fibration
transport, and structured universal constructions/lifts. New mathematics outside
these mechanisms is not promised for free. Conversely, the kernel cannot declare
itself ready by shrinking the accepted mechanisms or by refusing their legitimate
instances.

**Source of implementation work (updated 2026-10-28).** The integrated candidate is
[`work/kernel-v1-20261023`](https://github.com/dzackgarza/lean-cas-dsl/tree/work/kernel-v1-20261023)
in [PR #67](https://github.com/dzackgarza/lean-cas-dsl/pull/67), derived from `b0/kernel`
with the applicable #63/#64 binder and complete-lift behavior to preserve and verify
within that combined implementation.
[The current handoff](https://github.com/dzackgarza/lean-cas-dsl/blob/work/kernel-v1-20261023/HANDOFF.md)
and the actual combined source determine current defects. Links to `b0/kernel`,
the October 22 checkpoint and earlier audits below identify historical observations;
they are not a current backlog without reproduction. The tasks distinguish missing
code from existing implementations whose integration and generality still require proof.

<a id="current-delivery-sequence-2026-10-28"></a>

#### Current delivery sequence (2026-10-29)

[#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10) orders the unchanged KM1–KM9
obligations below. In accordance with the [owner's instruction on #82](https://github.com/dzackgarza/lean-cas-dsl/issues/82#issuecomment-6476540209),
the operative work and acceptance are the selected mathematical constructions, their
compositions and the relations being asserted. An implementation state, a reporting
classification, a program type or a migration of source modules is not a mathematical
milestone. Engineering prerequisites and safeguards remain explicit below.

**The first construction couples #66 and #69.** Completing all of #66, all readings,
or every legacy consumer is not an entrance condition for #69. KM1–KM9 are completion
obligations, not nine serial implementation projects. Establish the first construction's
meaning and exact required inputs, build its replacement through the actual production
path, and remove the path superseded for that use. Then extend coverage in the mathematical
dependency order. The full inventory and combined build remain required before delivery.

| Order | Mathematical work and owner | Required result |
| --- | --- | --- |
| 1 | Complete selected interpretation, #66 with #23/#82 | The existing first composite has its full dependent parameters, structures, admission hypotheses, diagram and relation, independently agreed. Implementations installed downstream do not select its meaning. |
| 2 | Selected construction, comparison and defining-map use, #69 with #66 | Compute the required structured result and apply the required nonidentity comparison. A later operation uses the actual supplied defining map at its exact endpoints. All required cone/cocone or subobject data remain associated with the independently fixed construction. A scalar invariant or formal plan alone is insufficient. |
| 3, before extending coverage | Preservation of the first construction under its actual subsequent uses and independent public use, #69/#24 | For each mathematical operation used in this trial, state its inputs, outputs and preservation of selected structure and coherence; cite the enforcing implementation. A public-only source contributor feeds an unchanged target consumer. Extend this argument before claiming a genuinely new construction or composition, rather than requiring the whole promised scope before the first experiment. |
| 4 | Complete the promised mathematical scope, #66/#69 with #23/#82 | Interpret and compute the remaining admitted constructions and their subsequent uses. Supply the corresponding argument before counting a genuinely new construction or composition as supported. One successful chain is not a proof of the whole scope. |
| 5 | Complete independent mathematical observations, #24 | At the delivered combination, establish all fixed readings, assertions, negative controls, connected real-engine computations, notebook observations, public interfaces and prescribed frozen independent trials. |

Use #69's existing first-stage RX-LIFT construction, nonidentity coordinate, inclusion and
factorization, with its unchanged questions, prerequisite bindings, imports and budgets.
The source-comparison/successive-lift questions follow when claiming that further composition;
they do not precede the first single-stage result. These are ordered existing diagnostics,
not a new or reduced acceptance suite or a prescribed example for an independent contributor.
State the construction's diagram, chosen structures and maps,
required universal factorization, comparison components and any higher compatibility. For a
kernel this includes `i : K → X`, `f ∘ i = 0` and its universal factorization; for a general
cone or cocone it includes every required leg and mediator. Accepted upstream mathematics
supplies the formal laws. The computed candidate is untrusted data judged against that
meaning; decoding does not prove universality or identify the answer with the formal result.

For an ordinary selected comparison `α : F ⇒ G`, retain its components and naturality
`G(f) ∘ α_X = α_Y ∘ F(f)`. Use an inverse only when supplied. A higher construction retains
its actual higher comparison and compatibility, rather than replacing it by strict equality.
A return to a structured source category needs the declared lift; an operation inherited at
its forgetful image does not supply that lift. The first public-only trial must exercise
the construction and its later map use, not just produce a well-formed packet.

**Stop expansion if the next mathematical operation cannot use the complete supplied
construction and its declared maps/comparisons.** Recovering missing context from a term or
packet, inventing identity associations or rerunning a selected construction while keeping its
old dependent maps exposes an unfinished interpretation or interface. Repair it and repeat
the fixed trial before expanding.

**Supporting integration and implementation obligations.** First build the imports,
accepted mathematical interfaces, contract, runtime and driver actually needed for the
selected production computation. Repair necessary retained prerequisites or a minimal
temporary compiler/environment blocker; otherwise replace the failing path directly.
Do not require a green legacy whole-kernel, native-tool or notebook build before the first
substitution. A mock, type-only prototype or unintegrated second kernel does not count.
Keep the work in PR #67's integration line and measure the existing focused edit/check loop.
The high-priority [#83](https://github.com/dzackgarza/lean-cas-dsl/issues/83) tooling work
uses the local sequence in [Running checks](#running-checks) within this trial. It does not
replace the shared producer/action-retention repair or introduce a new evaluator or controller.
The complete combined build, native tools and notebook remain required before delivery.

Reuse adequate common machinery, including the existing execution owner where sufficient;
the presence of compatibility entry points does not itself establish competing lifecycles.
Remove the replaced interpretation/reconstruction/completion paths and their bypasses as each
mathematical use transfers. Enforce the required schema, endpoint, comparison, ownership,
failure and resource checks in that replacement. Do not retrofit all old records, repair
all old observers or optimize old schema/interner paths before deciding what survives.
Ordinary execution may omit unused audit serialization only after required preparation
validation is preserved; complete requested exports keep every fixed meaning, ID and failure.

Engineering probes that call removed private helpers or manufacture old cache entries must
retain their substitution, ownership and ambiguity controls at the replacement boundary.
Do not keep a superseded recovery API just to preserve such fixtures. Independently fixed
mathematical questions and expectations remain unchanged. Full corpus completion and final
API generation follow demonstrated composition; only the public slice used by the first
independent trial is needed early. Deletion supports the mathematical argument; it does not replace that argument.

Preserve the actual supplied result/component associations, complete interfaces and owners.
Retained use, evaluation at a definition's use and deliberate fresh replay are distinct.
Required selected data is not disposable lookup storage. A new choice requires its own
dependent maps, or the accepted comparison and actual transport. Keep lazy demand, adequate
fused realizations and all admitted portable/owned alternatives. A reference alone provides
no public morphism action. Formal functoriality does not prove arbitrary leaf computations
pure, repeatable or correct, and does not require every primitive to be dispatched.

The [verbatim evaluator assessment](reuse/kernel-evaluation-machine-assessment.md) remains
unchanged as provenance. The implementation choice is now explicit in
[cc-realize-2cat](reuse/cc-realize-2cat.md): adapt PolyFun's caller/handler suspension and return
transitions into the existing selected-plan/`InvocationExecution` owner; retain the named
construction plans, completion validators, lift fold and dispatcher; remove the migrated
path's recursive orchestration and expression/packet recovery. Use encapsulated checked
records and opaque operand/output references. No external evaluator package or second
program store is added to the kernel. #69 implements and validates this route, rather than
choosing it again. No new framework phase, deletion manifest or governance service is adopted.

The other source choices are also fixed. [cc-dsl-language](reuse/cc-dsl-language.md) names
Lean's public application/binder APIs and the existing contextual exporter for #66.
[cc-forms-general](reuse/cc-forms-general.md) and [cc-adjunctions](reuse/cc-adjunctions.md)
name the existing upstream mathematical inputs, with no V1 Hex/foundation migration.
#24 reuses the independently authored `extensions-20261024` leaf package for rational lifts
and factors through current public helpers; it does not rewrite those algorithms.
[cc-backends](reuse/cc-backends.md) fixes existing process-hosted GAP and notebook transport
reuse. Exact source revisions are inspection provenance; own-organization delivery still
consumes latest main. Compatibility and mathematical outcomes remain to be demonstrated.

#66 preserves candidate mismatch versus selected-reading/internal failure and speculative
rollback; #69 preserves supported/unsupported/exhausted schema inspection through completion.
Relevant panic/default paths cannot convert internal failure into apparent success. Required
checks survive execution/export separation; absent export is not an unreadable question.

**Actual mathematical input dependency.** The source audit inspected kernel `4c33b574`,
whose manifest selects `lean-categories` `3bd4d3d9` and contract `34bb8abb`. Upstream
mathematical main was `8782c22b`; the selected source was 30 commits ahead and 65 behind.
Existing [upstream PR #93](https://github.com/dzackgarza/lean-categories/pull/93) contains
interfaces and targets main; [#94](https://github.com/dzackgarza/lean-categories/pull/94)
contains independent specimens and targets #93's branch. Candidate `CellAction.assemble`
consumes constructor-comparison fields absent from that main's `ConstructorEntry`.
The formalized power-series object's publication is also in the pending work. Reconcile
and independently assess these existing inputs through their own authority, then verify
the kernel against the resulting current inputs. Do not reimplement them, call them already
available on main, or treat a diagnostic snapshot as the delivery dependency rule. An exact
absent input blocks its consumers, not unrelated work; downstream defects do not rewrite
a formalization brief.

The first RX-LIFT slice also consumes #94's `DegeneratePlaneLifts` and
`DegeneratePlaneFactorization` declarations, including its selected monicity, point and
cone-factorization evidence, plus their required import closure. #69 names the exact source.
Verify their independent acceptance and permitted availability for this trial; they are absent
from the inspected upstream main. Unrelated upstream deliverables remain outside this
prerequisite, and the fixed specimen is not replaced with an easier main-only example.

The first two working days are the decision point for the construction and subsequent-use
trial. The 1–2 week allocation in #10 is a budget, not a forecast justified by past closure
rates. Existing per-ID reports distinguish build, meaning, preparation, availability,
execution and subsequent use; those are diagnostics, not a ladder defining mathematical
completion. The October 20 report's 101 runtime preparation gaps were not 101 unreadable
questions; its independent review found 148/153 readings. Preserve every fixed ID and report
stages not reached. The latest candidate run inspected,
[40652257963 at `60829a1f`](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40652257963),
failed before downstream acceptance; later documentation commits give no fresh runtime verdict.
Line counts, governance percentages and monotonic holds do not replace acceptance.

The contract integration work is also concrete: #24 records existing lift/map helpers on
contract source `34bb8abb` that are absent from inspected contract main `3382e4e0`, and the
independent leaf adapter must consume the public actual-image metadata. Reconcile and publish
that existing contract work through its owner; adapt the public leaf boundary without
rewriting rational algorithms or restoring recipe recovery. Complete that conformance before
freezing the unchanged-target trial. Source selection does not establish runtime compatibility.

### Issue disposition and later work

| Tracker | Continuing responsibility |
| --- | --- |
| #10, #66, #69, #24 | Current V1 work order, interpretation, execution and full independent acceptance. |
| #23 / #82, supported by #20/#21 | Existing consumer questions and exact construction-specific mathematical inputs, reviewed before readiness; no new inventory system. |
| #19 → #20 → (#21 and #23) → #22 | Full B0 computational coverage and exhaustive Sage parity after V1; bounded requirement discovery already runs now. |
| #3, #8, #13, #34, #68 | Later unit-group delivery through the selected process-hosted GAP bridge, logging, the next genuine research-use harvest, wider Sage installation portability and the selected public research entry point. Existing V1 runtime and advertised-capability defects stay in #24/#66/#69. |
| #71–#81 | Historical findings, corrections and resolved/superseded proposals. Closure consolidates tracking; it does not claim their transferred runtime work has passed. |
| #83, within #66/#24 | Demonstrate persistent compiler feedback on a real production edit, the fresh downstream result and measured artifact reuse; #66 owns focused feedback and question provenance, and #24 owns build/cache integration. Tool installation or policy edits alone do not complete this obligation. |

Certificate-primary evidence remains unadopted and would first require an INTENT change.
The selected existing forms and realizations in #10 resolve the reuse direction;
Hex/foundation migration and a new backend fleet are not V1 tasks. A required missing
finite-diagram leaf uses the named adapter source under #23, not a new kernel case. The fixed inventories and
the single exit condition below are unchanged.

#### Mathematical work and acceptance — KM1–KM9

These are the operative obligations. The mathematical statements below determine what the
implementation must interpret and compute. Ordinary equations describe the ordinary
fragment; CC-HIGHER supplies the required coherent analogues for a promised higher
construction. Neither a well-formed representation nor a finite execution test supplies
a formal law or proves an arbitrary backend correct.

| Work | Mathematical deliverable and acceptance |
| --- | --- |
| **KM1 — One compatible interpretation of the accepted mathematics** | Interpret the accepted categories, dependent families, operations, comparisons, admission hypotheses and universal constructions together. In particular, binder meanings and complete creation-lift data must coexist without changing the selected questions. **Supporting build order:** first compile and execute the real dependency closure of the selected construction while replacing its defective paths; a green legacy whole-system build is not an entrance condition. At completion, one kernel, contract, mathematical input, probe/tool and runtime combination builds. Preserve the applicable #63/#64 behavior in PR #67; disabling a gate or merely combining source does not establish KM2–KM9. |
| **KM2 — Declared constructions determine the meaning** | Terminal objects and generalized points, quotient and power-object constructions, literal domains, diagrams and observation relations are those of the applicable accepted declarations. For a chosen `U:C→Set`, an element of `U(X)` is a map `1_Set→U(X)`; it need not be a global point `1_C→X`. A declared presentation by `S→X` retains `S` and the accepted relation to the element being represented. Independent readings agree for the existing second presentations/structures and distinguish genuinely different choices. Reordering declarations cannot select a construction. Missing input and unresolved ambiguity stay explicit; a syntax spelling may select its declared operation. |
| **KM3 — Complete dependent application and admission** | An application retains every dependent parameter and its actual domain hypotheses; substitution yields the declared source and target. The fixed questions include destructured `((a,b),(c,d)) ↦ …`, several bound variables, selected `Vec(ℤ,2)` and its base ring, closed maps/points, dependent families and admitted binders. Interpret all K2–K8/K14 reading portions and the entire admitted inventory with their independently fixed meanings and protected negatives. An out-of-domain expression, an ambiguous interpretation and a valid question with no computation are distinct. A false well-typed assertion remains a valid question. No production backend is needed to establish its meaning. |
| **KM4 — Functorial propagation and coherent comparisons** | For selected `F : C → D`, use `F(X)` and `F(f) : F(X) → F(Y)` with the declared identity/composition laws. An operation on `D` is inherited at that image only on its declared domain; invariants defined on `Core(D)` are inherited along `Core(F):Core(C)→Core(D)`. A selected `α : F ⇒ G` acts by its actual components and naturality; equivalence of interpretations uses the comparison and compatibility actually supplied, not arbitrary noninvertible transformations. Consume constructor-induced comparison actions, proof-only refinements and specified reindexing. Establish K10's ring diamond and formed-module kernel comparison, K11's complete resolution, K12's constructor action, `Fin 2 × ℤ/3` refinement, and two structures on one carrier. New objects/operations acquire exactly the applicable composites without editing old objects/leaves. Existing `completeRoutes` and `ProofRefinement.construct` are implementation inputs to validate, not tasks to recreate. |
| **KM5 — Morphisms, generalized points and change of presentation** | Composition and application use the selected arrows with their full endpoints. If `x : S → X`, its functorial image is `F(x) : F(S) → F(X)`; comparison of views `α_X : F(X) → G(X)` acts on `y : S → F(X)` by `α_X ∘ y` with domain `S`. No domain is replaced by a singleton or chosen by carrier equality. The fixed nonidentity `𝔽₉` translation and successive computations use the actual supplied maps and points. Accepted symbolic/opaque arrows are not required to admit finite graph enumerations. **Supporting checks:** exact computational endpoints, ownership/session compatibility and missing/wrong comparisons remain validated. |
| **KM6 — Complete universal data and subsequent constructions** | For `D : J → C`, the requested construction includes its chosen cone/cocone, all required legs and universal factorization. For a kernel in its accepted pointed/module context, retain the selected `i : K → X`, `f ∘ i = 0` and factorization; a class of isomorphic subobjects does not alone select its representative map. A result returned through `U : C → D` requires the prescribed lift/creation data and comparison, not automatic inheritance from `U`. Compute and subsequently use the declared lift of the module kernel with restricted form and inclusion (without inferring a categorical kernel in a category of form-preserving maps), the finite-set creation-lift pullback, a second registered shape/route and successive lifts. A lifted cone is universal upstairs only under the accepted creation/lifting hypothesis; otherwise retain exactly the structured construction and universal property actually supplied. Actual supplied computational data remains distinct from the accepted formal construction and its proof. Missing/wrong components are detected; a bare apex, copied downstairs result or unevaluated formal plan is insufficient. Existing prescribed-lift computations remain inputs to this work. |
| **KM7 — Adequate presentations of the promised mathematics** | Every advertised V1 operation has presentations of its complete dependent inputs and outputs, with accepted denotations and the maps needed for later mathematical use. Discharge each dated public-contract complaint: nonintegral/irrational points, bottom-valued degrees, Kähler differentials, matrices, possibly infinite spans/subsets, binder-defined maps, product apices/projections and points used in composition/mediators. An existing callable source form does not automatically present a returned product. For each case, identify the adequate existing form or exact missing generic form and demonstrate the fixed mathematical use. A public-only contributor can compute the operation without inventing a meaning, proof or representation convention. **Supporting checks:** complete encoding/decoding, hostile replies, dependencies and owners. |
| **KM8 — The same mathematical question and observation** | Every permanent assertion retains its independently assessed relation/proposition, operands, domains, parameters, selected structures, morphisms and required comparisons. Proof terms and revision labels alone do not change that meaning. For a form `d : T → C` and relation `R`, a kernel comparison of decoded presentations `c` needs accepted justification `c(a,b)=true ↔ R(d(a),d(b))` at the complete parameters; `DecidableEq T` alone is insufficient. A declared opaque computational comparison answers that same fixed relation and is judged by independent acceptance, without supplying its proof. Preserve all admitted questions, including newly readable inverses, through independently assessed interpretation changes. **Supporting checks:** execute the same question with or without requested audit export; preserve every failure meaning and fix measured runtime obstructions to the required computations without hiding them by changed questions or budgets. |
| **KM9 — Independent extension within the promised mathematical scope** | After KM1–KM8, complete the prescribed frozen independent trials for new objects/old operations, new operations/old objects, group-valued constructions, refinements, competing comparisons, reindexing, nonidentity presentation change, dependent application/admission/binders, complete structured results/lifts and leaf replacement. Each extension is interpreted and computed with its full mathematical data, required higher compatibility and declared subsequent uses. Give the compositional argument for each claimed mechanism; finite examples supplement it. Contributors use published interfaces, and the fixed kernel, contract, old objects and old leaves receive zero accommodating changes. A required repair means failure, refreezing and affected reruns, not exemption. |

For KM2–KM8, apply the [CC-HIGHER input/use boundary](computational-core.md#higher-input-computational-use-and-justified-reduction)
inside the construction's existing work: identify its accepted full diagram and extension,
the actual operations demanded by its continuation, and any theorem licensing a strict or
truncated consumer. KM9 assesses the corresponding preservation and existing independent
observations. The ordinary first RX-LIFT does not prove general higher coverage; a missing
higher input blocks its actual dependent construction, without introducing a separate
foundation project or relaxing any fixed question. #82 owns unresolved higher inputs and
#23 locates their consumers; no new issue queue or serial gate is added.

#### Supporting source locations and historical engineering checks

The [prior source-specific KM table](https://github.com/dzackgarza/lean-cas-dsl/blob/479d9bceb318a8966c95b3d1f9c19e68b9e03534/specs/computational-core-plan.md#concrete-kernel-implementation-work--exhaustive-within-the-declared-b0-scope)
is preserved at its inspected revision. Its `b0/kernel` locations and reported defects are
implementation leads to reproduce on the current candidate, not a second work order.
The mathematical cases and supporting build, source-removal, codec, performance and failure
obligations are retained in KM1–KM9, #66/#69/#24 and the acceptance table below. The selected
source determines which legacy path actually remains; historical locations do not require
reimplementing already adequate machinery.

#### Existing source and mathematical input dependencies

The checked reachable-route implementation (`completeRoutes`), proof-only classifier
construction (`ProofRefinement.construct`), prescribed lift-field computation
(`executePrescribedLift`) and per-assertion trace machinery already exist in earlier
integration source. Consume and validate them at the actual candidate; do not recreate them
merely because their consumers remain incomplete. Earlier K1 holds do not establish current
integrated acceptance. #66 owns the complete selected interpretation and its preservation,
with execution/export and measured performance repairs supporting that mathematical work.

The power-series object and constructor-induced comparison-cell interfaces have existing
upstream work in PRs #93/#94, as distinguished in the current dependency section. They are
not absent mathematics to reinvent, and presence on the selected branch does not establish
their independent acceptance or availability on latest main. Exact missing input blocks its
dependent construction only.

**Outside this V1 work:** K13's bulk registration programme, exhaustive Sage/GAP method
parity, broad production backend expansion, new mathematical surface beyond the existing
assignment, rebuilding the notebook frontend and unrelated administrative/optimization work.
K3/K14's complete readings belong to KM3; their remaining owner admission and full backend
coverage remain in the stronger full-B0 obligation. Required V1 real-engine workflows,
notebook execution, fixed positives and protected negatives are unchanged.

#### Single exit condition

**The kernel MVP closes when KM1–KM9 hold together**: every admitted B0
expression either has its independently fixed valid semantic reading
and a *fully specified runnable computational request*, or has an
independently justified invalid/ambiguous reading; all supported generic
transport/construction cases and complete reply shapes work; a missing
implementation affects only the computation outcome; and independent
fresh extensions demonstrate closure under the declared mechanisms with
the source frozen. Full B0 remains a separate, stronger delivery requirement:
the specified computations must still execute through registered engines
and satisfy their fixed mathematical assertions. A finite suite alone does
not prove genericity; the structural/compositional arguments and negative
counterexamples in KM2–KM9 are essential.

### Kernel construction procedure (owner instruction, 2026-10-21)

**Owner V1 assignment, 2026-10-23.** The current assignment explicitly authorizes
kernel delegation, targeted upstream interface work, computational-contract changes,
necessary execution-surface repairs and publication. Those authorizations supersede
the older procedural restrictions below where they conflict with finishing V1.
Mathematical ownership, leaf blindness, permanent assertions and independent
acceptance remain binding. Implementation authorship cannot accept its own
mathematics or interpretation migration.

The integrated candidate must also execute at least four useful connected real-CAS
workflows across at least three areas: exact selected arithmetic, finite sets and
constructions, polynomial algebra, linear or structured algebra, and transport or
inherited operations. The executed set must include complete structured data used
in a subsequent operation and a nonidentity transport. Reuse existing real engines
and narrowly scoped independent diagnostic leaves. This functional demonstration
and the ten frozen-candidate exit trials are required for V1; a compiling source
tree or a protocol self-test alone does not complete it. Broad leaf expansion and
unrelated notebook work remain outside scope.

Use this procedure subject to the current delivery sequence above and #10. Its older
priority wording does not override the coupled #66/#69 construction trial, deletion of its
superseded paths, or the distinction between the first executable dependency closure and the
final combined build. The applicable ownership, question-preservation and independent
acceptance requirements remain in force; no admitted assertion or completion requirement
changes with this ordering correction.

For local development, [#83](https://github.com/dzackgarza/lean-cas-dsl/issues/83) and the
[#74 disposition](https://github.com/dzackgarza/lean-cas-dsl/issues/74#issuecomment-6468597360)
govern through the single sequence in [Running checks](#running-checks). Local feedback does
not wait for source publication or CI. Explicit red source checkpoints preserve work without
claiming verification, completing an obligation or bypassing independent acceptance.

The former diagnostic criterion was *no admitted assertion stopping at a
request-formation gap*: an entry of kind `gap` whose detail does not begin
`NoImplementation: no admitted registration computes`. The 2026-10-20
report at `5410e70` had 154 entries: 18 holds, 101 request-formation gaps,
26 registration gaps, 6 invalid and 3 unavailable. That criterion remains
necessary under KM3, but it is **not kernel readiness**. The kernel is ready
for substantive leaf work only after KM1–KM9, including the frozen-kernel
independent trials and question-preservation assessment; full B0 execution
and independent acceptance remain obligatory.

Controller, custodian, review, publication and CI work (construction directive A) ordinarily
belongs to a separate session authorized by an owner instruction that names it, following
directive A. The explicit #83/#24 assignment includes local development tooling and the existing
build/cache integration in this kernel work, as specified in [Running checks](#running-checks).
That assignment does not transfer independent mathematical authorship, evaluator installation
or acceptance authority. A kernel session that finds a defect outside its assigned scope writes
one line under "Noticed, not worked" (rule 1).

#### Rules

Each rule names an observable condition and the action it requires. None depends on judging
how important, small, risky or promising something is.

1. **Selection.** Follow #10's selected mathematical construction across the
   relevant KM1–KM8 obligations: exact inputs and interpretation, executable
   construction/comparison/defining-map use, then its preservation argument
   and independent public use before expansion. #66 and #69 proceed together;
   do not complete an entire reader or legacy build before replacing the paths
   that obstruct this computation. KM9 is the final independent frozen-kernel
   gate. The older K1–K14 assertion-ID
   rows below identify precise regression examples and protected B0
   obligations, **not an alternative work-selection queue**.
   Within an active KM task, use the relevant K IDs and targeted probes
   to locate and verify the generic fix; do not move to a particular
   backend implementation just because its ID is next. K13's bulk
   registrations and the leaf-owned execution/admission portions of
   K3/K14 are excluded. An actual generic defect exposed by a K1
   computation remains kernel-owned under the applicable KM task.
   Missing independently authored upstream mathematics/acceptance
   blocks only the particular dependent KM mechanism; continue the
   next available kernel mechanism. At completion of KM2–KM8,
   re-evaluate KM1 on the integrated tuple and run KM9; every
   component must pass. A defect unrelated to the selected KM
   mechanism is recorded once in `HANDOFF.md`, not opportunistically
   patched.
2. **Write set.** An ordinary kernel-mechanism item's source changes only: `CasCatalogue/`, `CasGates/`, `CasTools/`,
   `CasAcceptance/*Probes.lean`, `CasAcceptance/Strata/`, the existing
   owning `specs/reuse/cc-*.md` or `specs/reuse/K<n>.md` (and
   `specs/reuse/KM<n>.md` only if a genuinely new KM-specific Lean
   definition requires a reuse record), `JOURNAL.md` (rule 9) and `HANDOFF.md`
   (rule 9); and, when the item's request form needs it, `CasContract/` in
   `lean-cas-dsl-leaf-contracts`. Publish the compatible contract through its owner and record
   it for integration; local edits, diagnostics and red checkpoints do not wait for that
   publication. Other paths and repositories are outside that item's ordinary scope:
   `custodian/`, `.github/`, `scripts/`,
   `justfile`, `tests/acceptance/`, `CasAcceptance/Permanent/`, the rest of `specs/`, hooks, CI,
   leaves, `lean-categories`, containers and every other repository. If the next edit is there,
   it is not this item's work unless an explicit owner assignment includes it. The #83
   development-tooling and #24 build/cache integration assignments include their existing
   owning instructions and execution configuration; they do not change mathematical ownership,
   protected acceptance or the scope of a kernel mechanism.
3. **Refused or unavailable operations.** When a commit hook, push, CI job, controller or reviewer
   refuses an operation, or a backend (`CAS_SAGE_PYTHON`, `CAS_GAP_PYTHON`) fails to start, write
   the exact command and its error under "Owner actions" in `HANDOFF.md` and continue. A backend
   that fails to start marks the item `blocked: engine <name>`. Never edit a gate, hook,
   controller, workflow or recipe to get past a refusal, never bypass one, and never build,
   install or recreate an engine or container. A refused push leaves the commits on the local
   branch.
4. **Performance.** Measure the current edit-to-result path: startup, completed diagnostics,
   required artifact rebuild, preparation, execution, export and memory separately. Diagnose
   a persistently slow focused check or an internal timeout at its owning boundary; do not
   fill the wait with unrelated edits or raise heartbeats. #83 authorizes this work within
   the existing #66/#24 allocation. Use the selected environment and existing profiler or
   driver, without a diagnostic command silently refreshing dependencies or changing budgets.
   Split a compilation boundary only when measurements justify it; preserve dynamically
   discovered registry imports and the original behavior. No file-size or check-count quota
   substitutes for that evidence.
5. **Verification and checkpoints.** Follow [Running checks](#running-checks) for the edited
   source. A checkpoint may be explicitly labelled red/source-only with failed or unrun
   stages recorded in its commit or existing work record. It preserves source without
   claiming a completed diagnostic, fresh artifact, runtime result or acceptance. Neither
   publication nor a full-suite run is a prerequisite for that checkpoint or local feedback;
   protected publication and acceptance gates remain in force at their actual boundaries.
   When reporting a verified repair, name the relevant unchanged assertion IDs or exact
   existing generic check, the source/environment used, the observed result and evidence path.
   Do not invent IDs or treat one passing probe as the whole KM gate. Compare before/after
   runtime reports with the same mathematical/dependency inputs, package selection and manifest,
   identifying the kernel source and artifacts separately for each run. If those inputs change,
   rerun the required comparison on the new dependency environment. Compare every entry's
   mathematical question;
   a changed question cannot close without independent assessment of the unchanged assertion
   (rule 8). Source-ready, published and verified are distinct states.
6. **Causal review when repairs stall.** Repeated changes that do not advance the intended
   computation require reconsidering the shared mechanism before another symptom patch.
   Inspect the unchanged failing question, completed diagnostics, actual stage results and
   relevant diffs; use a fresh read-only review when it helps challenge the diagnosis.
   Check whether missing producer/action retention or an invented prerequisite is generating
   the repairs. Record the causal finding in the existing owning document and resume the
   required construction. Red checkpoints do not count as progress or suppress this review;
   neither a commit counter nor an easier successor replaces the original obligation.
7. **Item identity.** A K assertion item is its ID set, not the
    current detail. Moving an ID to another request-formation error
    does not close it. A K assertion item closes when every ID meets
    its row's condition in one candidate report; a targeted report
    can establish *that item's* condition. A KM gate closes only
    after **all** evidence required in its own row has passed on the
    combined candidate. No K item, compile, or isolated probe
    substitutes for that evidence. A later contradictory full report
    reopens the affected claim.
8. **Blocked items.** An item is blocked only when its next step needs an input owned by another
   role (formalization, acceptance, leaf) or an owner operation. Then:
   - mathematics: if the item names an upstream row, start the formalization subagent in a
     `lean-categories` checkout with that acceptance-table row's text and its cited sources,
     verbatim and nothing else (the owner's instruction of 2026-10-20 that such inputs are
     delegated to a subagent). If the item names none, write the missing input under
     "Owner actions";
   - an interpretation or question change: start the acceptance subagent in its own checkout with
     the admitted assertion text and its cited sources only;
   - registrations: K13 is post-KM9 production work; before KM9 use
      independently authored *diagnostic* leaf specimens only when needed
      to validate the published contract or a generic kernel mechanism;
   - write `blocked: <exact missing input>` next to the item in `HANDOFF.md` and take the next
     item.
   The session does not end while a subagent it started is running. When one finishes, run
   `just track-main` in the work worktree when consuming its dependency input, record the
   actual selection and commit `lake-manifest.json` if it changed. Rebuild affected imports,
   restart their persistent consumers, rerun the targeted check of each item blocked on that
   input, and resume selection
   at rule 1. Nothing waits for a subagent: the session keeps working the work list while it
   runs. The session ends when every item is closed or blocked and no started subagent is
   running, or when the owner stops it.
9. **Records.** Write one `JOURNAL.md` entry on closure of an
   implementation unit, at most ten lines: KM owner, relevant assertion
   IDs and outcomes if present, otherwise the precise generic probe
   and its observed result, candidate commit and evidence path.
   Commit `HANDOFF.md` only when a unit closes or is blocked,
   after a refusal (rule 3), or at session end (rule 11).
   Implementation and gate states are kept in `HANDOFF.md`;
   this plan fixes requirements, not writable completion claims.
   Write no other administrative report or agent-memory record
   during a kernel session.
10. **Checkouts.** Reuse the assigned worktree on the construction branch `HANDOFF.md` names
    for editing, persistent diagnostics and targeted checks. When a separate worktree is
    needed, create it outside the repository (`git worktree add ../lean-cas-dsl-kernel <branch>`).
    Preserve the checkout, selected dependencies, artifacts, Lake traces and logs in the
    authorized durable workspace. Never run `git stash`, `checkout`,
    `reset`, `restore` or `clean` in `/home/dzack/gitclones/lean-cas-dsl`; its working tree holds
    the owner's uncommitted edit. Where checkouts share a Lake package directory
    (`packagesDir` in the lakefile), a different manifest can move those packages to another
    revision and invalidate dependent artifacts. Respect the selected-package wrapper and
    preserve that environment. Run no `lake` or `just` command in the owner's checkout, and run
    `just track-main` only where "Running checks" says.
11. **Handoff.** At session end `HANDOFF.md` contains only:
    the branch and commit, pushed status or exact error; latest CI
    report (run id and artifact); KM1–KM9 status as open, closed
    *with its required evidence*, or `blocked: <exact input>`;
    the K assertion IDs relevant to any outstanding KM mechanism;
    "Noticed, not worked"; "Owner actions". Do not name a `/tmp`
    path or ephemeral worktree as the only location of anything
    the next session needs.
12. **Claims.** Cite the complete per-ID report for a K assertion
     item. Cite every compositional argument, probe, coherent source
     result and independently run frozen-kernel trial required by the
     corresponding KM row before claiming kernel readiness. Source
     review, a compile, a benchmark, or a reduction in gaps alone
     cannot establish the milestone.

#### Running checks

**Current local development sequence (owner #83, 2026-10-29).** This is the single
local-check sequence used by `AGENTS.md` and the construction rules above. It implements
[#83](https://github.com/dzackgarza/lean-cas-dsl/issues/83) with the source-checked
[#74 disposition](https://github.com/dzackgarza/lean-cas-dsl/issues/74#issuecomment-6468597360).
The current work is still #10's coupled #66/#69 trial; earlier compiler feedback and #24's
build/cache work support that computation. Publication, a green legacy aggregate build and
completed CI are not entrance conditions for local feedback.

**MCP setup in the actual worktree.** The repository's [`.mcp.json`](../.mcp.json) uses
the [upstream standard stdio configuration](https://github.com/oOo0oOo/lean-lsp-mcp#3-configure-your-idesetup)
(`uvx lean-lsp-mcp`, `LEAN_PROJECT_PATH=.`). Start a client supporting project `.mcp.json`
from this worktree's root, with `uvx` and the selected Lean/Lake on its inherited `PATH`;
other clients use upstream's equivalent configuration. Keep the session alive and request
`lean_diagnostic_messages` for the edited file, waiting for the completed current-source result
as below. For already selected dependencies outside Lake's default package location, copy or
symlink the existing Lake `--packages` JSON to this worktree's `.lake/package-overrides.json`
before starting the server. [Lake loads these workspace overrides](https://github.com/leanprover/lean4/blob/v4.33.0/src/lake/Lake/Load/Resolve.lean#L584)
in nested `setup-file` calls; a `PATH` wrapper's `--packages` option alone does not propagate
there. Reuse the recorded selection during diagnostics without `lake update` or `just track-main`;
changed imports still require the rebuild/restart in step 3.

**Memory during targeted builds.** Keep the Realize worker open across edits, completed
diagnostics and hover/reference queries. On a memory-constrained host, finish those requests,
then request `lean_diagnostic_messages` for `CasCatalogue/FileItems.lean` before building.
The configured [`LEAN_LSP_MAX_OPEN_FILES=1`](https://github.com/oOo0oOo/lean-lsp-mcp/blob/v0.31.0/src/lean_lsp_mcp/config.py#L63-L73)
makes the [idle-file eviction in leanclient 0.13.2](https://github.com/oOo0oOo/leanclient/blob/v0.13.2/leanclient/aio/client.py#L574-L589)
send `textDocument/didClose`; [Lean 4.33 terminates that file worker](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Server/Watchdog.lean#L1277-L1278).
FileItems imports only Lean. Verify the Realize worker exits and record memory plus the unchanged
MCP/watchdog PIDs before starting the targeted build. Pending requests and pinned scratch
documents are excluded from eviction. The server stays alive; closing Realize discards its
file elaboration state, so measure reopening separately from warm edits. Use step 3's targeted
command: MCP `lean_build` runs the whole build and restarts the shared Lean client.

**Observed memory cost (2026-10-30, #83).** The isolated original `Realize:olean` build at
`922920b` completed in **463.365 seconds**, with **6,645,140 KiB** peak child RSS
(`issue83-targeted-artifact-build-02.json`). The preceding LSP snapshot summed to about
**5 GiB RSS** across its processes; this host's cgroup limit is **8 GiB**. The earlier overlapping
build exited 137, and the cgroup recorded an OOM kill. These observations support overlapping
LSP/compiler memory as the cause; summed RSS includes shared pages and does not establish an
exact simultaneous memory peak. Measure release and the next build before claiming this sequence
prevents the failure or improves elapsed time.

1. **Inspect the actual declarations.** Use declaration search, hover, references and source
   from the selected worktree and its actual dependencies before changing an application or
   interface. Run the existing Lean language server through `lean-lsp-mcp` against that
   worktree and package/toolchain selection; keep it alive across edits. Do not guess a
   signature from a stale branch, a printed name or a remembered implementation.
2. **Edit and obtain completed local diagnostics.** Wait for diagnostics corresponding to
   the current source version, and retain the actual error or completed result. A request
   still processing, an empty partial response or a timeout is not a clean diagnostic.
   When the existing editor/MCP client cannot operate in the assigned worktree, record the
   observed access/setup failure and use the existing focused module build as the evidenced
   fallback. Installing or configuring the official tooling remains implementation work;
   writing a bespoke client is not a prerequisite. Lean's server can expose executable-
   declaration compilation failures as well as elaboration errors. Its completed diagnostics
   do not by themselves establish fresh module artifacts, downstream execution or native linking.
3. **Build the artifacts the downstream consumer needs.** After an imported module changes,
   use the selected environment's targeted `lake build Module:olean` or other actual required
   target. Rebuild its affected imports, then restart dependent file/runtime workers before
   attributing a result to the edit: imports are loaded once per file-worker process. Reuse
   an existing worker for repeated specimens only while its compiled imports remain unchanged.
   A behavior that depends on C compilation, linking or native execution needs the corresponding
   focused native check. Preserve Lake's artifacts and traces so it can reuse unchanged work.
4. **Run the unchanged failing question and protected negatives.** Use the existing downstream
   driver/harness through the production path with fresh compiled imports. Preserve the original
   prerequisite bindings and their order, imports, mathematical parameters and comparisons,
   shared execution session/state, and the original budget. Keep preparation, execution and
   requested export results separate. For `cas-harness`, supply `--suite` and `--inventory`
   for the selected original scope. A scratch selection may omit unrelated questions only
   while retaining that complete context; otherwise feed the original file to the existing
   selection mechanism. `#cas_tests` takes a file/directory, not a one-ID selector, and separate
   standalone `#cas` commands each start a fresh scope/harness: they do not demonstrate retained
   cross-command computation. Keep integrated drivers downstream of `TestSuite`/`Realize`;
   importing `TestSuite` into `Language` or `Realize` creates a cycle. Temporary same-file checks
   use only APIs already available there. Run the relevant protected negatives on the same
   candidate, preserving their original assertions and failure meanings.
5. **Run broader integration asynchronously.** The configured candidate/full-suite workflows,
   complete combined build, real engines, notebook consumers and independent frozen trials
   remain required at their prescribed delivery/acceptance boundaries. They are not routine
   local-commit checks. Inspect actual reports and stages reached; a missing or failed stage
   supplies no passing result. Source checkpoints, publication, compiler feedback and runtime
   verification remain distinct from independent mathematical acceptance.

An explicitly labelled red/source-only checkpoint may precede successful diagnostics, artifact
build or execution. State failed and unrun stages in the commit or existing work record without
claiming verification or bypassing a protected gate. Resume the failed local step on that source.
Checkpoint frequency is not progress evidence; repeated symptom fixes still require the causal
review in rule 6. Do not substitute an easier question, different state or larger budget, or
fill a slow check's wait with unrelated changes. A targeted result establishes only its actual
scope; all evidence in the corresponding KM row remains necessary for closure.

**Environment and dependency boundaries.** Keep checkout, dependencies, compiled artifacts,
Lake traces and diagnostic logs in the existing authorized durable workstation or remote
workspace, and use existing process/session tools so a build can continue independently of the
chat connection. Verify access and persistence rather than inferring them from installation.
Use native Git where the environment permits it. A new host, a bespoke server or a new authority
controller is not a prerequisite for this local sequence.

Consume own-organisation dependencies at latest `main`: run `just track-main` in the assigned
worktree at session start and when consuming a completed role's dependency input (rule 8), and
resolve latest-main inputs at the prescribed integration-build and full-harness boundaries.
Record actual checkouts, package overrides, toolchain and manifest in the existing provenance.
Local LSP diagnostics, targeted builds and focused runtime commands add no dependency refresh.
Keep one comparison on the same selected dependency environment; when its inputs change,
rebuild/restart the consumers and rerun the affected comparison. A persistent process must identify the
mathematical environment it actually imported, not acquire a new label from a mutable manifest.
`just focus`, `just probe`, `just bench-question` and `just bench-reading` are not substitutes
when their update/limit behavior changes that environment or the original question's budget.

**Evidence required for #83.** Demonstrate a real production edit, completed diagnostics for
that edit, a fresh downstream result with the required context and negatives, and actual artifact
reuse. Record cold startup, warm edit-to-completed-diagnostics, required dependency rebuild,
preparation/execution/export and memory separately in the existing work record. Tool installation,
a no-op build, a pre-edit runtime baseline or this policy update establishes only its stated
scope; none establishes the complete persistent setup or closes #83. Diagnose measured swapping,
serial elaboration or startup costs at their causes. Module extraction requires measured benefit
and retained behavior, including dynamically discovered registry semantics; no line quota or
wholesale split mandate is introduced.

**Integration ownership.** Under #24, compile named production modules before engine installation,
then retain engine-dependent probes, integrated consumers and native tools. Use standard cache
actions to restore the actual selected artifact directories before compilation and save after
the build produces them, preserving toolchain/dependency identity and Lake traces. Measure a
subsequent restore/reuse before claiming a speedup. This is existing build/cache integration,
not another framework or a prerequisite for local diagnostics.

**Historical observations.** The following measurements and workflow descriptions record their
inspected sources and host. They are not present-day timings, universal memory limits or local
commit/check quotas. Use current measurements and actual workflow source for current decisions.

- **Gates and candidate CI were distinct in the inspected workflow sources.** [`gates.yml`](../.github/workflows/gates.yml)
  triggers on non-Markdown pushes to `main`/`b0/**` and explicit dispatch. Its acceptance job
  runs base/head reports and publishes `acceptance-report` when the files were actually
  produced. **Workflow source matters:** main at `1d5b06c` has no Sage/GAP installation
  step; the candidate branch's Gates definition adds engine setup but retains those branch
  filters. Do not credit main's job with that unintegrated setup or assume either definition
  runs on every integration-branch push.
  The [candidate workflow](https://github.com/dzackgarza/lean-cas-dsl/blob/work/kernel-v1-20261023/.github/workflows/kernel-v1-candidate.yml)
  runs on `work/kernel-v1-20261023` with its committed manifest, configures real engines,
  and publishes `kernel-v1-candidate-<sha>-<attempt>` engineering records. That diagnostic
  tuple is not evidence of compatibility with the latest-main delivery inputs.
  Inspect the actual report and stages reached: failed compilation can prevent export,
  workflows and notebook execution, and missing reports are not inherited passes or zero
  gaps. Documentation-only commits supply no fresh computational verdict. Use the latest
  applicable completed evidence when selecting/closing work; an unrelated source-check or
  custodian result is not a Lean build or acceptance result. A refused push is rule 3.
- **Measured cost of one check (2026-10-21, then-current host).** Harness startup mapped 3.9 GB of
  imports: 30 s with a warm page cache, about 110 s cold, and any build evicts that cache. Each
  assertion then costs 10 to 30 s of CPU, more when it dispatches to a backend. Kernel C is
  compiled at `-O0`, which makes a full kernel C rebuild and link take about 70 s instead of
  about six minutes. Elaborating `Language.lean` (then about 5,500 lines) took several minutes,
  and an edit to it or to `Trace.lean` rebuilt its dependants. Those observations motivated
  focused checks; the current question and protected negatives determine their scope.
- **Observed memory contention on that host.** The machine had 7 GB of memory; each harness
  process mapped about 2 GB of imports, and concurrent harness/build work swapped and slowed
  checks several-fold. Respect current resource constraints and measure contention before
  parallelizing heavy work; these old figures do not establish the current host's capacity.
- **Historical feedback targets (2026-10-21).** The instruction used under two minutes for a
  targeted check and a commit including hooks, under ten minutes for a push, and under six
  hours for asynchronous CI. These planning targets supply comparison context, not measured
  current performance or a restriction on starting the authorized #83 improvement work.

#### Work list

**Historical K1–K14 diagnostic and full-B0 inventory.** The current KM delivery order is
#10 and the current sequence above; this table is not a second queue. Preserve every required
behavior, but reproduce dated defects before treating their old details as current. "Kind"
is the entry's kind in the named computation-only report unless the row says otherwise.
A request-formation gap does not by itself mean the mathematical question is unreadable.

| Item | IDs (from the `5410e70` report) | Closes when |
| --- | --- | --- |
| K1 required computations | `sets.card.z4_cubed`, `sets.card.z7`, `sets.card.z5_empty_power`, `sets.card.fin2_times_z3`, `sets.card.integers`, `sets.finite.integers`, `sets.finite.fin2_times_z3`, `sets.implemented.card_fin`, `sets.card.fin2_sqcup_fin3`, `sets.eq.rev_rev`, `sets.limit.pullback.card`, `finite_sets.limit.pullback.card`, `lattices.discriminant.a1`, `lattices.discriminant.a2`, `lattices.discriminant.a3` | every ID holds with at least one dispatch |
| K2 invalid inverse readings | `inverses.value`, `inverses.solve`, `inverses.left`, `inverses.right`, `inverses.det` and the `(statement)` entry of `inverses.cas` | no ID is invalid. Their earlier questions are empty, so every reading is a question change (rule 5). Upstream row: `core-admission-realized` |
| K3 required positives | the assertions of `tests/acceptance/b0-required-positives.cas.proposed` | every assertion holds through registered execution, run unchanged, with its protected negatives. None is admitted yet: once all hold, K3 is `blocked: admission operation (owner)` until admitted |
| K4 membership and containment judgments | `algebras.polynomials_several`, `algebras.polynomials`, `schemes.affine_line`, `schemes.affine_space`, `calculus.taylor_exp`, `calculus.taylor_sin`, `composed.root_one`, `differentials.member`, `ellipses.even_square`, `ellipses.odd_square`, `ellipses.prime`, `ellipses.not_prime`, `factorization.approximation`, `finite_sets.member`, `finite_sets.not_member`, `finite_sets.subset_union`, `finite_sets.intersection_subset`, `comprehension.typed`, `comprehension.image_typed`, `comprehension.even_member`, `comprehension.odd_not_member`, `fractions.member`, `fractions.sqrt_member`, `subspaces.member`, `subspaces.not_member`, `numbers.containments`, `numbers.containments.transitive`, `numbers.membership.zmod`, `numbers.membership.negative`, `polynomials.variable`, `polynomials.member`, `polynomials.irrational_roots`, `several_variables.variable`, `several_variables.last_variable` | every ID is not a request-formation gap in the computation-only report, or holds in the full report through Lean discharge. Expect question changes (rule 5) |
| K5 closed elements as request data | `calculus.integral_square`, `composed.composition`, `integration.normalized_count`, `integration.normalized`, `integration.differential`, `integration.derivative`, `integration.at_zero`, `finite_sets.union`, `finite_sets.intersection`, `finite_sets.difference`, `finite_sets.symmetric_difference`, `fractions.halves`, `fractions.cancel`, `fractions.modulus`, `functions.extensional`, `functions.at_zero`, `functions.at_three`, `functions.even`, `numbers.complex.re`, `numbers.complex.im`, `numbers.complex.bar`, `numbers.complex.norm`, `numbers.complex.abs`, `polynomials.at_minus_sqrt2`, `series.coefficient_two`, `series.coefficient_three`, `series.coefficient_zero`, `series.coefficient_four` | no ID is a request-formation gap |
| K6 operands not formed by a catalogue operation | `composed.root_count`, `differentials.derivative`, `ellipses.naturals`, `ellipses.evens`, `ellipses.multiples`, `ellipses.squares_even`, `factorization.multiplicity_two`, `factorization.multiplicity_three`, `factorization.multiplicity_seven`, `comprehension.elements`, `comprehension.card`, `comprehension.even_card`, `comprehension.image_apply`, `comprehension.image_method`, `matrices.product`, `matrices.juxtaposition`, `matrices.application`, `matrices.det`, `matrices.rank`, `matrices.kernel`, `matrices.trace`, `matrices.charpoly`, `numbers.gcd` | no ID is a request-formation gap |
| K7 maps without an observation decoder | `numbers.integers.sum`, `numbers.zmod5.sum`, `numbers.zmod5.product`, `numbers.zmod5.negation`, `numbers.zmod5.difference`, `numbers.zmod7.distributive`, `numbers.zmod7.value`, `numbers.rationals.sum`, `several_variables.dimension`, `several_variables.plane` | no ID is a request-formation gap |
| K8 remaining request-formation gaps | `differentials.at_two`, `polynomials.root`, `factorization.prime_factors`, `fractions.lowest_terms`, `calculus.limit_sinc`, `calculus.limit_infinity` | no ID is a request-formation gap |
| K9 unavailable requests | `finite_sets.card_product`, `finite_sets.card_power_set`, `sets.card.square` | the kernel's request for each ID matches the contract's declared input form (then the backend error is leaf work and the ID leaves this item), or it is corrected so that it does |
| K10 comparison used in execution (`cc-cohere-exec`) | ring `cardinality` probe | the executed request records the comparison `cmp.rings.carrier` that selected its route; without that row the outcome is an ambiguity naming both routes |
| K11 route enumeration and reachable closure | `Resolve`, `Closure`, `Cohere` probes | no consumer silently relies on default route fuel; establish a finite reachable enclosure closed under the actual `edgesFrom` rules and derive the simple-route bound from its vertex count, or provide an adequate terminating complete alternative. Preserve explicit composites, distinct structures, selected comparison witnesses/directions and ambiguity. Any cycle reduction needs its actual comparisons and a witness-preserving justification. Resource exhaustion reports incomplete closure discovery. Remove safeguards only with a sufficient replacement argument and implementation; no universal cycle-to-identity or non-increasing-measure registration rule is an upstream blocker. The named probes retain their intended outcomes |
| K12 constructor-induced comparison cells | the lift positive in `CohereProbes` | the probe resolves without ambiguity. Upstream row: `cc-cohere`; `blocked: lean-categories constructor action on comparison cells` until that input exists |
| K13 registration gaps (post-KM9 leaf dispatch; full B0 obligation) | `calculus.integral_sine`, `composed.root_sum`, `composed.root_product`, `composed.charpoly`, `composed.det`, `composed.trace`, `differentials.degree`, `differentials.differential`, `integration.primitives`, `factorization.over_complexes`, `finite_sets.card`, `lattices.rank.a1`, `lattices.rank.a2`, `lattices.rank.a3`, `lattices.card.a2`, `lattices.card.a0`, `subspaces.dim`, `subspaces.kernel`, `polynomials.degree`, `polynomials.factors`, `polynomials.degree_over_rationals`, `polynomials.at_sqrt2`, `polynomials.no_rational_roots`, `sets.apply.rev`, `sets.apply.rev_rev`, `several_variables.total_degree` | the leaf subagent, started once in a `lean-cas-dsl-leaves` checkout with the released contract and the operation ids and input forms named in these details (never the assertions), has finished, and no ID is a registration gap or a request-formation gap. A wrong or unavailable answer is the leaf's outcome, not a kernel item |
| K14 formed-module positives | the assertions of `tests/acceptance/b0-formed-positives.cas.proposed` | as K3 |

Every CI report re-checks K2 and the closed request-formation items; K1 and K3 need the
backends, so their targeted checks are rerun whenever another item closes. A reopened item
is reported against its owning obligation and preempts the selected construction only when
it blocks that construction or invalidates its required evidence. K numbering does not
create a competing repair queue; every regression remains visible and required for completion.

The K1–K14 table is retained as the concrete B0 assertion/diagnostic
inventory; checking its rows does not by itself prove readiness. Kernel MVP
requires KM1–KM9, **including** independent frozen-kernel trials and question
preservation, *before* mass K13 leaf work. Full B0 still requires all real
computations and protected negatives.

### Stage A

Stage A constructs a usable integration workflow as well as a buildable candidate.
The legacy workflow is not a prerequisite for its replacement.

Source construction, focused validation, publication, and final B0 acceptance are
distinct operations. Failure or unavailability of one blocks only its actual
dependants. In particular, documentation publication does not depend on fixing
mathematical assertions that its changes do not affect.

The approved stage-A changes include separating compilation from acceptance
execution, replacing the downstream catalogue inventory with faithful derivation,
correcting the outcome model, and correcting the controller that obstructs these
changes. Their implementation requires no renewed owner decision.

The controller worker receives the current construction mandate immediately.
Its work does not wait for the mandate's documentation commit to reach main.

The construction branch and commit are the ones `HANDOFF.md` names. During construction, `main` is integration source, not an accepted baseline release. Ordinary
source integration is distinct from advancing the independently accepted evaluator or mathematical
release. Publication uses the authorized repository operations; this text neither verifies nor
changes hosting protections. The mathematical release remains explicitly pinned and independently
assessed.

**Tracking disposition (2026-10-28 UTC):** #63 and #64 are superseded source references, with
their branches preserved at `87dc4ef8011d17fd0c5c410fc8430fdb91a598d5` and
`c3a9613181d5844c1af14de4ebd015bca4bb6452`. #67 is the sole integration vehicle.
Binder and interpretation controls continue in #66/#24; complete lift, defining-map,
diagram-transport and failure controls continue in #69/#24. Tracking closure is not merge,
implementation completion or acceptance. The older comparison below explains what to retain.

Outside a kernel session (which follows the kernel construction procedure), reconcile outstanding branches by their existing obligations, not as a merge queue (comparison at
#65 `cbe4f174`, #63 `f805933`, #64 `5fd3f924`):
- [#63](https://github.com/dzackgarza/lean-cas-dsl/pull/63) and
  [#64](https://github.com/dzackgarza/lean-cas-dsl/pull/64) are divergent reference branches, not
  ancestors already incorporated into #65. Preserve their work until its obligations are
  accounted for in the consolidated candidate; no `#63 → #64 → #65` merge prerequisite exists.
- #63's generic-binder obligations remain: zero/multiple applicable rows, row-local refusal with
  alternate rows in both orders, distinct selected structures on a common carrier, token
  separators, and evidence at the actual domain. #65 has a different binder implementation;
  retain those regression behaviors without restoring the older reader wholesale. Its upstream
  independent assessment and the six interpretation-transition findings remain requirements of
  the chosen tuple, not instructions to replay the retired sequence of pins.
- #64's obligation is a complete lifted result in its own category, with defining maps and the
  correct image along the exact registered functor. #65 replaces the old cone-carrying `Wire`
  with `StructuredResult.Result`; reconcile the invariant, diagram transport, failure strata
  and real finite-set pullback execution there. Do not transplant the old decoder API or count
  `universal := none` as a completed structured result. The replacement does not require a leaf
  proof or a new runtime mathematical proof construction.

#65's pinned mathematics and contract are candidate inputs, not accepted because they are newer.
Assess the chosen compatible tuple independently; neither #63's old pin nor a historical hold on
an older pin defines a second target. Preservation of source does not accept that source.

### Acceptance table

These are the mathematical observations and compositional arguments for the existing row
identifiers. They remain subject to the full fixed inventory and independent evidence model.
The current KM1–KM9 table specifies their operative work; historical stage letters do not
create a second queue. Necessary engineering observations are listed separately.

| Existing row | Mathematical obligation | Required observations and argument |
| --- | --- | --- |
| `b0-typed-application` (CC-CALC, CC-SEP) | Apply the declared dependent operation to its complete parameters and arguments, retaining its domain hypotheses and resulting source/target. | All admitted operands have their independently intended types; an out-of-domain argument is not admitted. Substitution respects the dependent signature. Unresolved metavariables are not completed mathematical data. |
| `b0-selected-structure` (CC-CARRIER, CC-SEP) | Retain the selected structured object, rather than only its underlying carrier. | The existing two forms on one module and `Maps`/`Vec` on one carrier keep their distinct structures. Carrier equality or the first transparent alias that unifies does not select one. |
| `core-admission-realized` (LC-18) | Use the accepted admission domain, map and evidence for the actual question. | The fixed `(3 in ℚˣ)⁻¹ = 1/3` is admitted; `2 ∈ ℤˣ` fails its required unit condition. Failure to obtain evidence alone is not a proof that a mathematical condition is false. The kernel neither invents the domain nor reshapes the obligation to fit its tactic. |
| `b0-domain-preservation` (LC-14) | Preserve the admission's actual domain and maps through composition and later application. | The resulting morphism is at the selected mathematical domain; an incidental carrier or execution presentation does not replace it. |
| `b0-binders` (#46, [binders.md](binders.md)) | Interpret a binder as its declared dependent mathematical operation, retaining its variables, domains and parameters. | Preserve the complete fixed readings of `calculus.limit_sinc`, `calculus.limit_infinity`, `calculus.integral_square`, `calculus.integral_sine`, `series.*`, `composed.root_sum` and `composed.root_product`. One interpretation of the accepted binder interface covers its instances; an operation-specific syntax case does not establish it. |
| `cc-resolve`, `cc-closure` (CC-TRANSPORT, CC-RESOLVE, CC-CLOSURE) | Inherit an operation at the selected functorial image on its actual domain. Invariants defined on cores use the induced core action; arrow constructions use the induced arrow action. | The fixed lattice cardinality and `rank(A₂)=2` are obtained through the declared structural functors and the actual invariant domains, with no duplicate lattice operation. A structured return still needs its declared lift. K11's completeness argument and selected parameters remain required. |
| `cc-cohere`, `cc-cohere-exec` (CC-COHERE) | Use the actual comparison components and their required naturality/higher compatibility. A directed comparison does not automatically identify two interpretations. | The fixed ring cardinality diamond uses `cmp.rings.carrier` at the selected object; without the required comparison its competing interpretations remain ambiguous. Its selected nonidentity action and later use are computed where required. Order and backend availability do not select mathematical meaning. |
| `cc-fib` (CC-FIB) | Change parameters through the specified transport, with base, variance, selected lifts and coherence. | Along `u:ℤ→ℤ/4`, restriction sends a selected `ℤ/4`-module to `u* N` over `ℤ`. Extension is the distinct covariant construction and requires its own declared data. The mathematical argument is the supplied cartesian/cocartesian or other accepted transport structure, not matching parameter names. |
| `cc-realize` transport (CC-CARRIER) | Apply the accepted nonidentity comparison between selected presentations. | In the fixed `𝔽₃[x]/(x²+1)` and `𝔽₃[y]/(y²+y+2)` example, compute the specified `x↦y+2` translation and its later use. Distinct presentations are retained; neither that distinction nor field isomorphism decides an unspecified equality assertion. The admitted relation and chosen comparison govern. |
| `cc-lift`, `core-return-lifts`, `lc-lift-subobject` (CC-LIFT, CC-UNIV) | Return the complete construction through its declared lift, with source diagram, defining morphisms and comparison. | The fixed module kernel lifts to its declared formed-module construction with restricted form and actual inclusion, rather than only the bare module. This alone is not a categorical-kernel claim among form-preserving maps. A lifted cone is universal upstairs only under its accepted creation/lifting hypothesis. The existing successive-lift and second-shape observations use the actual supplied maps; missing lift computation remains a gap. |
| `cc-refine`, `cc-props` (CC-PROP, CC-DECIDE) | Form the accepted proof-only refinement while preserving the selected object and its defining structure. | `Fin 2 × ℤ/3` obtains its finite-set structure through accepted evidence; the fixed abelian/nonabelian questions about `ℤ/3` and `S₃` retain their meanings. A computed Boolean alone does not place an object in a refinement. |
| `lc-units-structure`, `cc-universal` (CC-UNIV) | Group-valued constructions have the group structure and any defining inclusion/action supplied by their accepted mathematics. | Inversion on `Mˣ` and the second existing group-valued construction follow from that interface, without a new operation declaration. The fixed `A₃↪S₃` observation includes cardinality 3 and its actual inclusion. A chosen subobject representative and its map are not replaced by its quotient class alone. |
| `cc-realize-2cat`, `cc-realize`, `cc-adapter`, `cc-backends` (CC-ACTION, CC-ADAPTER, CC-DECODE, CC-ROUTE) | Compute the independently fixed operation/composite and its complete diagram or arrow data. | Every required computational assertion executes at its selected meaning. Later operations use the supplied data and defining maps. A fused realization may compute the whole composite without each primitive registration, but cannot change that composite or its required comparisons. Formal laws remain independent of leaf answers. The historical node name does not impose a dimension-two ceiling. |
| `cc-observations` | Answer the admitted mathematical relation on denotations. | Preserve `\|(ℤ/4)^3\|=64` and the fixed comparisons. A kernel reduction to equality of decoded presentations requires its accepted upstream justification; presentation inequality alone does not imply semantic inequality. A registered opaque computation of the declared relation remains untrusted and independently judged. No form is presumed injective merely because its data equality is decidable. |
| `gov-meaning-permanence` | Preserve each independently admitted proposition/relation with its full parameters, selected structures and comparisons. | A changed reading is independently assessed against the unchanged assertion and sources. Text equality, equal Boolean answers or provability alone do not establish the same question. Incidental proof terms and revision labels do not by themselves change the mathematics. |
| `b0-trials` | Extend the promised constructions and operations with their full mathematical data and subsequent uses. | Complete the existing independent exit trials and construction-specific compositional arguments. Frozen kernel, contract, old objects and old leaves receive zero accommodating changes; a defect requires repair, refreeze and affected reruns. |

Supporting engineering and authority obligations:

| Existing row/check | Required observation |
| --- | --- |
| `b0-integration` (#59) | One compatible kernel, contract, mathematical input, probes, tools and runtime builds. The reader consumes the upstream semantic registry; the contract mirrors no semantic row kind and supplies registration/port/failure only. Compilation and mathematical acceptance remain distinct. A completed acceptance run reports every fixed assertion even when some fail. The old contract `ee14cce` is historical provenance, not the current dependency prescription. |
| `cc-failure-strata` | Preserve invalid/out-of-domain, ambiguity, absent realization, unavailable/crashed computation, malformed output, well-formed wrong answer and internal/resource failure through the pipeline. An exception or timeout never proves semantic invalidity. Check the actual current consumers; the previously reported `TestSuite.runFile` catch-and-relabel defect is a historical source lead, not an assumed current result. |
| Application/binder/codec checks | Generic interpretation retains full dependent arguments and actual hypotheses; no unresolved data is admitted. Published forms support encoding, decoding, hostile replies, exact endpoints and later use. Missing defining data is malformed; wrong mathematics in a well-formed answer is judged independently. |
| `b0-authority` | Preserve the established author/input boundaries and independently protected acceptance transitions. The existing authority section governs; this is not a mathematical object or a new prerequisite for unrelated construction. |

### Recorded construction observations (2026-10-02)

These are dated source and probe observations, not accepted row statuses. The cited checks have
not been re-established here at the consolidated tuple. No partial observation closes a row or
releases an acceptance dependency; that requires its full acceptance and independent judgment
at the specified tuple (architecture.md, policy 4).

| Row | Recorded observation | Evidence or blocking dependency |
| --- | --- | --- |
| `b0-integration` | check reported | main `3c8eaec`: build compiles without executing the suite; `cas-harness` reports per assertion; `check_acceptance_regression.py` |
| `cc-failure-strata` | check reported | `fc791e0`; `Outcome.ofException`; interpreter errors are `internal` (composed.* moved internal → invalid once typed application landed) |
| `b0-typed-application` | partial kernel observation | `1ae53ea`; RegistrationProbes. 8 admitted assertions still invalid: upstream evidence and `lim` domain, below |
| `b0-selected-structure` | check reported | `fa0a426`; SelectedStructureProbes |
| `core-admission-realized` | check reported | RegistrationProbes (`(3 in ℚˣ)⁻¹ = 1/3`; `2 ∈ ℤˣ` refused) |
| `b0-domain-preservation` | check reported | `ea432e4`; evidence goals carry no `RingHom.toFun` |
| `b0-binders` | blocked | the independent upstream assessment of the binder work |
| `cc-resolve`, `cc-closure` | resolution observation only | ClosureProbes; the value assertions (`rank(A₂) = 2`, …) are owed by the acceptance author |
| `cc-cohere`, `cc-cohere-exec` | check reported | CohereProbes, ResolveProbes |
| `cc-fib` | check reported | FibrationRegistryProbes |
| `cc-realize` transport | blocked | upstream: presentations and their isomorphisms (formalization dispatched) |
| `cc-lift`, `core-return-lifts`, `lc-lift-subobject` | check reported | LiftProbes, LiftLimitProbes |
| `cc-refine`, `cc-props` | check reported | PropsProbes, RegistrationProbes |
| `lc-units-structure`, `cc-universal` | blocked | upstream: group-valued constructions (formalization dispatched) |
| `cc-realize-2cat`, `cc-realize`, `cc-adapter`, `cc-backends` | partial probes; execution still owed | kernel probes over `CasAcceptance/Strata`; real registered execution still required; historical host observations do not establish current engine availability |
| `cc-observations` | check reported | RegistrationProbes (`|(ℤ/4)^3| = 64` holds through a registration, wrong answers are `wrong`) |
| `gov-meaning-permanence` | partial fingerprint mechanism | `c09e06d` reported fingerprints for 137/149 read assertions; stability and partial coverage do not establish question preservation. Current checked-in inventory: 153 admitted identities, 142 records; directive B covers all identities and proof-artifact migration |
| `b0-authority` | rule of conduct (owner ruling 2026-10-10) | agents keep to their roles; no technical gate is owed |
| `b0-trials` | not started | stage E, after the kernel is fixed |

**Required computational assertions (frozen IDs).** These must execute through a registered
implementation at the tuple and meet their assertions: `sets.card.z4_cubed`, `sets.card.z7`,
`sets.card.z5_empty_power`, `sets.card.fin2_times_z3`, `sets.card.integers`,
`sets.finite.integers`, `sets.finite.fin2_times_z3`, `sets.implemented.card_fin`,
`sets.card.fin2_sqcup_fin3`, `sets.eq.rev_rev`, `sets.limit.pullback.card`,
`finite_sets.limit.pullback.card`, `lattices.discriminant.a1`, `lattices.discriminant.a2`,
`lattices.discriminant.a3`. The plan's existing positive computational examples that have no suite
assertion yet (`rank(A₂) = 2`, `rank(E₈) = 8`, the kernels of `sign : S₃ → ℤ/2`, the trivial map and
`id_{S₃}`, `ℤ/3` abelian and `S₃` not, formed-module cardinality, the `𝔽₉` transport) are owed as
suite assertions by the acceptance author and are required once admitted. **Every admitted
assertion** in the accepted `CasAcceptance/Permanent/admitted.json` must be semantically valid
at the tuple (153 identities in the checked-in inventory on 2026-10-04; the inventory, not a
historical count or fingerprint subset, supplies the denominator):
"invalid because the kernel cannot interpret it" is a defect, never a final status. `NoImplementation`
is acceptable only for an assertion this paragraph does not require.

**Outside B0, with their existing dispositions:** notebook reconstruction (`cc-notebook`, deferred by
the owner 2026-09-29); new mathematical coverage, production leaves and notebook features (frozen by
the convergence process).

### Exit trials

**These trials are a required kernel-MVP exit gate before substantial
production leaf work**, and remain part of final B0 acceptance. Run after
the kernel is fixed, by contributors who choose the concrete extension themselves; the
orchestrator supplies no pre-shaped definition or expected output. A trial that needs an edit to the
frozen kernel or an old leaf has failed; the deficiency is repaired, the candidate re-frozen, and the
trial repeated.

| Mechanism | Required observation |
| --- | --- |
| New structured object | Existing applicable operations appear through its formal structure; two structures on one carrier stay distinct |
| New generic operation | Existing applicable objects acquire it after the upstream release; no old object or leaf is edited |
| Generic group-valued construction | `Aut`/subgroup/stabilizer expose group and subgroup interfaces by construction |
| Classifier/refinement | The refined object keeps its data and gains the justified interface; a backend property result never changes placement |
| Competing structural routes | Distinct routes stay distinct; ambiguity is reported; an admitted comparison is used explicitly |
| Parameter/base transport | Prescribed reindexing and selected maps are retained |
| Nonidentity presentation change | Transport goes through the accepted nonidentity comparison, never equality or backend `==` |
| Structured result lifting | The complete structured result with its defining maps; a missing lift computation is a named gap |
| Generic application/admission/binder | A new instance is read without notation-specific kernel cases or implementation-shaped upstream evidence |
| Leaf replacement | Missing, wrong, malformed or unavailable implementations change computational outcomes only; checked with no leaves and with deliberately wrong leaves |

### Gates

Three families, as modifications of the existing compiler, checks and harness:
- **A, build and boundary integrity.** The release checks under Lean; the kernel and contract
  compile at the tuple; leaves contribute no Lean or semantic registration; the semantic reading
  imports no leaf state; protected rules are evaluated from their accepted revision, and candidate
  code runs without credentials that can alter them; a failing required check cannot be omitted.
- **B, question permanence** (`gov-meaning-permanence`).
- **C, B0 acceptance**: the required assertions and trials, compared per assertion identity and
  outcome, never by file counts; the broader corpus is reported with its remaining gaps.

A gate is kept only if it protects an explicit obligation or observed failure mechanism, judges
actual code, data flow, types or execution rather than a label, cannot be changed and self-accepted
by the candidate's author, and costs only at its boundary (policy 2). Under that test:
- the banned-construct ratchet's ban on `partial def` does not protect a mathematical obligation,
  and is withdrawn from `custodian/verify.py` as construction work (architecture.md, "Operating
  phase: B0 construction"); the actual obligation is that a pure algorithm required to terminate on valid input
  does, and that effectful failure is reported as an implementation failure;
- `check_kernel_totality.py` judged a self-applied label; it is withdrawn, and its obligation is
  carried by the outcome model of `cc-failure-strata`;
- `check_authorship.py` judged trailers each author declared about itself; it is retired (removed
  from the build, CI and the repository, 2026-10-02). Authority comes from configuration (below).

### Authority configuration (`b0-authority`)

**Owner ruling (2026-10-10).** This separation is a rule about what each agent is permitted to do, not a technical gate on what it is able to do. An agent may hold a credential or tool capable of more (for example the shared GitHub token); it does not use it to write outside its role, and acceptance does not wait on removing such capability. A breach of the rule is a defect in the agent's conduct, recorded and repaired, not an argument that `b0-authority` is unreachable.

The essential restrictions are on reading, writing, commissioning, approving and replacing
authoritative inputs. Assigned author permissions bind conduct, including when a shared
credential or tool has broader capability. The launcher supplies independently assigned
requirements and permitted inputs and operations; the author follows them. Protection of
independent authoritative transitions remains a deployed-control obligation, whose actual
configuration and bypass paths are verified before claiming that protection:
- the kernel worker does not use a credential or tool to write `lean-categories` or commission
  its authors; upstream requirements come independently from the protected requirement revision;
- independently accepted references require the applicable independent review, dismiss stale
  approvals, and allow no worker bypass; acceptance statements, interpretations, evaluator rules,
  owner requirements and protection configuration cannot become authoritative through a
  construction-source merge. Use controls that actually protect that transition; file patterns,
  role variables, hashes and CODEOWNERS alone are not an authority boundary;
- `lean-categories`' registry schemas and validators are upstream mathematical authority;
- the custodian's review decides trusted-boundary changes against these requirements (policy 6);
  the owner decides only a change of requirement, completion standard or authority (policy 2).

Record the assigned roles, independently supplied requirements and permitted inputs and
operations, together with the verified authoritative-transition controls and independent result.
Do not wait for removal of an author's broader credential or tool capability. A missing
administration operation or independent acceptance path is a dependency of its consumers, not a
reason to claim protection or fabricate approval. Ordinary kernel source work continues; a `gov-*` node blocks only operations whose
correctness or authorized acceptance actually consumes its result (policy 5).

### Construction directives (owner replacement, 2026-10-02)

These replace the earlier "Disposition of outstanding work" and "Work selection and failure
routing". All existing B0 rows and required assertions are retained. The directives replace
incident-by-incident administrative tasks with coherent implementation work. They are
implementation groupings of existing obligations, not additional acceptance milestones. The
policies they implement are [architecture.md](architecture.md), "B0 policies", "The policies".

Their dependency graph is operational, not an A–B–C–D source-work queue. A, B and C may be
implemented and locally tested in parallel against available accepted inputs. Within C, upstream
work proceeds independently from the fixed mathematical requirements; kernel consumers wait only
for the accepted inputs they use. B's authoritative interpretations consume accepted mathematics,
and B/C's integrated validation consumes the same compatible candidate tuple. A's verified
boundary is required before claiming structurally independent authoring, activating a replacement
judge or advancing an authoritative record. D consumes that boundary, B's complete question
preservation and C's full computational tuple, then freezes the candidate for the existing trials.
A failure in one operation blocks those consumers, never all construction.

#### Construction directive A: complete the constrained execution and authority boundary

**Existing scope:** `b0-integration`, `b0-authority`, and the controller portions of the current
mandate.

Implement role-specific tool exposure, independently sourced dispatch, protected authoritative
inputs, candidate execution without authority credentials, and review requests assembled from one
revision tuple.

Remove the old authority paths and their consumers in the same change. Retaining a legacy free-form
dispatch endpoint, a caller-set role variable that authorizes admission, or a writable authoritative
status would preserve the original mechanism. Role labels and hashes may serve bookkeeping only.
Construction source may implement and test the replacement; only independent acceptance may make
it the authoritative judge. Identify any unavailable deployment control as an implementation
dependency rather than replacing it with a self-declared restriction.

Exercise the resulting controller on the actual historical transition classes: an authorized
controller replacement, ordinary documentation recording, an unrelated failing check, unavailable
publication, missing review context, and an attempted downstream rewrite or commission of upstream
work.

The positive cases must proceed through ordinary operations. The forbidden cases must have no
authority-bearing operation available. No special exception for a listed historical commit, file,
agent, or incident may be required.

This work is not a prerequisite for unrelated kernel source construction. It is a prerequisite for
claiming that protected publication, independent authoring, or independent acceptance is
structurally enforced.

#### Construction directive B: complete question preservation and stage-correct outcomes

**Existing scope:** `gov-meaning-permanence`, `cc-failure-strata`, and the relevant
application/admission obligations.

Replace post-evaluation question recovery with the single preserved typed-question path. Make the
executed request consume that same question. Remove consumers of reduced answers or incomplete term
collections as substitutes for meaning.

Establish the accepted interpretations independently. Cover the entire admitted assertion
inventory, including assertions the candidate cannot currently read. Do not repair the denominator
by dropping failures.

Validate distinctions that the defective mechanism erased: different relations on the same
operands, different selected structures on the same carrier, different parameters, different
logical structure, and different structural routes. Preserve the mathematical question rather
than an exact proof term or encoding: proof-irrelevant or representation-preserving repairs use an
independently assessed typed comparison or artifact migration. That comparison retains proof
proposition types and every semantically relevant datum. A changed interpretation needs independent
assessment: repair an erroneous old reading against the unchanged admitted assertion and its
sources, or obtain an upstream correction if the intended mathematics itself changes. Neither
case permits baseline regeneration to fit the candidate.

#65's `QuestionIdentity` and proof-identity probes are candidate work toward this requirement.
They do not independently accept its new fingerprints. The series reinterpretation identified
on #63 must be assessed separately from proof-term noise; the entire admitted inventory remains
in scope whether or not the candidate can currently read it.

Complete the stage-specific failure interfaces across the reader, realizer, backend port, decoder,
and harness. Do not retain a generic catch-and-relabel path beside the corrected model.

Completion requires the full mechanism, not another set of stable fingerprints.

#### Construction directive C: finish the compatible semantic and computational tuple

**Existing scope:** the remaining stage-B, C, and D obligations, without narrowing any row.

The upstream formalization author completes the required mathematics from the existing
requirements and sources; independent upstream assessment accepts its release. The kernel worker
does not choose its signatures, row arrangement or evidence terms, and the author does not
supply its own independent acceptance.

Recover correct existing work rather than recreating it as a sequence of artificially staged pins.
Produce the accepted mathematical revision and test its finished combination with the
corresponding kernel and contract. The six-stage binder pin sequence stays retired.

For the kernel, the specific unfinished work identified by the audit remains substantive
implementation work: generic execution of prescribed result lifts, complete structured results
with independently formal defining maps and lifts paired with computational data, nonidentity
presentation transport, parameter transport, and interpretation of the accepted binder and
group-valued constructions. These are not repaired by adding special cases for
the motivating examples.

The computational contract must describe each required request and reply without requiring a leaf
author to inspect kernel source. A leaf receives the released contract and implements
registrations against existing engines. It does not infer missing protocol semantics, rebuild
generic kernel machinery, or supply proof machinery to raise its own acceptance standing.

Run every required computational assertion through the registered execution path on an environment
with the necessary engines. Engine absence is an execution dependency to resolve, not a reason to
replace the computation by scaffolding or a Lean proof.

A named gap remains a gap. It cannot close a positive execution obligation.

#### Construction directive D: establish B0 at a frozen candidate

**Existing scope:** `b0-trials` and final B0 acceptance.

Freeze the candidate kernel, contract, and old leaves. Independent contributors choose the concrete
extensions for every mechanism already listed in the plan.

The trials must include both directions of extension: new formal objects obtaining old applicable
operations, and new generic operations reaching old applicable objects without edits to those
objects or leaves. They must also exercise the specified transport, coherence, refinement,
application, and structured-result mechanisms.

Replacing leaves with missing, wrong, malformed, or unavailable implementations must alter
computational outcomes only. It must not alter mathematical meanings, types, or available
operations.

An extension requiring a kernel special case or an old-leaf repair fails that trial. Repair the
generic deficiency, re-freeze the candidate, and repeat the affected trials. Do not accept the
repair as an exemption attached to that extension.

Final acceptance requires all fixed B0 obligations at one compatible tuple, including the required
computations and compositional arguments. Successful hostile examples cannot replace those
arguments; a blanket refusal of difficult inputs cannot replace the required positive
capabilities. Both conditions are already part of the owner's convergence specification.

## Rules for executing this plan

- **The evidence model governs every node** ([architecture.md](architecture.md), "The evidence
  model: nothing from a leaf is trusted"). A leaf is a registration (operation id, input form,
  opaque implementation) and ships no mathematics and no Lean. No node's acceptance is
  established by anything a leaf supplies: a denotation, proof, identification, evidence, status,
  certificate or self-test. Correctness evidence is the permanent acceptance suite alone, and what
  Lean can discharge is proved in `lean-categories` or discharged generically by the kernel.
- **Step 0 is mathematics.** The upstream author states each mathematical object in FOUNDATIONS
  with a citation or by its Mathlib declaration (CC-TRUE). A downstream node identifies that
  accepted input; it does not write the upstream statement. If the input is absent, only the
  operation depending on it waits, with the dependency recorded in the existing obligation.
- **Search before authoring, for every obligation** (CC-REUSE): definitions and proof obligations
  alike are first attempted by broad formalization-corpus API searches under several
  formulations; only glue and residue are hand-written, and the search record ships with the
  work. Known first candidates: Mathlib's `Functor`, `Functor.Elements`, `Arrow`, `Core`,
  `Over`/`Under`, `MonoOver`/`Subobject`, `Grothendieck`, `ModuleCat.restrictScalars`/
  `extendScalars`, `ConcreteCategory`, limits and kernels come first. Project code adds only the
  registry, the resolver and the leaf boundary (declared types and registrations) that no library
  supplies.
- **Formal laws and computational evidence are separate** (CC-LAWS). Accepted mathematical
  declarations supply their required proofs and coherent data. Independent execution tests
  judge realizations; no finite test or engine law query substitutes for formal structure.
  Ordinary Lean elaboration, reduction and proof checking remain required.
- **Each node names its consumer**: the smallest end-to-end call that must work when it
  closes, stated below as its acceptance.
- **Specimen leaves probe the core.** The formed-module/lattice chain, the ring diamond, the
  \(\mathbb F_9\) presentations and the hostile orthogonal-subgroup backend are probes. A specimen
  leaf is a registration like any other: nothing it states is believed, and its answers are judged
  by the suite. A defect a probe exposes is repaired in the core node that owns it.

## Historical design directions and source-node records

The following dated directions and node observations are preserved as history and source
provenance. The current work order and mathematical acceptance are #10, KM1–KM9 and the
acceptance table above, read with the current CC requirements. The old node names remain
cross-references; their dated source descriptions and stronger or superseded formulations
are not additional implementation queues or current mathematical claims. In particular,
the current distinctions between families and transport, directed and invertible comparisons,
chosen representatives and subobject classes, and formal constructions and untrusted
computational data govern those historical descriptions. No fixed accepted question or
required observation is retired by preserving its old record here.

<details>
<summary>Historical directions, DAG and node deliveries</summary>

## Current direction (2026-09-29, owner correction)

**Goal.** `lean-cas-dsl` is rewritten to *be* the system specified in
[computational-core.md](computational-core.md): a mathematician-facing DSL elaborating into one
coherent Lean category/functor calculus, over typed contracts for opaque computations, over
arbitrarily messy Sage/GAP/Julia/OSCAR code. This is a new system, not a port.
`sage-categories` is the record of what such a system must support and of what goes wrong without
it (spec §3, §9); its implementation and its node structure are not reproduced.

**Measure.** The system is done when a leaf with every mistake observed in the research
repositories (its own subgroup notion, isotropic operations on generic groups, a second `Aut`, a
forgotten inclusion, a lattices-to-sets shortcut) can change nothing the user sees except that its
own answers fail the suite, and every object presents everything expected of its kind (every
subgroup has everything subgroups have). A leaf adds no operation: every operation is mathematics
formalized in `lean-categories`. Progress is measured against the design points of the spec
(CC-*), not against leaves.

**Design procedure (2026-09-29).** These assessments supply the existing B0 obligations. Source
work now follows the construction directives and actual input dependencies; recording an older
step is not a new global prerequisite:

1. `cc-design-assessment` — assess the current `lean-cas-dsl` against each design point of the spec
   and the leaf contract (spec §5): what is realized, what is realized wrongly, what is missing,
   with file locators. Output: [design-assessment.md](design-assessment.md).
2. `cc-drift-triage` — **owner decision 2026-09-29:** the notebook layer is not carried forward
   through the architecture work. `CasDsl`, `CasDslTests` and the notebooks leave the build gate;
   rebuilding the notebook surface on the finished architecture is the last node (`cc-notebook`).
   The `lean-categories` mathematics from the drift commits stays as it is.
3. Design nodes — the assessed gaps are the existing `cc-` nodes below, with their CC-*
   requirements and actual dependencies. Construction implements those obligations coherently;
   an ordinary defect does not create a new node or require serial source work.
4. **A few specimen leaves test whether the core suffices** (lattices over formed modules, the ring
   diamond, finite fields under two presentations, a hostile orthogonal-subgroup backend). A
   specimen registers computations only. It shows that separation of concerns holds and that
   everything expected of a kind arrives by composition, whatever the specimen computes. Where a
   specimen needs something the core lacks, that is a core deficiency recorded as a design node;
   the specimen is never extended, and the notebook layer never patched, to make it pass. Specimen
   mathematics is stated at its true generality: a bilinear module is an `R`-module with a map out
   of `M ⊗ M` (`L²(ℝ)` with the integration pairing is one), never a matrix; a Gram matrix is at
   most one leaf's input form for a finite free case and never appears in the core, the notebook
   layer, or a specimen's semantics.
5. **Separation of concerns** ([architecture.md](architecture.md) owns it; this is its summary).
   - **`lean-categories`**: all mathematics, including which categories, structural functors,
     classifiers, operations (methods) and coherences exist, and the presentation forms of
     operations' inputs and results with what they denote.
   - **Kernel** (`lean-cas-dsl`, `CasCatalogue`): deterministic derivation, from the pinned
     `lean-categories` release, of what an expression denotes, which operations apply and how they
     propagate (functorial transport in place of inheritance), resolution, ambiguity, placement and
     refinement, plus the leaf API (declared types of computations) and the registry of leaf
     registrations. It authors no mathematics. Equality is a judgement Lean makes in the category
     the objects live in, three-valued (CC-DECIDE), and is distinct from isomorphism: `𝔽₂[x]/(x)`
     and `ℤ/2ℤ` are isomorphic and not equal. An isomorphism between two presentations is
     mathematics of the catalogue (CC-CARRIER), never a leaf's assertion. A backend's `==` is never
     authoritative for equality, isomorphism or identity of presentations.
   - **Leaves**: opaque computations registered against registered operations' declared types
     (operation id, input form, implementation), in backend code of any kind. A leaf ships no
     mathematics and no Lean, and nothing from it is trusted.
   - **Notebooks**: interactive computation for research. The notebook language only elaborates
     surface syntax into kernel terms. It defines no category, typing, encoding, codec, algorithm
     or equality (`cc-notebook`).
   - **Acceptance**: the only correctness evidence: permanent, leaf-blind assertions whose
     expected values come from proof, citation or an independent oracle
     (`cc-acceptance-permanent`).

## Direction after the owner correction of 2026-09-29 (second)

**Where the work is.**
1. **The mathematical API, in `lean-categories`.** This is about 90% of the work, and it is where the
   API design happens. It formalizes the categories, objects, elements and methods (usually functors,
   or morphisms on elements) that the language offers, each at its lowest owner, with its surface
   name.
2. **The permanent test suite, in `lean-cas-dsl`.** Tests are written in the DSL, as SPEC.md writes
   mathematics (`assert |(ℤ/4)^3| = 64`). They are admitted once and never changed, and they assert
   facts and the existence of implementations. This needs a DSL that states such facts through the
   catalogue alone, and a harness that reads and runs test files.
3. **Leaves.** These are mechanical and external. A leaf satisfies the intake contract, never sees
   the tests, and is measured only by the harness. The leaves in `lean-cas-dsl-leaves` exist as
   litmus probes of the kernel, of `Cat` and of `lean-categories`; a leaf is written or changed
   there only when doing so exposes such a deficiency.

**Nodes, in order.** The `lc-api-*` nodes are `lean-categories`' and are listed here as
prerequisites of the language.

| ID | Work and acceptance | Needs |
| --- | --- | --- |
| `lc-api-names` | **Delivered 2026-09-29 (`lean-categories` `390edd9`).** **Upstream.** Every registered category, object and method carries its surface name; the language resolves every identifier only through these rows. **Acceptance:** `Sets`, `FiniteSets`, `Groups`, `Rings`, `Card`; `ℤ`, `ℕ`, `Fin`, `ZMod`; `cardinality`, `is_finite` are names in the catalogue, and no name is defined in `lean-cas-dsl`. | — |
| `lc-api-literals` | **Delivered 2026-09-29 (`390edd9`: `lit.cardinals`, `CardinalLiteral`).** **Upstream.** Literal forms of result categories: cardinals first (`n`, `ℵ₀`), with their denotations. **Acceptance:** a literal row for `cat.cardinals` whose denotation is Mathlib's `Cardinal`. | — |
| `cc-dsl-language` | **Delivered 2026-09-29 (`CasCatalogue.Language`).** `|ℕ| = ℵ₀` and `|ℤ| = ℵ₀` elaborate and are gaps (no presentation of ℕ or ℤ is realized); `|(ℤ/4)^3| = 64` holds. A DSL syntax category for SPEC.md's statements (`let`, `assert`, `E.m()`, `|E|`, `X × Y`, `ℤ/n`, `E in C`, literals). It elaborates through the catalogue's names, objects, limits and methods, and names no category id, handle, realizer or leaf. **Acceptance:** `assert |(ℤ/4)^3| = 64` and `assert |ℕ| = ℵ₀` elaborate to the semantic proposition, with its realization selected by the kernel. | `lc-api-names`, `lc-api-literals` |
| `cc-observations` | **Open.** Comparing a computed value with a literal: the kernel reads an answer, given in the operation's declared result form, as a literal of the result category, whose literals, denotation and comparison justification are `lean-categories`' (`lc-api-literals`). Evaluation in the literal type answers semantic equality only under that accepted justification; see leaf-registration.md, Comparison. No leaf supplies an observation of its values or a proof about it. **Acceptance:** `assert |(ℤ/4)^3| = 64` compares the installed computation's answer with the literal `64` by evaluation alone; no leaf-facing form carries an observation or a proof. Delivered in part 2026-09-29: the comparison by evaluation; the leaf `ObservationEntry` with its proof `d.obj h = denote (observe h)` is (code gap: `gov-leaf-authority`). | `cc-dsl-language` |
| `cc-dsl-tests` | **Delivered 2026-09-29.** The acceptance suite as DSL files (`tests/acceptance/*.cas`), run by `CasCatalogue.TestSuite` (`#cas_tests`) and `CasAcceptance.Suite` (a Lake `input_dir`, so editing a test re-runs it). Each statement carries its id and provenance and is admitted append-only by `check_acceptance_permanent.py`. The runner reports each statement's outcome: holds, gap, unavailable, wrong, malformed or invalid; `assert implemented …` states that an implementation exists. `sets.cas` states the `Sets` facts (cardinalities, finiteness, products, coproducts, `rev ∘ rev = id`, the pullback of two graphs); the `FiniteSets` facts are gaps until a computation on `Fin(n)` in `FiniteSets` is installed; `lattices.cas` states `A_n^♯/A_n ≅ ℤ/(n+1)` for `n = 1, 2, 3` (gaps). Backend agreement is the harness's: the suite run over a backend's leaf alone. **Acceptance:** the suite runs through the harness; editing an admitted test fails the gate; no test names a leaf. | `cc-observations` |
| `lc-api-elements` | **Delivered 2026-09-29 (`lean-categories` `ae0f4c6`; language: `m(a)`, `{x ↦ y, …} : X → Y`, `id`, `∘`, shape calls `pullback(f, g)`, morphism equality).** **Upstream.** Element literals of object families, graph literals of a category's morphisms, and named morphism families. **Acceptance:** `assert rev(3) ∘ rev(3) = id(Fin(3))` and `assert |pullback(f, g)| = 3` hold; an out-of-range element or a non-functional graph is an invalid statement. | `cc-dsl-language` |
| `lc-api-refined-names` | **Delivered 2026-09-29 (`lean-categories` `536555f`).** **Upstream.** An object row may refine another along a registered structural functor, with the identification of its image (`Fin(n)` in `FiniteSets` refines `Fin(n)` in `Sets` along the forgetful functor). An unqualified name denotes the unrefined object; `X in C` denotes its refinement in `C`. This is one object with a refinement, not two objects ranked by precedence. **Acceptance:** `assert |Fin(3) in FiniteSets| = 3` and the `FiniteSets` pullback restated; every admitted `sets.cas` test unchanged. | `lc-api-elements` |
| `lc-api-lattices` | **Delivered 2026-09-29 (`lean-categories` `2f50034`: `LeanCategories.Lattices.Integral`, the dual as `{v ∈ ℚⁿ | Gᵀv ∈ ℤⁿ}` for every Gram matrix).** **Upstream.** Named lattices (`A(n)`), their duals and the canonical map `L → L^♯` as registered objects and morphisms of the lattice categories. **Acceptance:** `assert |cokernel(to_dual(A(2)))| = 3` restates `colimit.bil_wform.a2_discriminant.card`. | `lc-api-elements` |
| `cc-harness` | **Delivered 2026-09-29 (`cas-harness`, `CasTools.Harness`; `just harness`).** Over `CasLeaves` it reports what `CasAcceptance.Suite` reports; over `CasLeaves.Foundation.Objects` alone the same statements elaborate and more are gaps. It found that the language's vocabulary depended on the imported leaves (rows such as `rev` came only through a leaf's imports); the language now imports the whole release. Runs the suite over a set of installed leaf packages, each depending only on the intake contract, and derives the implementation gaps. Leaves never import or see the suite. **Acceptance:** the suite over this repository's litmus leaves, with the gap report as its output. | `cc-dsl-tests` |
| `cc-semantic-reading` | **Delivered 2026-09-29.** Every statement is first read semantically (`CasCatalogue.Semantic`): objects are their declarations, morphisms are elaborated at `X ⟶ Y`, limits are the registered presentations (returned along creation lifts), methods are functors after their routes, properties `Classifier.Holds`, comparisons `Eq`; failure is invalidity, independent of leaves. Before, a statement over an unrealized object stopped at the first missing presentation and was reported a gap even when meaningless. **Acceptance:** the suite's outcomes unchanged; `ℤ.frobnicate() = 3` and `gcd(84) = 6` are invalid, `|ℤ| = 5` a gap. | `cc-harness` |
| `cc-leaf-packages` | **Delivered 2026-09-29.** The leaves and the leaf contract leave this repository: `lean-cas-dsl-leaf-contracts` (`CasContract`: the twelve kernel modules a leaf is written against, and `cas_port.py`; depends on `lean-categories` only) and `lean-cas-dsl-leaves` (`CasLeaves` and their programs; depends on the contract and `lean-categories` only). This repository depends on both and discharges its suite over the leaves (`cas-harness`); no leaf package reaches the suite. The contract is the kernel's, not `lean-categories'`, which owns nothing of computation or execution (`specs/architecture.md`, "Packages"). **Acceptance:** both packages build standalone; the gate and `cas-harness CasLeaves` report what they reported before the move. | `cc-harness` |
| `lc-api-spec` | **Upstream, continuous: the bulk of the work.** SPEC.md's vocabulary, section by section, as catalogue rows (categories, objects, elements, and methods on objects and on elements), each section closing with its DSL tests admitted in `cc-dsl-tests`, gaps allowed. **Delivered 2026-09-29 for every SPEC.md section** (seventeen test files, 148 tests, all valid; those whose sets no installed computation handles are gaps): `numbers.cas`, `finite_sets.cas`, `functions.cas`, `polynomials.cas`, `differentials.cas`, `fractions.cas`, `linear_algebra.cas`, `composed.cas`, `calculus.cas`, `ellipses.cas`, `inverses.cas`, `factorization.cas`, `series.cas`, `several_variables.cas`, `algebras_schemes.cas` (`lean-categories` `57c5da8` through `3a84ea3`). **Not stated, and why:** `|𝒫(A)| = 2^|A|` in that form (arithmetic of cardinals is not registered; stated as `|𝒫(A)| = 8`); SPEC's `q.roots() ⊆ ℂ - ℚ` as written (stated along `map q to ℂ[x]`), and factors over `ℂ` as a division; `Spec ℚ[x]` and `d` on `𝒪_X` (a map of sheaves; SPEC displays it); `kernel(d/dx : ℚ[x] → ℚ[x]) = ℚ` (kernels of module maps are not reached from `Sets`); `Fs[0]` (stated by `Fs = {…}`); `ker φ` for a map written on coordinates (stated by its matrix); subspaces as subobjects in `Mod(ℚ)` (stated as subsets); `e^t` (stated `exp(t)`); truncations `ℝ[[t]]/(t⁶)` and `ℝ/O(ε)` (displays). **Open:** the presentation forms of objects of families over sets (`K∖{0}`, `Kⁿ`, `Matₙ(K)`, `R[x]`, `𝒫(X)`), and what each denotes, must be declared upstream with the operations that take them; a leaf only computes on them. | `cc-dsl-tests` |

## Direction after the owner correction of 2026-09-30: authorship and gates

The session that delivered `lc-api-spec` wrote in every layer. It formalized in
`lean-categories` while reading the kernel and the tests, wrote leaves, and planned to re-admit
tests itself. That inverts the one-way workflow ([architecture.md](architecture.md), "Authors: one
role per agent").
- The orchestrator owns policies, gates, compliance, the kernel and the contract.
- Formalization, acceptance and leaves are each written by a separate subagent.

These historical nodes retain their substantive obligations under B0. They block only operations
that consume their result; independent source work follows the construction directives. Ownership
is by the role-specific inputs and operations of architecture policy 1, not a downstream brief.

| ID | Work and acceptance | Needs |
| --- | --- | --- |
| `gov-roles` | **Delivered 2026-09-30 (orchestrator) (this text; architecture.md "Authors: one role per agent"; each repository's AGENTS.md).** The role split is written down, with its owner and links. | — |
| `gov-quarantine` | **Orchestrator. `bd31fe3` reviewed by the formalization agent 2026-09-30 (`lean-categories` `c06aeed`): units, numerals, finite subsets and sums, monics and companion, calculus domains, power series accepted; `taylor` repaired (division by the unit `k!`), and `roots`, `factors` moved to `R[x] ∖ {0}`, `prime_factors`, `multiplicity` to `ℕ⁺` and primes (they relied on Mathlib's conventions at `0`). Open from that review, for independent upstream assessment: `num.sets.fin` is a `.numeral` row though `Fin n` has no initial map (points of a set are not numerals: a registry-kind decision); the totality gate cannot see conventions inside Mathlib definitions (reviewers check them); `matrix_rank` over a commutative ring needs its mathematical requirement fixed by its authority. The leaves `b818e4c`, `aca37d9` remain quarantined.** The following are cross-barrier work, not accepted as any row's output:<br>- `lean-categories` `bd31fe3` (units, numerals, division, finite subsets and sums, monics and companion, calculus domains; `ElementLiteralEntry` → `NumeralEntry`; `ObjectEntry.inclusion`/`admission`);<br>- the contract mirror `a9bfc90`;<br>- the leaves `b818e4c`, `aca37d9`;<br>- the uncommitted evaluator edits of that session (never to be committed).<br>**Acceptance:** a formalization subagent reviews `bd31fe3` from its sources alone, and a leaf subagent takes over the leaves (`gov-leaf-rewrite`). Nothing builds on either before then. Nothing is reverted without the owner. | `gov-roles` |
| `gov-authorship-gate` | **Retired 2026-10-02: it judged self-declared trailers; separation is `b0-authority`'s.** It was delivered 2026-09-30 as `scripts/check_authorship.py`, in `just build`, keyed by `Agent-Role`/`Agent-Id` trailers. A CI check in every repository of the chain fails a commit whose `Claude-Session:` trailer appears in the history of another row of "Authors". **Acceptance:** a commit reproducing this session's pattern (one session in `lean-categories` and in `tests/acceptance/` or a leaf) is refused. | `gov-roles` |
| `gov-readmission-gate` | **Authority remains open under `b0-authority`.** The 2026-09-30 `AGENT_ROLE=acceptance` guard is caller-controlled bookkeeping, not independence. **Acceptance:** the kernel author has no operation that advances authoritative admissions, corrections or interpretations; the independent acceptance operation checks the fixed question and complete inventory. | `b0-authority` (authoritative admission only) |
| `gov-registry-gates` | **Delivered 2026-09-30 (orchestrator) for LC-14 encodings and inverses/division off groups (`lean-categories` `d4d6f1a`, `Registry/Totality.lean`); the general LC-16 case remains.** (a compliance gate in `lean-categories`' registry validator; it adds no mathematics). Registration fails, citing LC-14, for:<br>- a morphism, operation or numeral declaration whose codomain is optional or partial;<br>- an operation declared on a category not all of whose objects carry it;<br>- a row that is not a total morphism between registered objects.<br>**Acceptance:** the pre-`bd31fe3` rows (`Option`-valued element literals, `Matₙ(K) → Matₙ(K)⊥` inverse, partial division) are each refused with that message. | `gov-roles` |
| `gov-kernel-lc14` | **Delivered 2026-09-30 (orchestrator): gate `scripts/check_kernel_totality.py` (green); kernel repair `2178913`, `e4c31ab` and between, against `lean-categories` `c06aeed`.** The six catch-fallbacks are gone; numerals come from the numeral rows (images of the initial maps, points of `Fin n`), carried along constants or a registered inclusion from `ℕ`; a value lies in a domain only when formed there (`x in D`), its evidence proved when read (never a `sorry`: a failed tactic is refused), a numeral needed in a domain formed there with its evidence decided (`3 ∈ ℚˣ`; `2 ∈ ℤˣ` refused); evidence about a map is stated of the function it is (`functionOf`). Suite: 33 hold (the fractions are now gaps: division takes a unit, and no leaf presents `ℚˣ`), 18 invalid statements use values outside their domains, sent to the acceptance author. The kernel admits no rereading, default, caught-failure rerouting or test-tuned tactic to make a term defined (LC-14's banned list). The evaluator's `try … catch` reinterpretations are listed and removed. **Acceptance:** each banned construct is absent at the revision, and a term outside its domain is invalid when read. | `gov-quarantine` |
| `gov-no-leaves-here` | **Delivered on `kernel/leaf-registration` ([#53](https://github.com/dzackgarza/lean-cas-dsl/pull/53)), awaiting merge.** `lean-cas-dsl` consumes leaves and ships none: it requires no leaf package, imports nothing from one, and reads a leaf package's manifest at run time (`CAS_LEAVES`). The probes that registered leaves here were removed with the machinery they exercised, or re-pointed to the semantic reading. The kernel's own probes use test backends under `CasAcceptance/Strata`, which are scaffolding, not leaves. **Acceptance:** `scripts/check_no_leaves.py` is green and refuses `import CasLeaves` and `require cas_leaves`; checked at `3444877`. | `gov-roles` |
| `gov-contract-guidance` | **Orchestrator.** The leaf contract's AGENTS.md states the layers, authors and barriers. A failure to meet the contract is investigated in its owning layer; it cannot become a leaf-authored mathematical requirement or relax the contract to fit a computation. **Recorded 2026-09-30 as text**; actual isolation is owed by `b0-authority`, not the retired trailer gate. | `gov-roles` |
| `gov-evidence-upstream` | **Upstream formalization (schema, validators and evidence); orchestrator (kernel and its generic purity gate).** Owner corrections 2026-09-30: the kernel's evidence tactic knew mathematics; "teaching the kernel about math should be impossible, unless it is purely categorical and completely general". Delivered by the orchestrator: `ObjectEntry.evidence` with its registration checks (`lean-categories` 646f4a7, LC-18); `establish` runs only the registered evidence, and `decide` by evaluation is the kernel's only proof; the tactic battery, lemma lists and `by` quotations are removed; `CasGates.KernelPurity` (a default build target, CI `kernel-purity`) with `KernelPurityProbes` replaces the regex gate. Owed by the formalization subagent: evidence for the seven admissions. **Acceptance:** `CasGates` builds; `3 ∈ ℚˣ`, `M ∈ Mat₂(ℚ)ˣ`, `x³ - 2x + 1 ∈ ℚ[x] ∖ 0`, `exp ∈ C^∞` established through the registered evidence; `2 ∈ ℤˣ` refused. | `gov-kernel-lc14` |
| `gov-leaf-tests-out` | **Delivered on [#53](https://github.com/dzackgarza/lean-cas-dsl/pull/53), awaiting merge.** `AdapterProbes` and `BackendProbes`, which called leaf functions directly, are deleted. No module of `lean-cas-dsl` refers to a leaf's declarations; the only mention of the leaves is the default location of a manifest in `CasCatalogue/Realize.lean`. A leaf's own tests are its business and live with it. **Acceptance:** no module of `lean-cas-dsl` refers to a leaf's declarations; checked at `3444877`. | `gov-no-leaves-here` |
| `gov-leaf-rewrite` | **Delivered by the leaf author on `lean-cas-dsl-leaves` `leaf/registrations` ([leaves #2](https://github.com/dzackgarza/lean-cas-dsl-leaves/pull/2)), awaiting merge.** `leaves.json` with 18 registrations, and Python glue over Sage and GAP. No Lean. Its findings are recorded under `gov-leaf-authority`. **Acceptance:** the harness admits the manifest and runs it: `sets` 11 of 18 at `3444877`, no wrong or malformed answer. | `gov-leaf-authority` |

## Direction after the external review of 2026-09-30: the constructions, not more separation

An independent audit (DSL `3b5ca68`, `lean-categories` `c06aeed`, contract `6588a86`, leaves
`c4cff16`) traced declarations through projection, contract validation, realization and
acceptance. It found that package separation and gates alone do not show convergence. The
generic constructions below do. Continue their executable work in parallel with the authority
boundary; neither class of work globally suspends the other. Each finding was checked against
source before it was recorded here.

| Node | Owner, finding, acceptance | Needs |
| --- | --- | --- |
| `gov-quarantine-evidence` | **Owner decision.** `lean-categories` `011d0be`, `a6222c2`, `82bd8ad`, `01b2f89` (membership evidence for the seven admissions) were written by a formalization subagent whose prompt carried the kernel's goal shapes and the orchestrator's test cases: information from implementation to formalization. They are unpinned and nothing builds on them. **Acceptance:** the owner keeps them, has a fresh formalization agent review them from the requirement alone, or reverts them. | — |
| `gov-orchestrator-containment` | **Owner (authority), orchestrator (proposal).** Close the holes in `specs/architecture.md`, "The orchestrator is inside the threat model". **Acceptance:** for each row, the discretion it names is removed, not relocated, and nothing the orchestrator writes can reinstate it. Progress is counted in classes of intervention made inexpressible (architecture.md, "The unit of progress"), never in commits, checks or passing examples. | — |
| `gov-meaning-permanence` | **Independent acceptance (authoritative interpretations and mechanism); orchestrator (implementation).** Protect the full admitted mathematical question, not text or exact proof artifacts. **Acceptance:** an unauthorized changed meaning fails; an independently assessed meaning-preserving comparison or migration permits artifact changes without dropping any admitted identity, weakening its expected answer or changing required execution. No candidate-writable exemption or regenerated baseline can accept itself. | accepted mathematics (initial interpretations); `b0-authority` (authoritative activation, not source work) |
| `gov-leaf-authority` | **Orchestrator (contract, kernel), leaf agent (leaves), acceptance agent (suite).** Design: [leaf-registration.md](leaf-registration.md). Every leaf-facing form is exactly a registration (operation id, input form, opaque implementation); nothing in the contract, the kernel, the tools or the suite consumes a leaf's denotation, proof, identification, evidence, status or self-test. The code gaps are listed in the section below, one per line. **Acceptance:** each listed gap is closed at its file; no leaf-facing form carries a functor, a proof, evidence or a status; every leaf is rewritten against the new contract (`gov-leaf-rewrite`); no acceptance assertion is established from a leaf's definitions, and the suite is run only from `lean-cas-dsl`. | `gov-roles` |
| `core-presentation-dependent` | **Delivered on [#53](https://github.com/dzackgarza/lean-cas-dsl/pull/53) and [contract #3](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/pull/3), awaiting merge.** What a value denotes is the declared form's denotation, `lean-categories`'; no leaf supplies a presentation or an isomorphism. The counterexample of `CasContract/Probes/LeafBoundary.lean` is deleted with the presentation rows: it cannot be written, since a registration has no field for it. **Acceptance:** no leaf-facing form carries a presentation or an isomorphism. | `gov-leaf-authority` |
| `core-return-lifts` | **Orchestrator (kernel).** A method with `returnsToSource` (the kernel of a bilinear module: `Bil → Mod`, with the restriction of the form registered as a subobject lift) resolves with the lift recorded (`Resolution.lifts`). `Semantic.method`, `realizedMethodCall` and `Language.call` then ignore it and return the functor's target, so the formed subobject is never reconstructed. The value must be the registered lift of the image back to the source category, with the source category as the result. **Acceptance:** `ker` of a bilinear module is an object of `Bil` whose form is the restriction, read semantically, and realized where actions exist. A specimen with a nondegenerate form whose restriction is degenerate distinguishes the lifted result from the bare module. Realized, with no registered realization of the lift, the call is a gap naming the lift; it never returns the bare module. | `lc-lift-subobject` |
| `lc-lift-subobject` | **Independent upstream formalization.** Given `L : MonoLift U` and a subobject `i : K ↪ U(X)` (an object of `Subobjects(D)` over `U(X)`), the lifted subobject `L.hom X i : L.obj X i ↪ X`, as an object of `Subobjects(C)`, with the proof that it is mono (for instance when `U` is faithful, or as a field of `MonoLift`: the formalization author decides). For a route of several steps, lifts compose. The kernel only applies this construction. **Acceptance:** stated and proved in `lean-categories`, with `formedKernel f` as its instance at the restriction of forms. | — |
| `core-admission-realized` | **Delivered on [#53](https://github.com/dzackgarza/lean-cas-dsl/pull/53) (`5dd2738`) with `lean-categories` [#70](https://github.com/dzackgarza/lean-categories/pull/70) and [#71](https://github.com/dzackgarza/lean-categories/pull/71), awaiting merge.** An admitted element is part of the semantic term. Its hypothesis may be data, provided it is a subsingleton: admission into `Mˣ` takes `Invertible x`, so the inverse is computable. The registered evidence builds it, generically for groups, division rings, `ℤ`, `ℤ/n` (read from the monoid), matrices, products and powers. The kernel's evidence runner passes the term it builds. **Acceptance (`RegistrationProbes`, no leaf):** `(3 in ℚˣ)⁻¹ = 1/3`, `1/(3 in ℚˣ) = 1/3` and `(2 in (ℤ/5)ˣ)⁻¹ = 3` hold by kernel-checked decision; `(3 in ℚˣ)⁻¹ = 1/2` is refuted; `2 ∈ ℤˣ` is refused. The suite gains `fractions` 2→5 and `inverses` 0→5; its failures are unchanged. | `gov-evidence-upstream`, `gov-leaf-authority` |
| `lc-units-structure` | **Independent upstream formalization.** Units are `units M : Sets` for a bare `[Monoid M]`, with `⁻¹` and `/` registered as named morphisms of Sets. Moving the formula upstream fixed its ownership, but the structure is still not represented. `Mˣ` is the units functor `Mon → Grp` (right adjoint to the inclusion). Inversion is the group structure, reached through registered structural maps, so every construction landing in groups inherits it without another registration. **Acceptance:** `⁻¹` on `Mˣ` resolves through `Grp`, and a second group-valued construction gets `⁻¹` with no row of its own. | — |

## `gov-leaf-authority` (2026-09-30, owner correction)

**The contract** ([architecture.md](architecture.md), "The evidence model: nothing from a leaf is
trusted"). A leaf registers an opaque computation against a registered operation's declared type:
the operation id, the input form (one of the forms `lean-categories` and the kernel declare for that
operation, with what it denotes), and an implementation in any language returning a value of the
declared result form. The kernel reads each answer into that form or rejects it as malformed. A leaf
ships no mathematics and no Lean. It is meant to be glue over a mature engine
([`lean-cas-dsl-leaves` AGENTS.md](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/e2f8537/AGENTS.md), "A leaf is glue over existing backends"), which a separate
engineering review checks and which earns no trust. Nothing a leaf supplies is consulted, recorded as evidence, or
allowed to affect meaning or acceptance. The acceptance suite is the only evidence, run only from
`lean-cas-dsl`.

**Delivered on branches, awaiting the owner's review and merge:**
- `lean-cas-dsl` `kernel/leaf-registration` ([#53](https://github.com/dzackgarza/lean-cas-dsl/pull/53),
  `3444877`):
  - a leaf is a manifest of registrations, admitted against the catalogue;
  - the generic structural codec;
  - the realized reading over the semantic term, with transport along the catalogue's refinement
    rows, morphisms as graph literals, and limits as diagram in and cone out;
  - Lean discharge first, through `decide` and the catalogue's registered evaluations, each proof
    checked synchronously by Lean's kernel;
  - every leaf-supplied realizer, action, decider, isomorphism, presentation, observation,
    decoder, trust status, `register_leaf` and `run%` removed;
  - the 26 assertions established from leaf definitions retired against admitted leaf-blind
    statements.
- `lean-cas-dsl-leaf-contracts` `kernel/leaf-registration`
  ([#3](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/pull/3)): a registration has
  exactly three fields (operation, input form, backend), and the realization machinery is
  deleted.
- `lean-cas-dsl-leaves` `leaf/registrations`: `leaves.json` and Python glue over Sage and GAP.
  No Lean.
- `lean-categories` [#67](https://github.com/dzackgarza/lean-categories/pull/67),
  [#68](https://github.com/dzackgarza/lean-categories/pull/68) and
  [#69](https://github.com/dzackgarza/lean-categories/pull/69): decidable equality of
  concrete-category morphisms, the finite-subset literal form, and registered evaluation of
  literal forms.

**Evidence at `3444877`:**
- `RegistrationProbes` and `KernelPurity` pass.
- The suite's failures are exactly the 12 invalid statements of #46.
- Every file is at or above the earlier baseline except `sets`, whose holds came from leaf Lean.
  It is 3 of 18 with no leaf, and 11 of 18 over the real leaves.

**Findings from the first registration leaves** (`lean-cas-dsl-leaves` `leaf/registrations`,
`eea5eea`), each routed to its owner:
- Kernel: a registration is looked up by the exact input object id, so a refinement
  (`obj.rings.integers`, `obj.finite_sets.fin`) reaches no registration of its underlying set.
  Routing an operation to a registration along the catalogue's refinement and inclusion maps is
  the kernel's (CC-TRANSPORT, CC-RESOLVE). A leaf never re-registers each refinement.
- Kernel: the realized reading sends no diagrams over the port, so no limit (`lim.sets.product`,
  `lim.sets.pullback`, `lim.groups.kernel`) and no arrow operation (`meth.kernel`, `meth.arrow_ker`)
  is computable. It needs input forms for diagrams and arrows (CC-UNIV, CC-DECODE).
- `lean-categories`: forms missing for arrows, subgroups (`op.groups.orthogonal_subgroup`), finite
  subsets of a power object, numerals as operation inputs, and uncountable cardinals in
  `lit.cardinals`. Cardinality of `ℝ` has no value in the result form.
- Contract: a backend's command cannot name an interpreter from the environment
  (`CAS_SAGE_PYTHON`), so each program locates its own engine.
- Build: `lean-cas-dsl` no longer requires `cas_leaves` as a Lean package once the leaves ship no
  Lean. It locates `leaves.json` without Lake.

## DAG

`Needs` lists immediate prerequisites. A node marked **Open** has acceptance under the evidence
model that the delivered code does not meet; its code gap is listed under `gov-leaf-authority`.

| ID | Work and acceptance | Requirements | Needs |
| --- | --- | --- | --- |
| `cc-kernel-audit` | **Delivered 2026-09-29: [kernel-replacement-audit.md](kernel-replacement-audit.md)** (input to `cc-design-assessment`: what `sage-categories` supplies that the system must also supply). **Acceptance:** `kernel-replacement-audit.md` has one row per `sage-categories` milestone-A kernel node and per spec §3 row, each naming the owning `sage-categories` contract read, the Lean replacement with file/declaration/commit/consumer, or the gap with the missing capability stated. | all | none |
| `cc-design-assessment` | **Delivered 2026-09-29: [design-assessment.md](design-assessment.md).** Step 1 of "Current direction". **Acceptance:** `design-assessment.md` covers every CC-* requirement and the leaf contract with realized / realized wrongly / missing and locators. | all | `cc-kernel-audit` |
| `cc-drift-triage` | **Decided 2026-09-29** (see "Current direction", step 2). Step 2 of "Current direction". **Acceptance:** every commit since `a191b61` / `a8a87a6` classified core / probe finding (with its core node) / leaf drift in the audit document; the owner's decision on the drift recorded. | all | `cc-kernel-audit` |
| `cc-gate` | **Delivered 2026-09-29:** `just build` = `lake build CasCatalogue cas-registry-export cas-axiom-audit` (default target `CasCatalogue`, whose glob includes every probe); `just test` adds the audit and export runs; `CasDsl`/`CasDslTests`/worker/notebooks out of the gate. Checked: the gate builds, and a false `#guard` appended to `CohereProbes.lean` fails it. The build gate compiles the architecture and its acceptance probes, and nothing else: `CasCatalogue` (every `*Probes.lean`), `cas-registry-export`, `cas-axiom-audit`; `CasDsl`, `CasDslTests`, `nbdsl_worker` and the notebooks are removed from `just build`/`just test` and from the default targets (kept in history, not built). **Acceptance:** `just test` runs `lake build CasCatalogue` plus the two executables and the axiom audit; a deliberately broken probe fails it. | — | none |
| `cc-leaf-boundary` | **Delivered 2026-09-29 for the separation of rows.** Libraries: `CasCatalogue` (kernel), leaves (now `lean-cas-dsl-leaves`), `CasAcceptance` (probes), `CasTools` (exporter, axiom audit). Write authority is read from the module being elaborated: semantic rows only from `lean-categories`, leaf registrations only through the leaf contract (`register_leaf`, atomic). The twelve parameter-quotation axioms are theorems (`parameterArgsValid arguments schema = true`, by `decide`). **Acceptance:** a leaf can write no semantic row and cannot import the kernel's internals or the suite (`LeafBoundaryProbes`); each forbidden kind is refused (`AdapterProbes`); `cas-axiom-audit` permits only `propext`, `Classical.choice`, `Quot.sound`. The registration's form is `gov-leaf-authority`'s. **Residual:** a quotation checks the symbolic arguments' sorts, not that the argument names the parameter the row supplies. | CC-ADAPTER, CC-IMMEDIATE, CC-SEP | `cc-gate` |
| `cc-realize-2cat` | **Open.** A functor of the catalogue is its two actions, and composites are Mathlib composites (`Functor.comp`, pasting of `CatCommSq`). Executing a step on presented data is a registered computation against the step's declared type (input form to result form, both declared upstream with what they denote); the kernel composes the computations along the resolved route and believes none of them. **Acceptance:** `cardinality` of a lattice runs as the composite of registered step computations from the receiver's declared input form, its answer judged by the suite; no leaf-facing form carries a category of handles, a denotation functor or a square. Delivered 2026-09-29: the Mathlib composites; the leaf-supplied `RealizedAction` with its denotation and `CatCommSq` is (code gap: `gov-leaf-authority`). | CC-ACTION, CC-REUSE | `cc-leaf-boundary` |
| `cc-cells` | **Delivered 2026-09-29 for cell rows.** Reuse: [`specs/reuse/cc-cells.md`](reuse/cc-cells.md). Registry row `cell` (`CellEntry`): a Mathlib `NatTrans`, or `Iso` when invertible, between the composites of two lists of registered functors, validated by definitional equality; leaves cannot register cells. `cell%` composes registered cells with Mathlib's `≫`, `whiskerLeft`, `whiskerRight`, `NatTrans.hcomp`, `Iso.inv`. A cell's component on presented data is computed from the catalogue's cell over the fully faithful denotation of the declared presentation form, which is `lean-categories`', never a leaf's. Specimen: the list monad on sets (`lean-categories` `Foundation/ListFunctor.lean`). **Acceptance (`CellProbes`):** on `ℤ²`: `ρ [v,w] = [w,v]`; `(η ▷ L) ≫ μ` is the identity; `η ▷ L` gives `[[v],[w]]`; `L ◁ η` gives `[[v,w]]`; `η ◫ η` gives `[[v]]`; `ρ ≫ ρ⁻¹` is the identity; mismatched endpoints, inverting a non-invertible cell, a leaf cell and a wrong-endpoint cell are rejected. Components over leaf-supplied denotations and full-faithfulness witnesses are (code gap: `gov-leaf-authority`). | CC-CALC, CC-ACTION | `cc-realize-2cat` |
| `cc-cohere-exec` | **Delivered 2026-09-29 for resolution.** A comparison is an invertible `cell` row between two distinct structural composites (`cmp.rings.carrier`). Resolution (`classify`) identifies routes by these cells as directed edges and runs a call on the class's unique source route: no order of candidates, rows or renderings chooses it; several cells between the same two routes are `ambiguousComparison`, identified routes without a unique source are `noSourceRoute`. Applying a comparison to data is its component (`cell%`). **Acceptance (`CohereExecProbes`):** the call runs on the comparison's source route whatever the order of rows, and reversing the cell moves it; two comparisons between the same routes are an ambiguity; `cardinality` along both routes meets the same assertions of the suite. Computing a component from a leaf's relabeling square is (code gap: `gov-leaf-authority`). | CC-COHERE | `cc-cells` |
| `cc-limits` | **Delivered 2026-09-29 for limit rows.** Registry row `limit`: a family of Mathlib `LimitCone`s of one shape in a registered category, validated. Registered: `lim.sets.pullback` (Mathlib `Types.pullbackLimitCone`), `lim.groups.kernel` (`lean-categories` `Algebra/GroupKernel.lean`). On presented diagrams, the apex is a registered computation's answer in the declared result form; legs and mediators are the kernel's, from the catalogue's `LimitCone` over the fully faithful denotation of the declared form (`realizedLimitCone`, `IsLimit.ofFaithful`, transport along `diagramIsoCospan`/`diagramIsoParallelPair`). **Acceptance (`LimitProbes`):** the pullback of `![0,1,1]` and `![1,0]` has 3 elements with legs `[0,1,2]`/`[1,0,0]`; a competing cone's mediator factors it and is unique; the pushout in `SetHandlesᵒᵖ` is reached through `Op`; the kernel of the sign `S₃ → ℤ/2` has 3 elements with a monomorphic inclusion. The leaf `limitRealization` (apex handle with the identification of its denotation) is (code gap: `gov-leaf-authority`). **Residual:** `Op` is not a registered category constructor; cokernels and images are not registered. | CC-UNIV, CC-CALC | `cc-cells` |
| `cc-adjunctions` | **Delivered 2026-09-29 for adjunction rows.** Reuse: [`specs/reuse/cc-adjunctions.md`](reuse/cc-adjunctions.md). Registry row `adjunction` (a Mathlib `Adjunction L R` between two registered functors; validated, sides checked). On presented values, the transpose is `realizedHomEquiv`, a composite of Mathlib equivalences over the fully faithful denotation of the declared presentation form; the limit of a diagram through `Δ ⊣ L` is `realizedLimitConeOfAdj`. Registered: `cat.walking_pair`, `cat.sets.pair_diagrams = Fun(WalkingPair, Sets)`, `Δ`, `lim` by sections, and `adj.sets.pair.diagonal_limit` (`lean-categories` `Foundation/SectionsAdjunction.lean`). **Acceptance (`AdjunctionProbes`):** `(g₁, g₂) : Δ(Fin 4) ⟶ (Fin 2, Fin 3)` transposes to the pairing and back; the limit through `Δ ⊣ lim` is the product with its projections, and the mediator of `(g₁, g₂)` is the pairing; swapped sides are rejected. Transposes over leaf-supplied denotations are (code gap: `gov-leaf-authority`). **Residual recorded then:** `Adjunctions(F,G)` and `Equivalences(C,D)` are not registered; unit and counit are not registered as cells. The corrected reuse record and CC-HIGHER/#82 distinguish the chosen-structure fibre from varying-adjoint uniqueness; this dated delivery does not establish general higher adjunction consumption. | CC-CALC | `cc-cells`, `cc-limits` |
| `cc-lift-general` | **Delivered 2026-09-29 for lift rows.** Reuse: [`specs/reuse/cc-lift-general.md`](reuse/cc-lift-general.md). Lift rows gain a kind: `subobjects` (a `MonoLift`) or `createsLimits shape` (Mathlib `CreatesLimitsOfShape J U` along a structural step, `J` checked against the registered limits of that name). `RegistryState.resolveLimit` returns the registered presentation in the category, or the unique one returned along a creation lift, naming the lift. Registered `cat.finite_sets` and `lift.finite_sets.pullbacks` (Mathlib `FintypeCat.inclusionCreatesFiniteLimits`). **Acceptance (`LiftLimitProbes`):** the pullback of `Fin 3 → Fin 2 ← Fin 2` in finite sets is computed in `Sets` and returned along the lift (apex, legs, mediator, uniqueness); the resolver names the lift; wrong shape and wrong step are rejected. Returned cones over leaf realizers are (code gap: `gov-leaf-authority`). **Residual:** cartesian lifts of fibrations and preservation along adjunctions are not yet lift kinds; `resolveLimit` takes one lift step. | CC-LIFT | `cc-limits`, `cc-adjunctions` |
| `cc-refine` | **Open.** Reuse: [`specs/reuse/cc-refine.md`](reuse/cc-refine.md). A refinement by a property `P` is Mathlib's `P.FullSubcategory`; re-typing an object into it (the same object, data and images) happens only on a proof of `P`, proved in `lean-categories` or discharged generically by the kernel. A leaf's computation of `P` is an answer, judged by the suite, and never re-types an object. Containment follows `ιOfLE`. Equality of morphisms is the category's, in `lean-categories`; a computed equality is an answer. Registered `prop.is_finite` (`finiteHolds_iff`). **Acceptance:** `Fin 2 × ℤ/3` is re-typed into finite sets on a proof of finiteness, and `cardinality` resolves on it in finite sets with its value on the original; no leaf's answer re-types an object; undecided places nothing. Delivered 2026-09-29: `P.FullSubcategory`, `refineLE`, `prop.is_finite`; re-typing on a leaf decider's `Decision` and the leaf `equality` row are (code gap: `gov-leaf-authority`). **Residual:** containment and intersection of classifiers are not registry rows; refinement by structure classifiers is not re-typing. | CC-PROP, CC-DECIDE | `cc-leaf-boundary` |
| `cc-memo-resolve` | **Delivered 2026-09-29.** Reuse: [`specs/reuse/cc-memo-resolve.md`](reuse/cc-memo-resolve.md). `memo% (table) name (x) in "cat"`: the call of `method%`, resolved once and applied through `memoApply`, keyed by the rendered resolution and the input value; with `none` it is the plain call. **Acceptance (`RealizeProbes`):** over `[ℤ⁰, ℤ³, Fin 5, ℤ³, Fin 5]` the memoized and plain runs agree, the table holds one entry per distinct input after the first pass and none are added by the second, and every key is the resolution. **Historical scope:** these are 2026-09-29 observations of the named specimen, not a theorem of arbitrary leaves or a description of the present evaluator. Current retention, lookup and replay obligations are CC-MEMO/#69. **Residual recorded then:** resolutions are recomputed per elaboration; `ask%`, `run%` and `cell%` have no memoized form. | CC-MEMO | `cc-leaf-boundary` |
| `cc-backends` | **Delivered 2026-09-29 for the port.** Reuse: [`specs/reuse/cc-backends.md`](reuse/cc-backends.md). The core owns the port protocol (`CasContract/Port.lean`: framed backend port, `cas_port.py` reference implementation), never backend programs; each leaf owns the program behind its port, in any language. `connect` refuses an adapter announcing any operation that is not a registered operation id. The kernel reads each answer into the operation's declared result form or rejects it as `malformed`. Specimens: GAP kernels via `libgap` (`lim.groups.kernel`), with `--hostile=…` reproducing backend mistakes; Sage cardinality on `(ℤ/n)^k` (`passagemath-modules`). **Acceptance (`BackendProbes`, where GAP is installed):** an adapter announcing its own subgroup operation is refused at connection; an answer forgetting the inclusion or answering the whole group is rejected as malformed; GAP's and Sage's answers meet the suite's assertions. The leaf-supplied decoder (`backendOperation`) is (code gap: `gov-leaf-authority`). | CC-ADAPTER, CC-DECODE, CC-ROUTE | `cc-leaf-boundary`, `cc-limits` |
| `cc-specimens` | **Delivered 2026-09-29 (first run; re-run as nodes close).** Reuse: [`specs/reuse/cc-specimens.md`](reuse/cc-specimens.md). Specimen leaves register computations only; they show where the core is deficient. Formed modules by their form: `ℤⁿ` with a Mathlib bilinear map given by its formula (a map out of `M ⊗ M`, not a Gram matrix). **Acceptance (`SpecimenProbes`):** `cardinality` of `U = (ℤ², x₀y₁ + x₁y₀)` resolves by composition to the catalogue's composite, and its answer meets the suite (`ℵ₀`); the ring diamond and `𝔽₉` in two presentations (`CohereExecProbes`, `RealizeProbes`); the hostile orthogonal subgroup (`BackendProbes`). **Deficiencies found (nodes below):** `cc-realizer-first` (a call with two input forms for one category had no selection rule), `cc-refine-registry` (property classifiers had no registry row per property), `cc-forms-general` (forms on finite modules and `ℚ/ℤ`-valued discriminant forms had no registered construction). | all | `cc-leaf-boundary` |
| `cc-realizer-first` | **Delivered 2026-09-29 for the selection rule.** Reuse: [`specs/reuse/cc-realizer-first.md`](reuse/cc-realizer-first.md). A call starts from the receiver's declared input form (no source-less mode), and each step's registered computation is selected by the form reached so far. **Acceptance (`SpecimenProbes`):** `BilinModule(ℤ, ℤ)` with two input forms (Gram and form): `cardinality` resolves on each along its own computations (`ℵ₀`, `ℵ₀`, and `1` on the zero form on `ℤ⁰`), each answer judged by the suite. Selection through the leaf's `RealizedAction.id` is (code gap: `gov-leaf-authority`). | CC-SEP, CC-ROUTE | `cc-specimens` |
| `cc-refine-registry` | **Delivered 2026-09-29 for classifier rows.** Reuse: [`specs/reuse/cc-refine-registry.md`](reuse/cc-refine-registry.md). `lean-categories` `Classifier.ofProperty P` (the total is Mathlib's `P.FullSubcategory`, forgetful functor `P.ι`); `Classifier.holds_ofProperty`: the fibre over `X` is inhabited iff `P X`, proved once. Registered `clf.bilin_module.lattice` (`ofProperty isLattice`, total `cat.lattice`) and `prop.is_lattice`. `refine% (x) in "src" to "tgt"` re-types on a proof of the property, never on a leaf's answer; `ask% is_lattice` is a computation whose answer the suite judges. **Acceptance:** `refine% (Fin 2 × ℤ/3) in "cat.sets" to "cat.finite_sets"` is `some` on a proof of finiteness and `ℤ` is `none`; no leaf decider re-types an object. `refine%` driven by the forms leaf's registered decider is (code gap: `gov-leaf-authority`). **Residual:** property classifiers on a family fibre are registered per fibre, not along the family. | CC-PROP, CC-DECIDE | `cc-refine` |
| `cc-forms-general` | **Delivered 2026-09-29 for the construction.** Reuse: [`specs/reuse/cc-forms-general.md`](reuse/cc-forms-general.md). The discriminant is the registered cokernel `colim.bil_w_form.cokernel` of `L → L♯` in formed modules with varying values, generic in `R` (`lean-categories` `BilWFormCat.cokernelIsColimit`). What a presented cokernel denotes is `lean-categories`' `cokernelObject`; a leaf only computes on the declared input form. **Acceptance:** the A₂ discriminant group has order 3 (SPLAG ch. 4 §6.1) and its form satisfies `b([e₁],[e₁]) = [2/3] ≠ 0`, as assertions of the suite, gaps allowed. The leaf's denotation of cokernel handles (`WForms.lean`) is (code gap: `gov-leaf-authority`). **Residual:** `L♯` is not obtained from a registered metric-dual construction; change of values (`fun.lattice.change_value`) has no computation. | CC-FIB, CC-UNIV | `cc-colimits` |
| `cc-lift-faithful` | **Delivered 2026-09-29 for the kernel rule.** Reuse: [`specs/reuse/cc-lift-faithful.md`](reuse/cc-lift-faithful.md). `MorphismRule F` (a map below known to be the image of a morphism is lifted to it, computably) and `realizedLiftedLimitCone` over a faithful `F` reflecting the limit; reflection appears only in proofs. That the legs below are morphisms above is proved in `lean-categories` or discharged by the kernel, never supplied by a leaf. **Acceptance (`LiftFaithfulProbes`):** `ℤ/2 × ℤ/3` computed as sections of the pair diagram and returned to groups: apex of size 6, legs `x ↦ x div 3`, `x mod 3`; the mediator of `ℤ/6 → ℤ/2, ℤ/6 → ℤ/3` is the Chinese-remainder map. The leaf's `legs` proof is (code gap: `gov-leaf-authority`). **Residual:** a creation lift row names one step, so the returned limit is not yet a registry resolution along `Grp → Sets`. | CC-LIFT | `cc-lift-general` |
| `cc-colimits` | **Delivered 2026-09-29 for colimit rows.** Reuse: [`specs/reuse/cc-colimits.md`](reuse/cc-colimits.md). Limit rows carry `colimit` (a family of Mathlib `ColimitCocone`s). `colimitCoconeOfIso`, `realizedLiftedColimitCocone`, `realizedColimitCocone`. Registered `colim.sets.coproduct` (`Types.binaryCoproductColimitCocone`) and `colim.bil_w_form.cokernel`. **Acceptance (`ColimitProbes`):** `Fin 2 ⊔ Fin 3` has 5 elements, coprojections `[0,1]`, `[2,3,4]`, the descent of `![0,3]`, `![1,2,1]` is `[0,3,1,2,1]`, with factorization and uniqueness; a colimit family declared as a limit is rejected. The leaf's colimit identification (`colimr.sets.coproduct.finite`) is (code gap: `gov-leaf-authority`). | CC-UNIV | `cc-limits`, `cc-lift-faithful` |
| `cc-notebook` | **Delivered 2026-09-29.** Reuse: [`specs/reuse/cc-notebook.md`](reuse/cc-notebook.md). The old engine (`CasDsl/*`: value model, codecs, typing, routes, executors, the Sage bridge and port; its tests, `notebooks/boundaries.ipynb`, `tests/test_e2e.py`) is removed. `CasDsl` is `public import CasCatalogue` + `public import CasLeaves` and nothing else; `CasDsl.Notebook` is the kernel prelude. The demo's cells and `CasDslTests/Cells.lean` are generated from one list (`scripts/demo_notebook.py`), so the gate builds every notebook cell; `scripts/reexec_notebooks.py` re-executes `notebooks/demo.ipynb` through the `casdsl` kernel (`just test-ci`). **Checked:** gate green; `CasDslTests.Boundary` fails if any `CasDsl` module adds a registry row or declares a constant; the demo executes through the kernel (`method%`, `ask%`, `refine%`, `eq%`, `cell%`, `#resolve`) with genuine outputs. **Residual:** the kernel worker resolves its environment with `lake`, so the re-exec script puts elan on `PATH`. | all | the nodes above |
| `cc-failure-strata` | **Delivered 2026-09-29.** Reuse: [`specs/reuse/cc-failure-strata.md`](reuse/cc-failure-strata.md). `CasCatalogue/Failure.lean`: `Stratum` has the five kernel-visible kinds `invalid`, `noImplementation`, `ambiguousRealization`, `unavailable`, `malformed`; a wrong answer is acceptance's to detect. Every failure site of the surfaces is stratified: semantic errors are `invalid`; a missing registered computation is `noImplementation`; several applicable ones are `ambiguousRealization`; port failures map to `unavailable` or `malformed`; an answer the kernel cannot read into the declared result form is `malformed`. `#gaps "cat"` lists, for each method on the surface, whether it is computed or a gap. **Acceptance (`StrataProbes`):** the surfaces of sets, finite sets, groups and bilinear modules are equal with and without every leaf, and their gaps differ; an unknown method, an unregistered category and `annihilator` on sets are `invalid`; a receiver of two applicable computations is `ambiguousRealization`; a missing program and a failing backend are `unavailable`; an answer outside the result type is `malformed`. **Residual:** `resolveLimit` still reports failures as `Except String`. | CC-ADAPTER, CC-DECODE | `cc-backends` |
| `cc-acceptance-permanent` | **Open.** Reuse: [`specs/reuse/cc-acceptance-permanent.md`](reuse/cc-acceptance-permanent.md). The acceptance suite is the whole body of correctness evidence. An assertion is a proposition in the mathematical language, true, with an expected value from a formal proof, a cited known result or an independent oracle; it never names, inspects or imports a leaf, a handle, a backend or a representation, and is never established from an implementation's definitions. Admitted once and never changed for an implementation (`scripts/check_acceptance_permanent.py`: `--admit` for new assertions, `--correct` only for an upstream correction, under the acceptance role). An assertion no installed computation answers is a gap. **Acceptance:** editing an admitted assertion fails the gate; `|Fin 2 × ℤ/3| = 6`, `|(ℤ/4)^3| = 64`, `|(ℤ/7)^1| = 7`, `|(ℤ/5)^0| = 1`, `|ℤ| = ℵ₀`, the finiteness of `Fin 2 × ℤ/3` and not of `ℤ`, and `rev ∘ rev = id` on `Fin 3` are stated with their sources and established without any leaf definition. Delivered 2026-09-29: the permanence gate; the Lean assertions of `CasAcceptance/Permanent/*.lean`, proved by unfolding a leaf's denotation, with inputs from leaf handle constructors, and `#accept_backend`, are (code gap: `gov-leaf-authority`). | CC-TRUE, CC-DECIDE | `cc-failure-strata` |
| `cc-limit-surface` | **Delivered 2026-09-29 for the surface.** Reuse: [`specs/reuse/cc-limit-surface.md`](reuse/cc-limit-surface.md). `limit% shape (D) in "cat"` and `colimit% shape (D) in "cat"` resolve the registered limit (`resolveLimit`, taking creation lifts for limits), take the diagram in its declared presentation form, and return the registered cone with its apex's semantic value; the apex on presented data is a registered computation's answer. Failures are stratified: an unregistered limit is `invalid`; no computation for the diagram's form is `noImplementation`; several are `ambiguousRealization`. Upstream, re-pinned: `lean-categories` `5423142` (full and faithful `finite.forget.toFunctor`) and `carrierFunctor : BilWFormCat R ⥤ ModuleCat R`, registered as the structural `fun.bil_wform.carrier`, which acceptance found missing. **Acceptance:** the pullback of `[0,1,1]` and `[1,0]` in sets has 3 elements; the same pullback returned to finite sets has 3 elements; `Fin 2 ⊔ Fin 3` has 5 elements; the A₂ discriminant group has order 3 (SPLAG ch. 4 §6.1); each a cited assertion, gaps allowed; an unregistered equalizer in sets is `invalid`. Completing a cone with a leaf's apex handle and identification is (code gap: `gov-leaf-authority`). | CC-UNIV, CC-CALC | `cc-acceptance-permanent` |
| `cc-constructor-surface` | **Delivered 2026-09-29 for object rows and the surface.** Reuse: [`specs/reuse/cc-constructor-surface.md`](reuse/cc-constructor-surface.md). Upstream (`lean-categories` `413cd65`): the semantic row kind `object` (`ObjectEntry`: a Lean function from typed parameters to the objects of a registered category), rows `obj.sets.fin`, `obj.sets.integers_mod`, `obj.sets.integers_mod_power`, and `lim.sets.product`. `obj% "obj.id" (args…) in "cat.id"` builds an input from a registered constructor in its declared presentation form, so that assertions and notebooks name no leaf handle constructor; `hom%` builds a morphism likewise. **Acceptance:** the assertions of `cc-acceptance-permanent` and `cc-limit-surface` are stated through registered constructors, naming no leaf; an unregistered object and an object of another category are `invalid` (`StrataProbes`). The leaf `presentation` row (`Σ a : R, d.obj a ≅ X`) and `hom%` as a preimage along a leaf's denotation are (code gap: `gov-leaf-authority`). **Residual:** the A₂ discriminant and the finite-sets restatements need named objects of `cat.bil_wform` and `cat.finite_sets` upstream. | CC-UNIV, CC-CALC | `cc-sem-derive` |
| `cc-sem-upstream` | **Delivered 2026-09-29.** Reuse: [`specs/reuse/cc-sem-upstream.md`](reuse/cc-sem-upstream.md). The catalogue moved to `lean-categories` (`LeanCategories/Catalogue/`, namespace `CasCatalogue`, commit `60ba004`, pinned here): the symbolic calculus (`Syntax`), the realization witnesses of expressions (`Realization`, `FamilyFibration`, `Interpretation`, `Registry/Typed`), the category constructors and lifts, the property query (`Holds`), the semantic identities and rows, the semantic registry (`SemanticEntry`, `SemanticState`, its validators, `normalized_registry`), and every row. Here, `CasCatalogue/Registry/Extension.lean` keeps the registry of leaf registrations only, each against a registered operation's declared type; nothing in it carries meaning. **Acceptance:** `lean-categories` builds and audits its catalogue without `lean-cas-dsl`; `CasCatalogue` holds no semantic row and no semantic definition; the suite passes against the re-pinned release unchanged. | CC-SEP; architecture.md "Single semantic authority" | `cc-limit-surface` |
| `cc-sem-derive` | **Delivered 2026-09-29 with `cc-sem-upstream`.** `registryState` is the imported `semanticState` together with the leaf registrations. `addRegistryEntryChecked` passes a semantic row to `addSemanticEntryChecked`, which refuses every module outside `LeanCategories`. This repository has no semantic write path. **Acceptance:** `LeafBoundaryProbes`: a semantic row is refused in a leaf, the notebook, the kernel (`CasCatalogue.*`) and the probes, naming the rule. `SemanticProjectionProbes`: every semantic row visible here was written by a `LeanCategories.Catalogue` module, and the registry's semantic part equals `lean-categories`' semantic registry row for row. | CC-SEP | `cc-sem-upstream` |
| `cc-external-leaf` | **Delivered 2026-09-29 as the intake contract.** Reuse: [`specs/reuse/cc-external-leaf.md`](reuse/cc-external-leaf.md). A leaf may live in any package, written against the leaf contract only. Any module outside the core, its probes, the notebook and `lean-categories` that registers computations is a leaf (`isLeafModule`). It may not import the acceptance suite or the kernel's internals (`LeafBoundaryProbes`). The suite is run only by `lean-cas-dsl`'s harness over installed leaves; a leaf package never runs it. **Acceptance:** one computation in an external package meets a permanent assertion when the harness runs the suite over it; removing that package changes only the gaps. | CC-ADAPTER | `cc-constructor-surface` |
| `cc-p0-denotation-audit` | **Audit delivered 2026-09-28: [registry-denotation-audit.md](registry-denotation-audit.md). §4 records the owner's rulings (forms cocartesian over total modules; lattices as refinements of Bil; integrality/evenness as value containment; frames abandoned for resolutions). Closed 2026-09-28; its code consequences are `cc-fib` and `cc-resolutions`.** Audit every registry entry kind (`NamedCategoryEntry`, `CategoryFamilyEntry`, `ClassifierEntry`, `FunctorEntry`, `StructuralPortEntry`, `OpaqueCategoryEntry`) and every `CategoryExpr`/`FunctorExpr`/`NatTransExpr` constructor for its mathematical denotation. For `CategoryFamilyEntry`/`familyApp`: state the fibration (or pseudofunctor with variance) each registered family denotes, citing FOUNDATIONS §13.2 / §83–86 for modules and bimodules; list every family that cannot name one. **Acceptance:** a table in FOUNDATIONS (or a linked appendix) with one row per kind and per registered family, each with its denotation and source; no row reads "parameterized by". Findings that require code changes become children of `cc-fib`. | CC-TRUE, CC-FIB | none |
| `cc-fib` | **Forms tower delivered 2026-09-28 in Lean: `Bil →p ∫Mod →q CommRing` with `p.IsCofibered` (FOUNDATIONS 31.2b/31.2c, [audit §6](registry-denotation-audit.md)); Module fibration registered 2026-09-28: `familyTotal`/`familyFibreInclusion`/`familyReindex`, `cat.modules_total`, `fun.modules.{fibre_inclusion,reindex,underlying}` with U on the total category; ℤ→ℤ/4 cardinality by `rfl`. Fibration rows 2026-09-28: `FibrationEntry` with checked `IsFibered`/`IsCofibered` evidence; `fib.modules`, `fib.modules_ext`, `fib.bilin_forms` registered. Fibre equivalences 2026-09-28: `Fiber p (R, W) ≌ BilinModuleCat R W` (`BilinFormsOverRings.fibreEquivalence`). Lattices as a refinement of `Bil` 2026-09-28: `clf.bilin_forms.lattice`, `cat.lattices_over_rings` (first registered refinement); `cat.integral_forms` = pullback of `Bil` along the regular section (`fun.modules_ext.regular_section`); `cat.integral_lattices` = its lattice refinement along the registered projection `fun.integral_forms.to_bil`. Lattice conditions as classifiers 2026-09-28 (lean-categories `e71c252`, `CasCatalogue/LatticeRefinements.lean`): `clf.bilin_forms.{finite,free,even,unimodular}` on `Bil`, uniform over rings and value modules (evenness `b(v, v) ∈ 2W`, unimodularity a bijective adjoint), and the refinements `cat.finite_projective_lattices_over_rings`, `cat.finite_free_lattices_over_rings` (of the former), `cat.unimodular_lattices_over_rings`, `cat.even_integral_lattices` (of integral lattices; at `W = R` evenness is `IsEven`, the `2R`-integrality of the diagonal form: `isEven_iff_exists_two_smul`, `isEven_iff_diagonal`), along registered projections to `Bil`. General `I`-integrality/`I`-modularity need an ideal of each object's own ring and are not uniform classifiers; they stay fibrewise (`IsIIntegral`, `IsIModular`). Open: retiring the discrete forms and lattice families needs fibres of refinements over `(R, W)` as registered expressions.** Represent varying categories as fibrations. Register \(p:\int_R R\text{-}\mathbf{Mod}\to\mathbf{Ring}\) as a cartesian fibration with Mathlib's `ModuleCat.restrictScalars` as reindexing (and the cocartesian structure from `extendScalars` where used, with variance stated at each use). Fibre inclusions \(\iota_R\) and reindexing \(\varphi^{*}\) become `FunctorExpr` values derived from the fibration entry. The underlying-set functor is registered once on the total category. **Acceptance:** the CC-FIB acceptance — fibre over \(R\) evaluates to `ModuleCat R`; restriction along \(\mathbb Z\to\mathbb Z/4\) resolves as reindexing; cardinality agrees across the two fibres because both factor through the one total-category \(U\). | CC-FIB, CC-TRUE | `cc-p0-denotation-audit` |
| `cc-resolutions` | **2026-09-28: FOUNDATIONS Defs. 13.10–13.11 and Remark 13.12 state resolutions, truncations, presentations (2-truncated free resolutions), bases (length-zero free resolutions) and framings, with sources; §13.5–13.6 marked superseded. Code 2026-09-28 (lean-categories `a16a5d6`): `Modules.Framed` is now `Modules.TruncatedResolutions` — `FreeCover R I` (1-truncated free resolutions), `BasedModule R I` (length zero), `Coord R I`; the six families are registered as `cat.free_cover`, `cat.based_module`, `cat.coord` and their indexed variants; the formed, quadratic and lattice variants are the `Valued/Based` modules. Open: the owner's further framed-bundle conditions (stated as open in Remark 13.12).** State, with sources, the theory of resolutions that replaces frames: augmented resolutions, their truncations (a classical presentation is the 2-truncation), and the general framework (projective/free, simplicial, cofibrant, comonadic). Then framed bundles as bundles with resolutions satisfying the stated conditions. Retire FOUNDATIONS §13.5–13.6 and the six frame families. **Acceptance:** a FOUNDATIONS section with citations for each notion; no code until it exists. | CC-TRUE | `cc-p0-denotation-audit` |
| `cc-quad-basechange` | **Delivered 2026-09-28 (lean-categories `aaf7af3`, pinned here) without the Γ₂ port: `QuadraticMap.baseChange'` is base change of any quadratic map over any commutative rings, `(s ⊗ m) ↦ s² ⊗ q(m)`, built by descent along the free cover `R^(M) ↠ M` (right exactness of `S ⊗ −`) from Mathlib's basis-dependent `QuadraticMap.toBilin`, unique by `baseChange_ext` (FOUNDATIONS §15.6, "Construction used in the Lean code"); `QuadWFormCat` scalar extension and its identity and composition comparisons hold with no hypothesis on `2` (a `ℤ → ℤ/2` specimen checks characteristic 2); evenness is `isEven_iff_diagonal` — the `2R`-integrality of `Δ(L, b)` along the diagonal functor `Δ : Bil ⥤ Quad` — and over `ℤ` `2 ∣ b(v, v)`. Open: the Γ₂ representability and Roby's base change of Γ remain unformalized (wanted for themselves, no longer blocking); the finer projection `Quad → ∫Mod` (as `fib.bilin_forms` is for `Bil`). Quad fibration 2026-09-28 (lean-categories `2794bef`): `quadBaseChangePseudofunctor` (pseudofunctor laws on underlying modules), `QuadFormsOverRings` its Grothendieck construction, registered as `cat.quad_forms_over_rings` with `fib.quad_forms` — its projection to commutative rings, cocartesian (`Pseudofunctor.Grothendieck.isCofibered_forget`).** Characteristic-free base change of quadratic maps (COMPLAINTS: "Quadratic base change requires `2` invertible"): search and read `DividedPowers4` (and further corpus formulations) for `Γ₂` and its base change; state the construction in FOUNDATIONS §15.6 with its source (Roby's universal property of `Γ₂`); only then build `Quad`'s pseudofunctor exactly as for `Bil`. **Acceptance:** `QuadWFormCat` base change and its coherence hold with no `Invertible 2` hypothesis, and evenness over `ℤ` is the `I = 2R` integrality of `Δ(L, b)`. | CC-FIB, CC-REUSE | `cc-fib` (forms part) |
| `cc-constructors` | **Delivered 2026-09-28: `CategoryExpr.construct` with `ConstructorArg` (category / symbolic object / registered functor), `ConstructorEntry` (signature + semantic definition), registration checking `category ≡ semantics(registered denotations)`, manifest export and round-trip. Constructors: arrow, core, slice, coslice, elements, subobjects (full subcategory of `Arr(C)` on monos), functor category. Registered: `Arr(Sets)`, `Core(Sets)`, `Slice(Sets,X)`, `Coslice(Sets,X)`, `Subobjects(Sets)`, `Elements(U)` = points of modules, `Fun(Sets,Sets)`; composite `Elements(U) → ∫ᶜMod → Sets` typed by `comp`. Open: `Disc`, `MonoOver`, diagram categories as registered constructors; the rest of #54 §2–§5 (module-family signatures, exact-host fixtures).** Add #54's generic `CategoryExpr.constructor` case with typed constructor entries for `Elements`, `Arr`, `Core`, `Disc`, `Over`/`Under`, `MonoOver`/`Subobject` and functor categories, each evaluating to its Mathlib construction. **Acceptance:** CC-CALC's acceptance, plus #54's `Subobjects(Sets)` and slice/arrow/elements acceptance items. | CC-CALC, CC-TRUE | `cc-p0-denotation-audit` |
| `cc-actions` | **Open.** A functor entry of the catalogue carries its object and morphism actions as mathematics (spec §8); the one-constructor-per-map pattern is retired. Executing a step on presented data is a registered computation against the step's declared type, believed by nothing. **Acceptance:** CC-ACTION's acceptance on the formed-module → module → set chain over the fibration of `cc-fib`: the composite lattice → sets is ordinary composition and no lattice-to-set row exists; `A₂ ↦ ℤ²`, `E₈ ↦ ℤ⁸` and the A₂ root swap exchanging coordinates are assertions of the suite, met by computations along the route; negative rows (an action for another functor, a non-action, an unregistered functor) are rejected. Delivered 2026-09-28: the composites (`Leaves/Lattices/Valued/ActionProbes.lean`); the leaf `Realizer`/`Denotation` and `Action.Realizes` proof are (code gap: `gov-leaf-authority`). | CC-ACTION, CC-SEP | `cc-fib`, `cc-constructors` |
| `cc-resolve` | **Delivered 2026-09-28.** `CasCatalogue/Resolve.lean` + `ResolveSyntax.lean`. Edges are functor rows marked `structural` (underlying-object functors only; see CC-UNIFORM) and classifier forgetful functors; `.method` rows (#53 §7) name a registered functor at its owner (`object` or `isoInvariant` on `Core(owner)`). Every simple route is enumerated; none is `notApplicable`, several are `ambiguous` with all routes listed; `via` names a port; no shortest-path, order or priority rule. `method% name (x) in "cat.id"` elaborates to the checked composite `FunctorExpr` and runs the registered computations along it on `x`; `#resolve` reports the route. Registered: `card : Core(Set) ⥤ Disc(Card)` (`lean-categories` `Foundation/Cardinality.lean`) as `fun.sets.cardinality` with method `meth.cardinality`; the ring's two ports from Mathlib (`forget₂`, `AddGrpCat.toGrp`). **Acceptance (`ResolveProbes`):** a formed module resolves by a 3-step route, a lattice by a 4-step route; the cardinalities of `A₂`, `E₈` (`ℵ₀`) and the zero lattice (`1`) are assertions met along them; the term contains the composite and no string-keyed call; rings reach sets along two distinct routes and `cardinality` on rings is ambiguous naming both, resolved by `via`; unknown and inapplicable methods are reported. Composing leaf `RealizedAction`s is `cc-realize-2cat`'s gap. | CC-TRANSPORT, CC-UNIFORM, CC-RESOLVE | `cc-actions` |
| `cc-cohere` | **Delivered 2026-09-28: `.comparison` rows (`ComparisonEntry`: two structural routes between the same endpoints + evidence) validated at registration: both sides must be structural routes source → target, differ, and the evidence must be a Lean `Iso` between their Mathlib composites (`Registry/Extension.lean`, `validateComparison`, `mkFunctorComp`). The resolver merges candidate routes of one method that differ by one registered comparison (transitively), picks a representative only after that (canonically, by rendered route), and records the comparisons in the resolution's provenance. Registered `cmp.rings.carrier` with evidence `LeanCategories.Algebra.ringCarrierComparison` (lean-categories `8017e88`: the identity natural isomorphism between the multiplicative and additive routes `Ring → Set`). Acceptance in `CohereProbes.lean` / `ResolveProbes.lean`: without the row, ring `cardinality` is ambiguous naming both routes; with it, it resolves and names `cmp.rings.carrier`; a method owned at magmas stays ambiguous on rings (the ports stay distinct where they carry structure); unrelated evidence, a side that is not a route to the target, and a self-comparison are rejected.** Route identification by registered `NatTransExpr` comparisons. **Acceptance:** CC-COHERE's acceptance and the ring diamond (additive vs multiplicative distinct at monoids, identified at sets by a registered comparison). | CC-COHERE | `cc-resolve` |
| `cc-immediate` | **Delivered 2026-09-28, decided by Lean definitional equality, not by name: a structural functor row whose Mathlib functor is definitionally the composite of an existing structural route between its endpoints is rejected naming that composite (`validateImmediateFunctor`); a second port with the same endpoints is admitted. A method row whose functor is definitionally an existing method pulled back along a structural route (through `Functor.core` for iso-invariant methods) is rejected as below its generating level, naming the method and route (`validateMethodLevel`). The whole registry re-validates under both rules. Acceptance in `ImmediateProbes.lean`: `Lattice → Mod_R` written as `ι ⋙ forget` is rejected naming `fun.lattice.forget_form ⋙ fun.bilin_module.forget`; a formed-module cardinality defined as the pulled-back cardinality is rejected naming `meth.cardinality` and its route; registered rows and methods re-validate.** Admission rules for catalogue rows: reject a functor that duplicates an existing composite with no new content; reject a method below its lowest generating level. **Acceptance:** CC-IMMEDIATE's acceptance with negative tests. | CC-IMMEDIATE | `cc-resolve` |
| `cc-props` | **Delivered 2026-09-28 for classifiers and resolution.** Classifiers are the only owners of property meaning (`Classifier.Holds`, FOUNDATIONS Def. 46.4: the classifier's fibre over `x` is inhabited). Rows: `.property` (a surface name for a classifier; `receiver` makes it an alias, e.g. `is_abelian` on groups only). A property computation registers against a classifier with a three-valued result (true, false, undecided); a computed decision carries no evidence, and the suite judges it. An atom category that is a registered classifier's total, or a property subcategory of a registered atom, is rejected (this found `cat.semigroups`, `cat.freemodules`, `cat.finitelygeneratedmodules`, `cat.finiterankmodules`, `cat.division_rings`, now classifier totals). `ask% name (x) in "cat"` resolves the property and runs the registered computation. `lean-categories` `7d41594` fixed four property predicates that asked for some structure on the carrier instead of the object's own. **Acceptance (`PropsProbes`):** `is_abelian` is commutativity of the multiplicative port; ring `is_commutative` is ambiguous despite the carrier comparison; `is_abelian` is not on rings; an abelian-groups atom and an unowned property are rejected; undecided never becomes false; `ℤ/3` abelian and `S₃` not are assertions of the suite. The leaf `.decider` rows with evidence (`Decision` proofs) are (code gap: `gov-leaf-authority`). | CC-PROP, CC-DECIDE | `cc-resolve` |
| `cc-universal` | **Delivered 2026-09-28 for subobjects.** A subgroup is an object of the registered `Subobjects(Grp)` (a mono arrow). `fun.subobjects_groups.domain` (structural) makes every subgroup inherit group-level operations; `fun.subobjects_groups.inclusion` into `Arr(Grp)` is the method `inclusion`, the retained universal datum; intersection and inverse image are Mathlib's `Subobject` meet and pullback. A hostile backend's answer (unclosed generators, a false label, a method inventory) is read by the kernel into the declared result form (the closure, the table and the embedding) or rejected as malformed. **Acceptance (`UnivProbes`):** `A₃ ↪ S₃` read from the hostile answer has cardinality 3 and is abelian (assertions of the suite, whatever the backend's label), and its `inclusion` is the embedding `{1, r, r²}`; `inclusion_is_semantic` is a theorem; an apex-only reading does not typecheck; an action on bare groups is rejected for the subobject's domain. The reading being a leaf's decoder (`Leaves/Algebra/Subgroups.lean`) is (code gap: `gov-leaf-authority`). | CC-UNIV | `cc-constructors`, `cc-resolve` |
| `cc-lift` | **Delivered 2026-09-28: `CasCatalogue/Lift.lean` — `MonoLift U`, cartesian lifts of monomorphisms along `U` up to the canonical isomorphism over the base. `.lift` rows are validated so that the evidence's `U.mapArrow` is the route step's functor; methods may be marked `returnsToSource`, and resolution then requires a registered lift for every route step or fails with `missingLift` naming the step, recording the lifts used as provenance. `kernel` is owned by modules (`LeanCategories.kernelFunctor : Arr(C) ⥤ Subobjects(C)`, lean-categories `9428a02`, complete universal data `(K, ι)`), reached from formed-module morphisms along the structural `Arr(BilinModule) → Arr(Mod_R)`, and lifted back by `lift.bilin_module.restrict`, the restriction of forms (`BilinModuleCat.restrict`). `formedKernel f` is that lift; its form is the restriction (`formedKernel_pairing`, by `rfl`) and `f` kills its elements (`kernelSubmodule_map`). `Constructors.isMonoArrow` now defers to `LeanCategories.isMonoArrow`. Acceptance in `LiftProbes.lean`: the formed-module kernel resolves with the lift in its provenance; with the lift row removed it reports the missing lift on `fun.arrows_bilin_module.forget`; lift rows for the wrong step or with non-lift evidence are rejected. Executing kernels on presented data is a registered computation whose answers the suite judges (`cc-realize`, `cc-adapter`).** Operations returning to the source side require registered lifts, sections, preserved limits or adjunctions. **Acceptance:** CC-LIFT's acceptance: the kernel of a formed-module morphism is a formed submodule via the registered restriction of forms; without it, a missing-lift diagnostic. | CC-LIFT | `cc-universal`, `cc-cohere` |
| `cc-realize` | **Open.** The registry of leaf computations, keyed by semantic `FunctorExpr`/classifier (#53 §10 `BackendRealizationEntry`): each registration is (operation id, input form, implementation). `run% m (x) in "cat"` runs the selected computation and returns a value of the declared result form, with no status, proof or certificate; `using "impl"` selects one of several registered computations of the same composite. A memo table is keyed by explicit application (`Memo.lean`). Two presentations of a finite field stay distinct, and a comparison between them is mathematics of the catalogue (CC-CARRIER); `transport% (x) from K₁ to K₂` moves elements only along such a comparison. **Acceptance:** formed-module cardinality computed by several registered computations, each answer judged by the suite and none carrying a status; a receiver without a declared input form is rejected; cached/uncached observations use the declared mathematical relation and independent expectation under CC-MEMO; required selected results and their maps are retained; `𝔽₉ = 𝔽₃[x]/(x²+1)` and `𝔽₃[y]/(y²+y+2)` stay distinct and their equality is not decided true; `x ↦ y + 2` transports along the catalogue's comparison and its absence is reported as absence. Delivered 2026-09-28: `Memo.lean`; `Trust`, `Result` statuses, `TrustedImplementation`, `CertifiedImplementation`, leaf `.realizer` denotations, leaf `.handleIso` isomorphisms and `run% … proved` are (code gap: `gov-leaf-authority`). | CC-SEP, CC-ROUTE, CC-MEMO, CC-CARRIER | `cc-actions`, `cc-props` |
| `cc-adapter` | **Open.** The leaf contract command registers exactly (operation id, input form, implementation): no other field exists, so a category, method, property, placement, forgetful route, coercion, natural transformation, denotation, proof, identification, evidence or status is unrepresentable (spec §5). The kernel reads a backend answer (`BackendResult { operation, encoded }`) into the operation's declared result type or rejects it; for `op.groups.kernel` the answer must supply `(K, ι : K ↪ G)`, and one missing its inclusion is malformed. **Acceptance:** CC-ADAPTER (the registration type has exactly the three fields, and replacing every installed leaf changes no meaning, type or available operation) and CC-DECODE (a result missing its defining arrow is rejected; the kernels of `sign : S₃ → ℤ/2`, the trivial map and `id_{S₃}` meet the suite's assertions `A₃`, `S₃`, `1`). Delivered 2026-09-28: `register_leaf` refusing ten forbidden kinds (`AdapterProbes`); its five permitted kinds carrying denotations, proofs, evidence and statuses, and the leaf decoder `KernelDecode.lean`, are (code gap: `gov-leaf-authority`). | CC-ADAPTER, CC-DECODE | `cc-realize`, `cc-immediate`, `cc-universal` |
| `cc-closure` | **Delivered 2026-09-28.** `RegistryState.closure` and `#methods "cat"` compute a category's operation surface (objects, and morphisms through the arrow constructor) from the registry at query time: every method and property whose owner is structurally reachable, with its route, or with why it does not resolve (ambiguity, missing lift). Functorial constructors act on the structural graph (`FunctorExpr.constructMap` with `ConstructorEntry.functorialAction`: `Arr` by `Functor.mapArrow`, `Core` by `Functor.core`), so `Arr(U)` is a derived edge. `rank : Core(Mod_R) ⥤ Disc(Card)` (`lean-categories` `6fcabb7`) is registered as `meth.rank`. **Acceptance (`ClosureProbes`):** a new category formalized upstream with one property classifier on `Mod_R`, declaring no operation (torsion-free modules), gets `cardinality` and `rank` resolved and `kernel` on its morphisms reported with its missing lift; lattices inherit `rank`, and `rank(A₂) = 2`, `rank(E₈) = 8` are assertions of the suite. CC-CLOSURE's "inherits `kernel` with no further declaration" holds only up to CC-LIFT: an operation returning to the source needs a lift in the catalogue (spec §9, question 4). **Latest-main integration finding (2026-10-20):** hosted candidate `8be6fe8` with mathematics `80520813` fails the unchanged `LiftProbes`: the direct constructed forgetful route and the constructed fixed-value/carrier composite are distinct, and the resolver finds no registered comparison between them. The published base-category carrier comparison is present; constructor metadata publishes an action on functors, not an action on cells. The owning obligation remains open until the existing formal inputs and generic resolver justify this constructed coherence; no edge is removed, comparison invented, or positive assertion weakened. The same hosted run also exposes a stale single-route control in `CohereProbes` after the new base routes were added. Neither failure is B0 completion. | CC-CLOSURE | `cc-resolve`, `cc-cohere`, `cc-lift` |

## Order

The B0 acceptance table fixes the obligations; construction directives A–D give their operational
dependencies. Independent source work may proceed in parallel. Integrated acceptance and exit
trials consume their actual prerequisites at one compatible tuple. Historical nodes are detail for
the rows that cite them, never an additional global stage barrier.

## What is explicitly not in this plan

- Reproducing `sage-categories`' kernel: C3, dynamic classes, initializer threading,
  construction retention, state grafting (spec §3).
- A second semantic registry in `lean-cas-dsl` (spec §7, #53 §7).
- Certificates, trust levels, checkers or any other standing for a leaf or a backend: nothing from
  a leaf is trusted ([architecture.md](architecture.md), "The evidence model").

</details>
