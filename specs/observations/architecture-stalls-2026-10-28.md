# Why kernel development keeps stalling

Assessment date: 2026-10-28. Primary window: October 21–28, with close inspection of October 25–28. Earlier repositories supply architectural history.

The main recurring failure is **loss of selected mathematical or computational data at an interface, followed by attempts to reconstruct it downstream**. The successive projects have moved this problem: from Sage parents and category methods, through a categorical compiler backed by Python inheritance, into Lean elaboration and execution records. Lean has strengthened the formal semantic boundary. It has not yet made all the interpreter's internal relationships invariant by construction.

This produces a repeatable stall. A local consumer exposes missing context. A repair retains that context in another record or path. Adjacent consumers still use the earlier representation. Their next combined run exposes another loss, contradiction, or missing conversion. The result is substantial implementation activity without a stable extension boundary.

The evidence supports completing that boundary and removing its competing paths. It does not establish a need to replace the mathematical architecture, weaken the independent assertions, or change the computation-evidence model.

## Scope and evidence

This is a diagnosis from repository source, commit diffs, recorded experiments, and a directly inspected hosted build log. No new Lean or Sage execution was performed for this assessment. Historical experiment reports are identified as such; they are not current passing results.

| Source | Inspected revision or boundary |
| --- | --- |
| Active kernel development | `work/kernel-v1-20261023`, `362cb29f77525132519761046ae8ef14bb8bfa0b`; PR #67 |
| Executable source in that branch | `60829a1f7db040f6a8ae394777c0a10bc00d3946`; subsequent commits through `362cb29` change documentation, with no `CasCatalogue` delta |
| Published main | `6c424c4`; the substantial recent implementation is on the development branch |
| Recovery branch | `work/kernel-v1-recovery-20261028`, `c8279ee`; preserved drafts, not an accepted replacement |
| Hosted execution evidence inspected directly | Run `40652257963`, job `122694851193`, at `60829a1` |
| Sage categorical predecessor | `sage-categories` at `37ec1642fe19f24fb00f402fe45350341ebf6920`, plus historical issues and their corrections |
| Research implementation history | `research` through `681c152e`; selected historical repair diffs |
| Extracted Sage implementation | `sage-extensions` at `7169170b`, including its constructor and readiness assessments |

Commit frequency, source size, documentation volume, and passing-test totals do not establish architectural quality or completion. The findings below use specific lost relationships and the consumers that expose them. The inspected record cannot support a percentage allocation of development time to each cause.

## The progression: what each replacement gained

### Research and sage-extensions: mathematical relationships became runtime conventions

The earlier implementation already sought category-owned operations. Its defects show why choosing the right owner in prose was insufficient.

In [research `fa231845`](https://github.com/dzackgarza/research/commit/fa2318454826c2b128d640ab77dfeb3b544f8afa), consumers of `LLL_gram` disagreed about the direction of its basis change. The repair uses the columns of the returned matrix and the relation `G_new = Uᵀ G U`. Previously, Babai rounding transposed the map, while successive-minima enumeration used the wrong transformed Gram matrix. A bare matrix did not carry the selected source frame, target frame, and map direction that its consumers needed.

[Research `e8866fb1`](https://github.com/dzackgarza/research/commit/e8866fb1f232deed6c105e80cbbfc580732c90ed) records a related cluster. Fixed-morphism constructions had lost their fixed category. A selected framing lift had been replaced by a general solver that recursed. Framing detection still depended on a retired category instead of the retained resolution. A shared morphism class also conflated unital ring morphisms with rng morphisms. These are distinct local defects with a common architectural feature: construction data and mathematical distinctions were spread across parent classes, method order, flags, and caller conventions.

The maintenance tail follows from that arrangement. A correct local result does not ensure that a later operation receives its defining map, base ring, framing, or exact morphism category. Every new consumer must rediscover which pieces another construction retained.

### Sage-categories: better mathematics, still a lossy runtime realization

This project made a substantive advance. It represented selected structure functors, retained their images, distinguished refinement from forgetting, and developed universal-construction interfaces. It also found useful execution machinery in CAP, Catlab, Maude, DisCoPy, and homotopy-core. Its [execution reuse assessment](https://github.com/dzackgarza/lean-cas-dsl/blob/362cb29f77525132519761046ae8ef14bb8bfa0b/specs/reuse/cross-repository-execution-prior-art.md) identifies mechanisms worth retaining.

Isofibrations were central. The [functor specification](https://github.com/dzackgarza/sage-categories/blob/37ec1642fe19f24fb00f402fe45350341ebf6920/specs/functor.md#structure-functors-and-inherited-classes) ties inherited implementation to selected isofibrations, with faithfulness required in that selection context. This distinguishes access to some underlying datum from justified transport of structure. Isofibration alone does not supply a lift of every limit, quotient, or arbitrary morphism; those need the appropriate additional formal structure.

The runtime still compiled these selections into classes. The same specification assigns precedence by declaration order and uses controlled C3 with a shared occurrence. [Issue #26](https://github.com/dzackgarza/sage-categories/issues/26) exposes the mismatch: a semiring needs separate additive and multiplicative monoid images, but a shared monoid implementation occurrence carried mixed state. A local shadowing method could conceal the problem while a later generic monoid method remained exposed.

Other failures show that refinement and ownership were not local operations:

| Historical failure | Architectural significance |
| --- | --- |
| [#31](https://github.com/dzackgarza/sage-categories/issues/31): deciding concreteness of an underlying category caused an existing module to lose `action()` | Learning a property changed another object's implementation surface |
| [#33, corrected diagnosis](https://github.com/dzackgarza/sage-categories/issues/33#issuecomment-5563959264): intersection discarded an independently declared subcategory | Refinement changed the owner through which an already retained inverse was retrieved |
| [September 27 readiness assessment](https://github.com/dzackgarza/sage-extensions/blob/7169170b3c47e3af4da6279f47f6cd4108694a2f/docs/sage-categories-readiness.md): narrowing lost a fixed-endpoint constructor owner | A map datum reached the constructor for an endpoint pair |
| Same assessment: full-subcategory colimit dispatch bypassed a supplied lifting | A valid module quotient could not use the generic construction interface |

The cited issues are historical and closed. Their relevance is the mechanism, not a claim that those exact cases still fail. In particular, #33's corrected cause is intersection's loss of a declared operand, not the earlier suspected role-source failure.

Dynamic typing amplified these problems, but “Python was weak” is incomplete. The decisive design choice was using shared class occurrences and mutable placement to stand for distinct selected mathematical structures. A more disciplined Python representation could preserve more distinctions; a Lean record can still erase them.

### Lean-cas-dsl: formal authority is stronger; operational preservation is unfinished

The intended separation is sound for the stated goal: `lean-categories` owns mathematical meaning; the kernel derives the language and computational requests; leaves return untrusted computational data. Installing an implementation must not decide which objects or operations exist.

The current kernel also has real improvements. [`Resolve.classify`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Resolve.lean#L162-L197) collects comparison witnesses and competing comparisons. [`resolveMethod`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Resolve.lean#L409-L426) rejects unresolved comparison ambiguity and requires a designated source route. The old first-match findings in the September replacement audit do not describe this code.

The remaining difficulty is preserving those choices through execution. Formal soundness of an accepted Lean term does not establish that the runtime retained the intended producer, executed its selected action, or reused the actual result. Those are additional obligations of the interpreter's representation and execution boundary.

## What the recent window shows

| Period | Evidence | Stall exposed |
| --- | --- | --- |
| October 21–22 | [`212ba38`](https://github.com/dzackgarza/lean-cas-dsl/commit/212ba384d071b310f96e181d4452284aefd6214e) records expensive import, elaboration, and rebuild feedback; subsequent changes alter local/CI checking | Even a small semantic repair has expensive feedback; work-selection and checking rules become repair work themselves |
| October 23–24 | The kernel-MVP requirement replaces assertion-by-assertion selection; `9630f54`, `8938fd5`, `6feddb8`, and `263d55d` successively extend interpretation, complete endpoints, lift selections, and retained parameters | Passing a selected operation had not established compositional coverage of its public interface |
| October 25–26 | `ac8a31e`, `d7cfafc`, `5ab0edf`, `e4a1fd0`, `7462a36`, and `8f454d6` repair ownership, construction data, nested record decoding, scalar validation, and actual endpoint handling | The same context-preservation obligation reappears in lifts, composites, records, and refinements |
| October 27 | [`112dc2a`](https://github.com/dzackgarza/lean-cas-dsl/commit/112dc2a63a8051b240bc6286e7525bec6430a406) and [`de03ac0`](https://github.com/dzackgarza/lean-cas-dsl/commit/de03ac04ae9bf75fd5660f4cd4cadda3a6f79e47) introduce captured occurrences and a common invocation lifecycle | Earlier preparation could later recover a different input through an equal-expression cache entry; pending data and completed data also needed separation |
| October 28 | `3a4b84e` adds producer anchors; the inspected `60829a1` CI run builds producer probes but rejects existing consumers with producer-key conflicts | The new invariant is enforced locally while old callers still use incompatible recording paths |
| October 28 | The [handoff](https://github.com/dzackgarza/lean-cas-dsl/blob/362cb29f77525132519761046ae8ef14bb8bfa0b/HANDOFF.md#current-continuation-state--2026-10-28) records lost unpublished checkpoints and recovered source with unverified remaining integration | Workspace loss is a separate interruption; source recovery does not recover an integrated runtime result |

The chronology establishes recurring mechanisms, not that every repair was unnecessary. Several changes make real defects visible and correctly refuse inconsistent state.

## The high-level failure modes

### 1. Mathematical identity, presentation, and computation identity are conflated

An object with a chosen structure, its underlying carrier, a computational presentation, and the particular computation that produced data are different things. Equality in one sense does not identify the others. This is the connection between the semiring diamond, the lost inverse owner, and the current cache failures.

Current [`Trace`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Trace.lean#L465-L560) still stores nodes by `Expr`. `recordProduced` adds a fresh transparent occurrence anchor. `record` rejects conflicting metadata at an existing key. This is a useful stronger check. It does not by itself migrate every producer and consumer.

There is a concrete conflicting path in [`Language.typedParameter`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Language.lean#L1568-L1605). `checkedRouteAction` can return an expression already anchored to a retained route. The multiple-presentation case then records a different `.parameterEquivalence` node at that representative. The earlier node's producer identity and the new semantic-view metadata are competing for one storage key.

The [hosted job log](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40652257963/job/122694851193) confirms the wider integration failure. `ProducerOccurrenceProbes` builds, while `ParameterStructureProbes`, `StructuredParameterProbes`, `DeclaredProductContextProbes`, and other consumers report `distinct selected producers share one executable trace key`. The source path is a concrete conflict mechanism; it is not proven to be the first failing site of every affected probe.

**Causal conclusion:** a new identity mechanism cannot close the problem while old operations still reinterpret or overwrite its keys. The invariant has to govern all producers and subsequent views of the migrated computation.

### 2. Strong types surround records whose important relationships remain conventional

The current [`Wire` and `WireSnapshot`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L214-L289) keep `form` and `payload` as independent fields. They also carry optional category context, endpoints, invocation, framing, and lift state. [`ServiceRequest.Prepared`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/ServiceRequest.lean#L139-L178) has separate result-role booleans and optional interfaces. [`Wire.completedData`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L776-L787) derives completion from payload classification or observation flags.

Lean checks the field types as declared. These declarations do not themselves require the payload to belong to the complete selected interface, or make every contradictory role/lifecycle combination unconstructible. Existing validators can reject many such combinations. The architectural issue is that callers can still construct them and must remember which checks and fields belong together.

**Causal conclusion:** the project has moved some enforcement from Python into Lean runtime validation without yet preserving every checked relation in the internal value's construction boundary. That leaves agents responsible for distributed invariants. A nominal form index alone would not repair this; the complete selected context, dependent parameters, endpoints, and positioned ownership must remain associated.

### 3. Execution has several representations of the same evolving result

The [`Harness`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L2189-L2227) retains expression-keyed results, action executions, replies, services, derivations, service operands, and invocation executions. [`InvocationExecution`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L660-L688) adds a captured input and optional result; retained fields and intermediate results have further state. Different tables can legitimately serve different purposes. Their coexistence becomes a defect when more than one path can select or update the authoritative result.

The [October 27 diagnosis](https://github.com/dzackgarza/lean-cas-dsl/blob/362cb29f77525132519761046ae8ef14bb8bfa0b/HANDOFF.md#L421-L566) documents that consequence: preparation selected inputs, but later observation reread an expression cache; changing an equal-expression entry could change the computational input or presentation. A pending map converted to a point could also be mistaken for completed computation.

The current [structured observer](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L9901-L9975) already retains much more complete input data. It still orchestrates nested object/map observation through callbacks. A callback is not inherently defective. The problem is the unfinished transition between explicit selected plans and older recovery/completion paths.

**Causal conclusion:** adding captured plans beside the old evaluator increases the relationships that must stay synchronized until the old authority path is removed. The bounded explicit-machine trial in [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69) addresses this only if the migrated chain has one authoritative result location and its consumers use declared references to that result.

### 4. Genericity has been discovered through consumer failures instead of established at the interface

The September Sage readiness assessment passed several construction consumers but failed a module quotient and a narrowed fixed-endpoint map. The Lean branch repeats the structural pattern: success for a scalar result, literal endpoint, or simple record does not establish reuse through nonidentity transport, an opaque field, a dependent family, or a later universal operation.

The October 26 sequence is especially clear. Opaque record support was followed by complete inline-scalar validation, which exposed a distinction between actual supplied endpoint data and a canonical reference refinement. These are not merely more mathematical examples. They cross different combinations of the same generic representation mechanisms. Their coupling makes the repair cost recur.

**Causal conclusion:** the effective extension contract is still partly discovered by downstream work. The stable unit must be a complete compositional mechanism: selected input, action, full result, defining maps, and later reuse. Frozen independent extensions are the right test of that boundary. They supplement, rather than replace, the structural argument and permanent mathematical assertions.

For a pullback, obtaining an apex cardinality is weaker than retaining the computed apex and its projections, then using one of those actual projections in a later computation. Reconstructing a canonical pullback with equal cardinality does not establish that chain.

### 5. Semantic reading, audit export, and integration feedback are coupled

In current [`interpret`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L20460-L20493), semantic reading always proceeds through question fingerprinting and a complete trace snapshot before returning an executable typed question. Ordinary execution therefore pays for that export. The function also reads dependency provenance from the manifest during interpretation. The earlier journal records a manifest refresh during a running harness, illustrating the need for coherent execution inputs, separately from mathematical identity.

This is a code dependency, not an argument to weaken question permanence. The question must retain its fixed meaning; a full audit serialization need not be eagerly produced on every ordinary execution path. [#66](https://github.com/dzackgarza/lean-cas-dsl/issues/66) already owns this separation.

Feedback cost then amplifies representation churn. In the inspected October 28 job, the combined consumer build fails. Native tool building, question exports, connected workflows, and notebook execution are consequently skipped. The candidate is repeatedly stopped before its intended full behavioral evidence can be obtained.

**Causal conclusion:** frequent source checkpoints and isolated probes cannot substitute for a coherent path through the complete interpreter. Expensive rebuild dependencies and mandatory export enlarge the cost of each unresolved representation change. They are amplifiers of the architectural defect, not evidence that Lean itself is unsuitable.

### 6. Prose and checkpoints can preserve incompatible accounts of the active system

The [published-main handoff](https://github.com/dzackgarza/lean-cas-dsl/blob/6c424c4/HANDOFF.md) still directs work to `b0/poc-independent-role-integration` and lists the old K queue. The [current plan](https://github.com/dzackgarza/lean-cas-dsl/blob/362cb29f77525132519761046ae8ef14bb8bfa0b/specs/computational-core-plan.md#current-delivery-sequence-2026-10-28) identifies PR #67 and the active V1 branch. This is a concrete conflicting entrypoint, not a claim inferred from the amount of documentation.

The new producer rules also demonstrate the limit of behavioral policy. Telling each caller to retain its returned handle does not prevent another public function from recording incompatible metadata. A checked abstraction that makes this impossible is stronger than another instruction to call it correctly.

**Causal conclusion:** documentation can route work and explain invariants, but it cannot be the only enforcement of relations that are expressible in code. A history of corrections becomes expensive when the implementation still permits the corrected state. The current stronger conflict rejection is useful evidence that the code is starting to enforce a previously conventional distinction.

## What would break the cycle

The existing delivery requirements already name the appropriate direction. The following are architectural consequences of the evidence, not additional project requirements or implementation performed by this assessment.

| Boundary | Required change in responsibility | Evidence that would distinguish closure from another patch |
| --- | --- | --- |
| Mathematical declaration → selected application | Retain the complete selected structure and formal maps once; derive availability from the upstream registry | New generic mathematics reaches existing applicable objects without consumer forwarding |
| Selected application → computation | Preserve a distinct producer occurrence and its exact operand references | Equal formal expressions from distinct producers remain distinct through preparation and reuse |
| External data → internal result | Validate against the independently selected complete interface and preserve what the validation established | Changed endpoints or suppliers fail at entry; downstream projection does not reconstruct missing context |
| Pending computation → completed result | Give the selected computation one authoritative completion/result boundary | A point view cannot mark a pending map complete; repeated demand consumes the retained result |
| Structured result → later operation | Retain and project the actual defining data and maps | A computed construction's map is used in a subsequent real operation at its selected endpoints |
| Executable question → audit artifact | Preserve immutable meaning while making audit export a separate demand | Execution and complete export agree on the same question without execution requiring unused serialization |

The first useful demonstration is the already required structured-result/nonidentity-transport chain. It should consume a defining map from the same producer occurrence and remove that chain's competing recovery and completion paths. Lazy evaluation and adequate fused implementations remain valid: the selected realization determines which dependencies must execute. A fused call need not invent intermediate results or execution records.

The dependency lessons also survive. Mathlib owns the categorical mathematics. Lean's elaborator can handle appropriate selected dependent applications. CAP and the predecessor's retained construction algorithms can inform computational implementations. Adopting them is useful where it removes a demonstrated duplicate responsibility; merely adding another engine or wrapper does not solve producer identity or result retention.

## Assessment limits and decision

The recent work has not established that the formal separation is a dead end. It has established that a formal semantic layer can coexist with a dynamically assembled interpreter whose internal data relations remain porous. This is the main architectural continuity with the predecessors.

The current resolver's explicit coherence handling is a real difference from MRO precedence. Current rejection of producer collisions is a real improvement over overwriting them. Historical reported computations are useful evidence for the exact candidates that produced them. None establishes current integrated readiness after later source changes.

The latest inspected source still fails its combined consumer build. Full usable-V1 acceptance is not established by that run. Historical workspace loss and slow feedback explain some interruption, but they do not explain away the directly observed identity conflict or the repeated need to recover selected data.

The priority is therefore to finish the checked computation/result boundary already assigned in #69, together with the reading and export work in #66, and assess the complete system under #24. The decisive architectural test is whether an ordinary new consumer can use the declared result without knowing the producer's internal recovery rules. If it still needs another context repair, cache convention, or owner-specific bypass, the abstraction has not yet absorbed the maintenance burden it was created to remove.
