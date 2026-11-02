# Computational core: scope and work references

The [shared positive specification in #10](https://github.com/dzackgarza/lean-cas-dsl/issues/10#specification-and-fundamental-invariants) fixes the invariants from which its implementation tasks are derived. [The requirements record](computational-core.md#replacement-specification-and-fundamental-invariants) mirrors that contract. The 2026-11-02 audit supplies concrete source/API decisions and exact completion witnesses in the owning issues, including work after V1; this file does not establish another queue.


## Work tracking

Current instructions and decisions are in the issues. This file records scope and technical
references; it does not maintain a separate implementation queue or override issue
instructions. Update local descriptions when those decisions change.

| Issue | Responsibility |
| --- | --- |
| [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10) | Delivery roadmap and dependency order |
| [#85](https://github.com/dzackgarza/lean-cas-dsl/issues/85) | Replacement of the reconstruction-based interpretation pipeline |
| [#66](https://github.com/dzackgarza/lean-cas-dsl/issues/66) and [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69) | Coupled interpretation, execution and subsequent use |
| [#24](https://github.com/dzackgarza/lean-cas-dsl/issues/24) | Independent acceptance, fixed controls and extension trials |
| [#23](https://github.com/dzackgarza/lean-cas-dsl/issues/23) and [#82](https://github.com/dzackgarza/lean-cas-dsl/issues/82) | Required mathematical inputs and coherent data |
| [#83](https://github.com/dzackgarza/lean-cas-dsl/issues/83) | Development feedback loop |

The [architecture description](architecture.md), [CC requirements](computational-core.md)
and [reuse records](reuse/) document the decisions and their technical consequences.
[CONTRIBUTING.md](../CONTRIBUTING.md) contains the contribution policies.
Mathematical definitions and laws remain in
[lean-categories](https://github.com/dzackgarza/lean-categories/blob/main/FOUNDATIONS.md).

<a id="replacement-delivery-sequence-2026-11-02"></a>
<a id="current-delivery-sequence-2026-10-28"></a>
<a id="current-delivery-sequence-2026-10-29"></a>
<a id="immediate-next-work"></a>

The former local delivery sequence is replaced by the roadmap in **#10**, applying **#85**.
The scope descriptions below preserve mathematical obligations; historical implementation
choices, completion claims and work-selection procedures are not retained as instructions.

## B0: the extensible computational baseline (owner directive, 2026-10-01)

This section records the agreed scope for reference. Current task decisions and delivery
instructions are in [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10) and
[#24](https://github.com/dzackgarza/lean-cas-dsl/issues/24), with the original
[convergence requirements](owner/convergence-process.md) as provenance. An older local
description does not override those instructions.

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

<a id="kernel-mvp-proved-readiness-for-substantial-leaf-development"></a>

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


## Mathematical work and acceptance — KM1–KM9

These descriptions record the mathematical scope referenced by #66, #69 and #24.
Their current instructions govern implementation and assessment. Ordinary equations describe the ordinary
fragment; CC-HIGHER supplies the required coherent analogues for a promised higher
construction. Neither a well-formed representation nor a finite execution test supplies
a formal law or proves an arbitrary backend correct.

| Work | Mathematical deliverable and acceptance |
| --- | --- |
| **KM1 — One compatible interpretation of the accepted mathematics** | Interpret the accepted categories, dependent families, operations, comparisons, admission hypotheses and universal constructions together. In particular, binder meanings and complete creation-lift data must coexist without changing the selected questions. **Supporting build order:** first compile and execute the real dependency closure of the selected construction while replacing its defective paths; a green legacy whole-system build is not an entrance condition. At completion, one kernel, contract, mathematical input, probe/tool and runtime combination builds. Preserve the applicable #63/#64/#67 behavior through the replacement; disabling a gate or merely combining source does not establish KM2–KM9. |
| **KM2 — Declared constructions determine the meaning** | Terminal objects and generalized points, quotient and power-object constructions, literal domains, diagrams and observation relations are those of the applicable accepted declarations. For a chosen `U:C→Set`, an element of `U(X)` is a map `1_Set→U(X)`; it need not be a global point `1_C→X`. A declared presentation by `S→X` retains `S` and the accepted relation to the element being represented. Independent readings agree for the existing second presentations/structures and distinguish genuinely different choices. Reordering declarations cannot select a construction. Missing input and unresolved ambiguity stay explicit; a syntax spelling may select its declared operation. |
| **KM3 — Complete dependent application and admission** | An application retains every dependent parameter and its actual domain hypotheses; substitution yields the declared source and target. The fixed questions include destructured `((a,b),(c,d)) ↦ …`, several bound variables, selected `Vec(ℤ,2)` and its base ring, closed maps/points, dependent families and admitted binders. Interpret all K2–K8/K14 reading portions and the entire admitted inventory with their independently fixed meanings and protected negatives. An out-of-domain expression, an ambiguous interpretation and a valid question with no computation are distinct. A false well-typed assertion remains a valid question. No production backend is needed to establish its meaning. |
| **KM4 — Functorial propagation and coherent comparisons** | For selected `F : C → D`, use `F(X)` and `F(f) : F(X) → F(Y)` with the declared identity/composition laws. An operation on `D` is inherited at that image only on its declared domain; invariants defined on `Core(D)` are inherited along `Core(F):Core(C)→Core(D)`. A selected `α : F ⇒ G` acts by its actual components and naturality; equivalence of interpretations uses the comparison and compatibility actually supplied, not arbitrary noninvertible transformations. Consume constructor-induced comparison actions, proof-only refinements and specified reindexing. Establish K10's ring diamond and formed-module kernel comparison, K11's complete resolution, K12's constructor action, `Fin 2 × ℤ/3` refinement, and two structures on one carrier. New objects/operations acquire exactly the applicable composites without editing old objects/leaves. Existing route-completeness and refinement implementations may be reused after their required responsibility and fit are established. |
| **KM5 — Morphisms, generalized points and change of presentation** | Composition and application use the selected arrows with their full endpoints. If `x : S → X`, its functorial image is `F(x) : F(S) → F(X)`; comparison of views `α_X : F(X) → G(X)` acts on `y : S → F(X)` by `α_X ∘ y` with domain `S`. No domain is replaced by a singleton or chosen by carrier equality. The fixed nonidentity `𝔽₉` translation and successive computations use the actual supplied maps and points. Accepted symbolic/opaque arrows are not required to admit finite graph enumerations. **Supporting checks:** exact computational endpoints, ownership/session compatibility and missing/wrong comparisons remain validated. |
| **KM6 — Complete universal data and subsequent constructions** | For `D : J → C`, the requested construction includes its chosen cone/cocone, all required legs and universal factorization. For a kernel in its accepted pointed/module context, retain the selected `i : K → X`, `f ∘ i = 0` and factorization; a class of isomorphic subobjects does not alone select its representative map. A result returned through `U : C → D` requires the prescribed lift/creation data and comparison, not automatic inheritance from `U`. Compute and subsequently use the declared lift of the module kernel with restricted form and inclusion (without inferring a categorical kernel in a category of form-preserving maps), the finite-set creation-lift pullback, a second registered shape/route and successive lifts. A lifted cone is universal upstairs only under the accepted creation/lifting hypothesis; otherwise retain exactly the structured construction and universal property actually supplied. Actual supplied computational data remains distinct from the accepted formal construction and its proof. Missing/wrong components are detected; a bare apex, copied downstairs result or unevaluated formal plan is insufficient. Existing prescribed-lift computations are reusable only where they preserve this complete boundary. |
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

### Single exit condition

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

## Fixed B0 diagnostic inventory

[#24](https://github.com/dzackgarza/lean-cas-dsl/issues/24) tracks the actual acceptance
inventory. The original K1–K14 identifiers below preserve concrete required observations
and diagnostic provenance. They do not select current work. Dated admission, blocked-input
and implementation status is historical; inspect current inputs and the admitted inventory
rather than treating an old reported defect as a present result.

| Item | IDs (from the `5410e70` report) | Closes when |
| --- | --- | --- |
| K1 required computations | `sets.card.z4_cubed`, `sets.card.z7`, `sets.card.z5_empty_power`, `sets.card.fin2_times_z3`, `sets.card.integers`, `sets.finite.integers`, `sets.finite.fin2_times_z3`, `sets.implemented.card_fin`, `sets.card.fin2_sqcup_fin3`, `sets.eq.rev_rev`, `sets.limit.pullback.card`, `finite_sets.limit.pullback.card`, `lattices.discriminant.a1`, `lattices.discriminant.a2`, `lattices.discriminant.a3` | every ID holds with at least one dispatch |
| K2 invalid inverse readings | `inverses.value`, `inverses.solve`, `inverses.left`, `inverses.right`, `inverses.det` and the `(statement)` entry of `inverses.cas` | no ID is invalid. Their earlier questions are empty, so every reading is a question change requiring independent assessment. Upstream row: `core-admission-realized` |
| K3 required positives | the assertions of `tests/acceptance/b0-required-positives.cas.proposed` | every assertion holds through registered execution, run unchanged, with its protected negatives. None is admitted yet: once all hold, K3 is `blocked: admission operation (owner)` until admitted |
| K4 membership and containment judgments | `algebras.polynomials_several`, `algebras.polynomials`, `schemes.affine_line`, `schemes.affine_space`, `calculus.taylor_exp`, `calculus.taylor_sin`, `composed.root_one`, `differentials.member`, `ellipses.even_square`, `ellipses.odd_square`, `ellipses.prime`, `ellipses.not_prime`, `factorization.approximation`, `finite_sets.member`, `finite_sets.not_member`, `finite_sets.subset_union`, `finite_sets.intersection_subset`, `comprehension.typed`, `comprehension.image_typed`, `comprehension.even_member`, `comprehension.odd_not_member`, `fractions.member`, `fractions.sqrt_member`, `subspaces.member`, `subspaces.not_member`, `numbers.containments`, `numbers.containments.transitive`, `numbers.membership.zmod`, `numbers.membership.negative`, `polynomials.variable`, `polynomials.member`, `polynomials.irrational_roots`, `several_variables.variable`, `several_variables.last_variable` | every ID is not a request-formation gap in the computation-only report, or holds in the full report through Lean discharge. Expect question changes requiring independent assessment |
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

The K1–K14 table is retained as the concrete B0 assertion/diagnostic
inventory; checking its rows does not by itself prove readiness. Kernel MVP
requires KM1–KM9, **including** independent frozen-kernel trials and question
preservation, *before* mass K13 leaf work. Full B0 still requires all real
computations and protected negatives.

## Acceptance table

These are the mathematical observations and compositional arguments for the existing row
identifiers. They remain subject to the full fixed inventory and independent evidence model.
The issues specify current work and acceptance; these rows explain the referenced
scope and do not assign another queue. Necessary engineering observations are listed separately.

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
| `b0-authority` | Preserve the established author/input boundaries and independently protected acceptance transitions documented in [architecture.md](architecture.md). Assignments and status belong in #10 and its work issues; this is not a mathematical object or a new prerequisite for unrelated construction. |


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

## Exit trials

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

<a id="kernel-construction-procedure-owner-instruction-2026-10-21"></a>
<a id="running-checks"></a>

## Construction and verification

[#83](https://github.com/dzackgarza/lean-cas-dsl/issues/83) contains the development-feedback
instructions. [CONTRIBUTING.md, Gate](../CONTRIBUTING.md#gate) documents commands, dependency
refresh behavior and the evidence each command provides. Compiler diagnostics, fresh
artifacts, production execution and independent acceptance establish different properties.
The work issues specify the required original questions, contexts, controls and budgets;
this reference introduces no additional environment or verification prerequisite.

## Historical records

The [earlier main plan](https://github.com/dzackgarza/lean-cas-dsl/blob/0cee529c343fbe1c5f7a5f1326d4b805cc8fed44/specs/computational-core-plan.md)
and [PR #67 planning and execution history](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/specs/computational-core-plan.md)
remain available at their exact revisions. They preserve source findings, old DAG/node
records and dated observations. Current instructions are in the linked issues; the
historical records do not create another work queue or establish present acceptance.
