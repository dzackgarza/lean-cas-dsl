# Research decisions: selected data and independently implementable category interfaces

**Feature:** `001-categorical-research-language` · **2026-11-07**. This is the current research/decision entry for the [clarified specification](spec.md), [consolidated plan](plan.md) and [mathematical-input contract](contracts/mathematical-input.md). It supersedes the later G1 proposals as normative selection instructions. The original [independent architectural alternatives/reuse ledger](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6664331639) and [adversarial discussions](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6664324222) remain historical evidence, not independent approval of this revision.

## 2026-11-25 — Acceptance of kernel work, and the order of computational work

**Decision** (owner instructions of 2026-11-25; constitution v4.0.0; spec clarifications of that date). Kernel work is accepted on kernel behaviour, with a protocol peer or an empty manifest. A computed mathematical result is leaf work and needs an implementation of every category on the selected structural route. Computational work has version milestones of its own, after kernel readiness, in the order of the structural scaffolding of the categories.

**Rationale.** `2 * 3 = 6 in ℤ`: ℤ is a ring, and its multiplication comes from a monoid structure of that ring. A kernel check that obtains 6 without the category implementations from sets up to rings bypasses the structure that the product exists to supply. The released contract is published by T028, completed by T100 and T101, and released at F, so an implementation written earlier is written against an unfinished contract.

**Alternatives considered.**

| Alternative | Assessment |
| --- | --- |
| Kernel tasks close on computed results from the existing flat registrations. | Rejected. Those registrations are not category implementations; the result does not come through the structural route. |
| Order the computational work by ease of expression or by what a kernel check needs. | Rejected by the owner. The order is mathematical. |
| A first vertical computational milestone before kernel readiness. | Rejected. The contract is not published until T028, and later tasks still add leaf-facing data (T100). |

**Order.** The [plan](plan.md#computational-milestones) lists the milestones in order; the entry "The list of computational milestones" below gives the rules that produce the list.

## 2026-11-25 — The notebook after the category implementations

**Decision** (owner instruction of 2026-11-25; spec clarification of that date). Kernel readiness F is the kernel with DSL scripts through the public session; it needs no notebook. The notebook (US7, US8) is one functional unit after the category implementations of M4 and before the functional work of M5 and all evidence-only work. Installation (#34) stays in M5.

**Rationale.** The owner's judgment is that the kernel is the hard part. The notebook tasks need the worker of lean-jupyter-kernel on the toolchain of the research image (its T004), and the kernel moves to that toolchain only at T352; with the unit after T352 and T105, the worker and its consumers change toolchain together. M5 consumes the unit: the client of #68 runs over the worker.

**Alternatives considered.**

| Alternative | Assessment |
| --- | --- |
| Keep the notebook in F. | Rejected by the owner. It also orders consumers on Lean 4.33.0 before the worker tasks that move to the research-image toolchain. |
| The notebook directly after F, before the category implementations. | Rejected by the owner: the notebook is at the end of the functional order. |
| The notebook after M5. | Rejected. The client, unit-group and diagnostics tasks of M5 use the worker. |

## 2026-11-25 — The list of computational milestones

**Decision 1** (constitution C23; FR-042). The milestone list covers all 100 registered categories of lean-categories `443fba9` and the categories that T131 and T133 add. A category with no structural chain to `cat.sets` (51 categories) is implemented after the categories that its formal definition is built from, and after the upstream task that adds a missing structural functor. An atom with no input (`cat.cardinals`, `cat.cardinalities`, `cat.ordinals`, `cat.walking_pair`) is a root.

**Rationale.** A built category's objects and maps are made of objects and maps of its inputs, so its public constructors consume theirs; this is the dependency that a structural functor expresses (C23, functor actions construct their targets).

| Alternative | Assessment |
| --- | --- |
| Leave the 51 categories without a place until a milestone needs them. | Rejected. The task is the full roadmap; a category with no place has no task. |
| Order them by their inferred layer only. | Rejected. The inferred layer ignores the structural functors that the upstream tasks add, and it gives no order for atoms. |

**Decision 2** (C6, FR-016, FR-022). A written ℤ or ℚ in a ring operation has one reading: the commutative ring ℤ forgets to the ring ℤ by `Iso.refl` (lean-categories `Catalogue/Semantics/Algebra/NamedCommutativeRings.lean:33-35`), so the operation families agree definitionally. The milestone list uses the ring rows of the recorded readings.

| Alternative | Assessment |
| --- | --- |
| The readings of the kernel report of 2026-11-22 (ℤ a commutative ring, ℚ a field). | Rejected. That reader forms one object candidate of a name; C6 forms every candidate and identifies definitionally equal families. It would add `cat.commutative_rings`, `cat.fields` or `cat.algebras` to the routes of 46 statements with no mathematical cause. |

**Decision 3** (owner instruction of 2026-11-25; #24, #19, plan "Computational milestones"). The unit of computational work is one version of one category implementation: each category implementation is a Spec Kit feature of lean-cas-dsl-leaves with the milestones V1 (every spike computation and every statement that kernel V1 requires computed), V2 (the remaining full-B0 statements of #19) and V3 (the classified Sage coverage of #20, #21 and #23). The task list holds one task for each category version, in structural order, V1 of every needed category before any V2. A statement belongs to the category that owns its rows, at its version (plan, "Statements"; `research/category-scope.md`). The V2 and V3 tasks come after T105 and before the assessments of Part 2 (C21; #19 does not wait for V1 acceptance). The V3 tasks are written when the classification records their statements.

| Alternative | Assessment |
| --- | --- |
| One task for each group of categories (the earlier milestones T200 to T224). | Rejected by the owner. Each category implementation has its own specification and versions, and the leaves specs cite one task for each version. |
| Close each V1 task on all statements of its category. | Rejected. #24 makes complete readings, not every full-B0 computation, a V1 requirement. |
| Write the V3 tasks now. | Rejected. No classified statement exists before T141 and T143; a task with no statement has no check. |

**Decision 4** (engine survey; C17). The milestones use the container Sage 11.0.beta5 (source build), GAP 4.16.1 through Sage `libgap`, SymPy 1.14.0, PARI 2.17.4, Singular 4.4.1, and through juliacall Catlab.jl 0.17.7 (pullbacks of finite sets) and Oscar 1.8.2 or Hecke 0.39.22 (modules over polynomial rings, forms over number fields). A cardinal is finite (Sage `cardinality()`) or $\aleph_0$ (a set that Sage puts in `EnumeratedSets` with infinite cardinality).

| Alternative | Assessment |
| --- | --- |
| passagemath 10.8.14 in a separate environment. | Rejected. The research container is the reproducible environment and holds Sage; one environment cannot hold both `sage` packages. |
| CAP (GAP) for pullbacks. | Not chosen. Its limits are recalled in the survey, not read; Catlab's finite-set limits are read. |

**Cardinals.** No engine computes $\aleph_0 \cdot \aleph_0$. The cardinal implementation computes the arithmetic of finite cardinals and $\aleph_0$ with a cited reference, for the three V2 statements that need it (constitution 4.0.1, policy "Established computational implementations").

## 2026-11-25 — Logs and timing records are current work; attainments; a leaf that asks the kernel

**Decision 1** (owner answer of 2026-11-25; FR-043, SC-016). The timing record of each test and each computation, the durable log of each test run and the application log of the kernel session are current work. T112 and T127 are the first unchecked tasks.

**Rationale.** Constitution C24 states these as present obligations. C21 puts final performance and self-consistency evidence after functionality; these records are neither. They are part of the feedback capability that C21 puts first.

| Alternative | Assessment |
| --- | --- |
| Keep T112 after F. | Rejected by the owner. It needs an amendment of C24, and every Part 1 run stays without the required records. |
| Records now, application logs at M5 with #8. | Rejected by the owner. #8 concerns diagnostics shown to the user, which stay opt-in; the application log is written always. |

**Decision 2** (owner answer of 2026-11-25; FR-042). The stated result of a computational milestone is not an owner choice. It is the set of statements of the original workloads whose selected route stays within the categories implemented through that milestone, and it covers what the later milestones consume. The [task list](tasks.md#complete-the-required-computational-implementations-and-actual-delivery-tuple) lists each category version, and [`research/category-scope.md`](research/category-scope.md) gives its statements.

**Decision 3** (constitution C22; runtime contract, section 6). When a suspended leaf asks for an operation that no leaf implements, its resume holds the no-implementation outcome for that child, and the leaf continues. C22 says that the kernel returns that outcome to the requesting leaf; a rule that retires the chain keeps the outcome from the leaf. Other child failures retire the chain as before.

## 2026-11-25 — Carrier of occurrences and selections

**Requirement.** Constitution C23: each selected source binding and each returned occurrence keep their exact association through preparation, projections, substitution and later calls. C18: a representation whose consumers repeatedly lack the information that it was to retain is reconsidered before more machinery is built around it.

**Source finding** (kernel branch at `dd491b4`, every non-test file of `CasCompiler/` and `CasRuntime/` by search; the task list gives the locations). The reader holds its selections as typed data. The session passes only the term to the kernel, and `lowerTerm` receives an `Expr`. Selections and runtime occurrences therefore travel inside the term: 73 `Expr.mdata` key names, with whole terms held in `Function.const` envelopes, written in 61 files and read in 59. A typed `ValueBinding` is written back into a term before each re-lowering.

**Why the premise fails.** Lean treats `Expr.mdata` as transparent. `whnf` removes it (Lean 4.33.0, `Lean/Meta/WHNF.lean:396`, `whnfEasyCases`), beta reduction removes it unless `preserveMData` is set (`Lean/Expr.lean:1592`), and unification assigns terms without it. The kernel source states this at six places and holds 24 substitutions with `preserveMData := true`, a hand-written head normalizer and an ordering of the lowerer whose purpose is to read each mark before a reduction. Each such site is one repair. The kernel has 179 `whnf` call sites and 391 `isDefEq` call sites, so the set of sites is not bounded by a list.

**Measured consequence, 2026-11-23 to 2026-11-25.** 522 `just loop` runs, 428 failed. The most frequent runtime messages were "the runtime argument does not retain its specified source value" and "the runtime value has a different marked source type dependency". The non-test kernel source grew from 15,239 to 30,277 lines, its metadata sites from 39 to 152 and its `isDefEq` lines from 204 to 375. No task closed.

**Alternatives.**

| Alternative | Assessment |
| --- | --- |
| A. Keep the term metadata and repair each loss site. | The measured course. The set of loss sites is every term operation on a marked term. |
| B. Typed data beside the term, keyed by binding identity. An occurrence is a binder of the context (`BindingId`); a selection is a typed record that the reader passes to the lowerer and the runtime. | Chosen. A variable is opaque to reduction and unification, and two binders with equal types and values stay distinct. `ContextTelescope`, `BindingId` and `bound : HashMap BindingId ValueBinding` exist and already carry the named source bindings. Prior art: A-normal form names every intermediate value (Flanagan, Sabry, Duba, Felleisen, "The Essence of Compiling with Continuations", PLDI 1993); Lean's own compiler does so in LCNF, where each `LetDecl` has an `FVarId` (`Lean/Compiler/LCNF/Basic.lean:350`). |
| C. Keep the term as carrier and replace metadata by opaque wrapper constants. | Rejected. An opaque wrapper is not definitionally equal to its value, so dependent types that mention a marked value stop checking; unification still builds terms without it. |
| D. A source representation of its own in place of Lean terms. | Rejected. It discards the reader, the layouts and the checked families that work, and is a third rewrite. |

**Decision** (owner instruction of 2026-11-25 to decide the carrier before more repair; internal representation is a delegated engineering choice under C17). Alternative B. T116 moves occurrences; each task that changes a selected family moves that family's selection (rule "Typed selections" of the task list); checkpoint M1.1 closes on T116, T032 and T048. The decision is a hypothesis under C18: if a consumer cannot be served by typed data keyed by binding identity, record the case here and reopen it.

## 2026-11-22 — Operational category independence and continuing feedback

**Decision.** Retain independently categorical mathematics, generic forward realization and
computational-only leaves. Make their software consequence explicit: a category implementation
receives a generated public interface, constructs complete objects and arrows, and reaches
unchanged applicable consumers through its actual dependencies. Extend the existing API exporter
and ports; do not invent another registry or representation translator. Distinguish semantic
relationships, public computational dependencies and physical build/runtime dependencies.
Necessary shared code and engines remain permitted under C22.

The two comparative reports are inputs to this analysis, not implementation evidence or
authority to alter the mathematics. The relevant primary sources were inspected on 2026-11-22:

| Source | Observation and resulting decision |
| --- | --- |
| [Sagebrush PR #1529](https://github.com/sagemathinc/sagebrush/pull/1529) | Open PR. Its author records MATLAB comparisons, behavioral corrections and lazy loading after a bundle-size failure. Adopt the concrete changed-capability/public-consumer feedback pattern; this does not establish comparative agent productivity or integrated correctness. |
| [PassageMath PR #3075](https://github.com/passagemath/passagemath/pull/3075) | Moves optional `bz2` imports to their use sites; reports unaffected imports and computations in a Python installation without that extension. Require actual dependency locality, including operation with unrelated optional engines absent. |
| [PassageMath PR #3069](https://github.com/passagemath/passagemath/pull/3069/files) | The patch both changes one objective to obtain a unique optimum and replaces incidental solver outputs with relational checks. Adopt relation-based assessment of permitted choices. C9 forbids changing a protected original question to obtain uniqueness or agreement. |
| [Sagebrush issue #1567](https://github.com/sagemathinc/sagebrush/issues/1567) | Open reported extended-gcd counterexample: the gcd is correct while returned cofactors fail the prescribed identity. Not independently reproduced here. Require the full result relation, including maps/dependent fields and continuation; neither a scalar projection nor provider agreement supplies it. |
| [Declared computational API](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/main/api/README.md) | Existing generated categories, objects, constructions, functors, signatures and addresses are the implementation starting point. The kernel reads the independent registry. Category-filtering an aggregate export does not establish a smaller Lean import/build closure. |

The reports' `SourceLimit.limitApex?` diagnosis is stale for the inspected local kernel revision
`5c3231979edb53e994419fcf090291b950e8bd30`: the helper was removed in
`4c6be22` and the selected row/cone is retained. The remaining source-to-result obligations
must be checked at their current owners, including selected leg use and the unsupported
`returnsToSource` path; deleting an old symbol is not the acceptance condition. The maintained
task bodies preserve this distinction.

The [architecture](../architecture.md#category-interfaces-computational-dependencies-and-build-boundaries)
states constructor/operation conformance and the conditional composition argument. Categorical
composition establishes the stated composite relationship only under the independently fixed
primitive interpretation hypotheses; it does not prove external algorithms correct. Permitted
different outputs retain their actual selected maps and uses. Fixed selected inputs, exactness,
normalizations and ordering remain binding.

**Scheduling and constitutional consequence.** Constitution v3.1.0 elaborates C0/C9/C21/C23/C24
under the owner's explicit request. T114 establishes current fast feedback immediately and
maintains it; T028 publishes the generated category interface; T061 completes generic actions
and later use; the category tasks deliver actual category implementations and their focused build/public
consumer boundaries after F. T105 publishes the compatible tuple on the image port of T352 (#90).
Independent extension/substitution assessment and final mathematical budgets retain their
existing later owners. These are requirements to implement, not claims that the current system
already satisfies them.

## 2026-11-22 — Runtime boundary and compatible release

The further report correctly distinguishes mathematical interfaces, build/package boundaries
and runtime transport. [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
already provides packages, libraries, executables and selective incremental builds. Those
facilities do not prove this project's actual import graph is narrow. The
[Lean module reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
also requires accounting for executable metaprogram dependencies rather than hiding imports.

Retain the existing process-v2 design and native build tools. Category interfaces, packages,
processes and ports need not be one-to-one. A provider-only source change under the same accepted
interface/contract rebuilds its actual implementation closure, without changing or rebuilding
the generic kernel or mathematical environment. New independently accepted formal modules may
require imports and affected rebuilds; they must not require a new kernel case or accommodation
in prior applicable leaves. C23/C24 now state that distinction.

The concrete release concern is verified at these sources, without claiming a runtime test:

| Inspected component | Source-level observation |
| --- | --- |
| [Kernel manifest at b1f5ab6d](https://github.com/dzackgarza/lean-cas-dsl/blob/b1f5ab6d5c7a0bd68aabef7e9a781d7722894e90/lake-manifest.json), also local kernel `5c3231979edb53e994419fcf090291b950e8bd30` | Both pin contract `dcb9a15f7caef4157348c02af877029251df3585`. |
| [Pinned cas_port.py](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/dcb9a15f7caef4157348c02af877029251df3585/python/cas_port.py) and [kernel connection](https://github.com/dzackgarza/lean-cas-dsl/blob/b1f5ab6d5c7a0bd68aabef7e9a781d7722894e90/CasRuntime/Connection.lean) | `serve(backend, backend_version, ops)` takes three arguments and delegates to the v2 session; the kernel invokes `negotiateV2`. |
| [Published Sage adapter](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/8b181d7bd23796ddb37a8e7abb1053001c3c012f/backends/sage_modules.py) | Calls `serve` with four positional arguments, including adapter version. That unchanged call does not match the pinned SDK. |
| [Contract main at ef3771dd](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/ef3771ddf94a1fcf4d694ae577abb6069b0258e5/python/cas_port.py) | Retains the old four-argument entrypoint and defaults to protocol 1. Substituting it does not establish the kernel's v2 contract. |

Importing `cas_port` alone therefore does not identify a protocol version, contrary to the
report's inference. The actual signature and negotiation requirements determine compatibility.
T017–T028 repair the exact current contract consumers; the category tasks migrate retained leaves after F;
T105 publishes and exercises the coherent tuple. Do not revive retired T024/T025, add a
compatibility intermediary, or make complete publication a prerequisite to every runnable
functional task.

The generated category surface must be directly usable through the existing supported SDK,
rather than a filtered global catalogue that authors interpret manually. Preserve exact
dependent descriptors, selected endpoints, choices, captures and existing wire encodings.
Host-language signatures are faithful projections, not a new semantic authority or mathematical
proof. Supporting new languages is not an extra V1 workload.

A mandatory Rust layer, a Rust-plus-other-language demonstration and standalone Lean leaves are
not adopted. The last proposal would change the expressly retained no-new-Lean-leaf policy.
Call/startup/transfer overhead uses existing diagnostics when needed and final performance work
after functionality; it is not an additional M0 benchmark programme.

The earlier selected-data decision below remains applicable.

## The requirement, before choosing an algorithm

The owner has already specified the governing behavior. The mathematical authority supplies categories, operations, actual comparison cells and coherent choices, their laws and abstract computational interfaces. The kernel consumes and propagates that structure. A leaf may supply prescribed computational data for a permitted choice, but never define/formalize its own choice family, validity criterion or laws. An absent required choice/cell causes its prescribed error before dependent use. Several permitted choices need not be equal or canonical; actual chosen components and their later action remain selected data.

Three different questions must not be merged:

1. Is this supplied selected route/cell well-formed at the required boundary, with its required data?
2. Does this independent operation permit a choice, and has its prescribed supplier supplied the actual candidate data needed for its continuation?
3. Do these inherited operation bindings agree under the independently accepted whole-operation agreement rule?

The previous general “exact routes → fair evidence search → universal cover → selection” proposal silently made question 3 a prerequisite of all instances of 1 and 2. It also made a missing-data/ambiguity diagnostic require a stronger theorem that no comparison could exist. Neither strengthening follows from the source requirements.

## Source investigation and actual reuse decision

| Source inspected | Exact result relevant to this decision | Use |
|---|---|---|
| `lean-categories/LeanCategories/Catalogue/Registry/operation-agreement.md`, original `fc6d3d6961223c75290c93da540c87f17a926cc7` and current `6c7f6a8f026500da30c00736580c5bd30c87331b` | Same blob `4ac250f567c8fe132a26dfae3b3b2516b2013040`. Rigid full dependent family, actual transports, checked reflexivity without a special registry row, existing accepted nondefinitional comparison; absence leaves surviving bindings ambiguous. No new search over unregistered theorems/carrier isomorphisms. | Adopt this actual source rule, not a downstream approximation to it. [Source](https://github.com/dzackgarza/lean-categories/blob/6c7f6a8f026500da30c00736580c5bd30c87331b/LeanCategories/Catalogue/Registry/operation-agreement.md). |
| Current `Registry/Entry.lean`, blob `91dcc98706087fc13d6171beb5d014dfc0f7574b` | Constructor functorial/comparison/identity/composition actions are actual declarations. Structural forgetting/inclusion differs from parameter-changing construction. Selected presentation comparisons retain full signatures; licensed evaluation cannot supply a different comparison or criterion. | Consume those exact roles and terms. Do not infer a missing action from a label or Boolean structural flag. [Source](https://github.com/dzackgarza/lean-categories/blob/6c7f6a8f026500da30c00736580c5bd30c87331b/LeanCategories/Catalogue/Registry/Entry.lean). |
| Constitution v1.2.1 C1–C8 and independent-authorship sections | Independently formalized mathematics; proof-free leaves; actual chosen data; computational failure does not redefine meaning; allowed choices need not coincide; actual authors/input separation. | Correct subordinate specification/design/tasks without constitutional amendment. [Source](https://github.com/dzackgarza/lean-cas-dsl/blob/0db96de6cc73f02d5cefbe0eeba8183f60b7f67f/.specify/memory/constitution.md). |
| Recorded owner intent, September 29 | Formalization, deterministic kernel consequences, independent acceptance and computational leaves have separate authors/inputs/authority. Moving definitions between repositories does not create that separation. | Requirement provenance, not a source of new downstream mathematical definitions. [Source](https://github.com/dzackgarza/lean-cas-dsl/blob/df43c82e939d3b5a54c9b1126abcaa2927c62e3f/specs/owner/intent-discussion.md). |
| Existing whole-family computation and lift interfaces | Exact target/prerequisites/plan equality are computation-composition inputs; selected lifts/factors have actual fields/maps/comparisons and independent equations. | Keep generic operational interpretation and complete returned-data behavior. A computational plan equality is not a missing route/cell. [Computation](https://github.com/dzackgarza/lean-categories/blob/fc6d3d6961223c75290c93da540c87f17a926cc7/LeanCategories/Catalogue/Registry/Computation.lean), [lift](https://github.com/dzackgarza/lean-categories/blob/fc6d3d6961223c75290c93da540c87f17a926cc7/LeanCategories/Catalogue/Lift.lean). |
| Downstream route/search/coverage records and model files | Exact route representation, candidate proof scheduling and a conditional cover checker answer different engineering questions. Their tests do not establish that their input judgment is the intended source judgment. | Retain historical code/arguments; reuse only a component whose actual responsibility is needed and justified. Do not import them as the normative semantic gateway. |

The retrievals were exact source-path/commit inspections and comparison of the source rule with the downstream definitions. No new subject theorem, formalization-corpus result or implementation acceptance is claimed. This correction adds no application definition or proof needing an invented research gap. Existing runtime library reuse remains in the original source ledger.

## Alternatives considered

**Preferred route by shortest path, installed order or backend success:** rejected. It lets operational convenience choose mathematics, misses actual cell data and changes behavior when providers change.

**Leaf defines/formalizes its comparison contract and implements it:** rejected. It collapses the epistemic and computational authorities. Moving its definition into lean-categories is not independent authorship. A leaf supplying an already prescribed candidate choice datum is different and remains allowed.

**Universal semantic quotient / complete proof cover for every use:** rejected as the general architecture. It strengthens the problem, can demand irrelevant equality/uniqueness for a selected or choice-bearing construction, and misinterprets missing supplied data as an undecidability problem. A uniform source comparison is still required wherever the actual source contract asks for one; this rejection does not waive that obligation.

**Exact source interpretation with mandatory actual data:** adopted. Preserve the complete selected context, source-required cell/choice inputs and laws, licensed agreement check, and exact error boundary. Derive source structure generically; retain actual returned candidate choices and their dependent maps. This neither limits the original extension class to successful examples nor permits an unresolved positive to pass.

## Concrete consequences, not a deferred architecture question

The current math contract §4 gives the three judgments, processing order, required-slot data and outcome table. Current T007/T021 prepare and enforce actual mandatory computational data; T053–T056 implement the source-faithful closure/selection/error gate and its native first-use argument; T063 retains original comparison controls; T073–T076 preserve growth; T028/T079/T080/the category tasks/T109 prohibit the combined mathematical-authority/leaf assignment in actual handoffs. The plan, model and task bodies were edited in place. These responsibilities are not left for an implementer to ask the owner to decide again.

No new wire-level `preferredRoute` field, no new choice operation, no new leaf proof reply, no change to expected mathematical questions, and no new acceptance inventory are selected here. Existing prescribed public fields and exact source roles determine the actual computational boundary. Native implementation still owes its complete positive and negative outcomes, original budgets, independent trials and review.

## Status of earlier records

The [universal-classification counterexample](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6693321613) concerns its stated stronger premise; it is not evidence that the intended selected-data contract is impossible or that the specimen was independently admitted. The [route construction](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6693871042) remains a structural-language reference at its actual signature. The [fair discovery](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6697729346) and [universal coverage](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6705288299) records are **superseded as general selection/negative-judgment contracts**. Their conditional engineering claims/tests are not silently promoted into source requirements.

The previous clean planning-audit reports do not approve the corrected architecture. The current audit must trace the owner clarification through exact requirements, source rules, design entities, actual errors, task owners and preserved observations—not merely count FR associations or passing reference tests.
