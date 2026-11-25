# Validation entrypoint — fast feedback, complete functionality and original acceptance

**Feature:** `001-categorical-research-language` · **Updated:** 2026-11-25 (Asia/Taipei).

Use the [requirements](spec.md), the [plan](plan.md), the [task list](tasks.md), the [mathematical-input contract](contracts/mathematical-input.md) and the [runtime contract](contracts/computational-runtime.md). The [permanent constitution](https://github.com/dzackgarza/lean-cas-dsl/blob/main/.specify/memory/constitution.md) and the [owner's current handoff](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6726232237) govern. This guide states how to validate a change and which inputs the final assessments keep fixed. Observed outcomes and acceptance records remain in the owning issues; this guide records no run.

## Current development feedback comes first

T114/#84 uses the commands in the kernel implementation worktree; locate that checkout with
`git worktree list` and inspect its actual `justfile` and dependency tuple. Documentation on
`main` does not establish that implementation commands are present there. The
[feedback command reference](../../CONTRIBUTING.md#feedback-loops) gives the full usage.

A named local module is checked by building its `+Module:deps` and freshly executing its source
with `lake lean`. An explicit `+Module:facet` builds artifacts and requires an acceptance
consumer in the same invocation:

```sh
just loop "CasRuntime.SessionTests"
just loop "+CasCatalogue.TestSuite:leanArts" ellipses
```

The second command runs the complete unchanged file, including its definitions and later uses.
Acceptance commands default to the empty-provider diagnostic; insert `--manifest PATH` before
the file stems to use the actual provider manifest. A gap does not establish the selected
assertion. A protocol peer establishes only the public execution and protocol behavior it exercises.

The 300-second bound, the long-run commands, the run records and the freshness rules are in the
feedback reference.

A fast failing mathematical check establishes feedback, not the missing function. T016 retains
its historical completion; T114 establishes the current loop and maintains it during later work.
T028 and the category tasks add category-local public-interface/build checks when those implementations exist.
T105/#90 remains the later delivery port unless an actual unavailable environment blocks the
active task. See the [completion milestones](plan.md#completion-milestones).

## Functional observations must exercise the missing production capability

The actual path is public source → selected checked context → production lowerer → OperationalProgram → concrete executor → selected live provider invocation → complete admitted result → subsequent public source use. A test that constructs the prepared request/program itself or supplies its own executor can test a component but cannot establish the missing production connection. A v2 handshake or a standalone helper result establishes neither kernel readiness nor mathematical execution. A protocol peer at the provider position of this complete path establishes the kernel behaviour that it exercises (SC-014); it establishes no computed mathematical result.

Implement the lowerer and concrete executor against the shared signature at their recorded task positions, connect the public entrance and actual returned-data continuation, then finish every required generic mechanism and truthful protocol/notebook/interface behavior. This is not an instruction to stop at a first scalar, first RX-LIFT or easier demonstration. The original driver T041 can be adapted before its target is complete; T039's proof, T079's trial and a full exported inventory are not prerequisites to that functional work. All actual source/domain/selection/data/owner checks needed to perform an operation stay in its implementation.

Functional debugging may use whatever time/memory/heartbeat limit is needed under C21. A timeout, red expensive CI job or benchmark does not select work. The continuing development-feedback priority remains active. Outside that priority, C21's narrow cannot-finish-at-all exception permits necessary optimization only to enable the capability, then work returns to functionality. No per-construct export freeze, assessment receipt or preservation-proof checkpoint precedes implementation of the next required function.

## Required semantic distinctions

These are checks of existing requirements and controls, not new independent mathematical specimens or a replacement acceptance corpus.

| Concern | Required behavior | Functional owners / final evidence |
|---|---|---|
| Actual cells | Keep selected boundaries, components, direction and required coherence; use their actual action on returned data/maps. Endpoint equality, connectivity and a named cell without its required operations do not suffice. | T055/T056/T061, T043/T044/T049; T052/T062/T063/T106 |
| Allowed nonunique choices | Use the independently fixed family/supplier/stage and retain the actual candidate and dependent context. No new canonicality or substitution under old maps. | T115 (after the lean-categories task T118), with the fixed-result parts of T007/T013/T021/T032/T042; T039/T076/T106 |
| Missing required data | Established absent semantic selection/accepted agreement has the prescribed error before dependent dispatch. Invalid evidence, interrupted checking, absent realization and omitted candidate fields remain different. No default or theorem of absolute nonexistence is required. | T017/T021/T027/T055/T056; T015/T063/T106 |
| C6 declared preferred route | Validate a declared selection of a surviving binding and record it with the reading; it asserts no equality. No priority, order, cost or successful-provider fallback. Do not fabricate a preference in an original unresolved protected control. | T017/T055/T056/T028; T063/T106/T109 |
| Independent authorship | Mathematical comparison/choice families and laws are independently fixed. A leaf only supplies prescribed data/glue; no combined define/formalize/implement assignment or repository-label substitute for input separation. | Actual contribution boundary in T028 and the category tasks; T078–T082/T108/T109 |
| Correct composition and actual answers | Source laws, machine preservation, structural admission and independent opaque-answer assessment remain distinct. No model/helper test supplies missing source mathematics or actual production behavior. | Functional source/runtime tasks; T014/T039/T052/T062/T070/T076/T096 and full independent assessments |

Original RX05 full routes, omission/permutation/direction controls; RX06/RX07 actual reindexing and bidirectional nonidentity use; RX08 original ambiguity plus separate clarified positive; RX09 exact positive/constant-one negative; and full RX-LIFT actual maps/factors retain their independent expectations. Correct rejection does not pass a required positive.

## Working on one capability

The connected check starts at the public source entrance and follows the original mathematical
continuation. For the maintained RX-LIFT diagnostic, its driver must use `CasRuntime.KernelSession`,
preserving the source statements, all 22 prerequisite
bindings, selected comparisons and assertion order. Before F, the kernel observation of this input
(checkpoint M1.4) uses a protocol peer and checks the prepared requests and their operands. The
computed run after F (T041, T045) uses the actual independent manifest. The final run retains the original shared
200,000-heartbeat budget; a higher-limit functional diagnostic must be identified as such and
cannot discharge that final budget.
Changing the entrypoint is functional migration; the complete independent assessment remains
required under #24. Running the historical `CasCatalogue.Realize` driver cannot validate the
replacement. An opaque protocol peer cannot supply the original lift equations.

For a genericity claim, apply C12's frozen-baseline procedure: independently chosen new categories
and operations must reach unchanged consumers without accommodation to the kernel, contract,
old leaves or expectations. For a refinement, retain the source-authorized evidence, underlying
comparison and ambient inclusion; for a functor, consume its public target object and morphism
interfaces. These are the [MM001–MM012](spec.md#mathematical-model-acceptance) obligations within
the existing complete workload, not a smaller acceptance suite.

Across admitted constructor families, run the same applicable consumer with each actual selected
object/map and its required continuation. Use the existing MM and original workloads. For provider
replacement, check the complete independently specified relation and preserve permitted choices;
require exact equality only where the original contract requires it. Inspect actual imports and
run the required category consumer with unrelated optional engines absent when claiming locality.
These checks neither preselect the later independent contributor's specimen nor supply a new oracle.

## Kernel checkpoints and computed attainments

A kernel checkpoint (SC-014; [plan](plan.md#m1-checkpoints)) is observed through the public session with a protocol peer or an empty manifest. Use the commands of the [feedback loops](../../CONTRIBUTING.md#feedback-loops): `just loop "<session test module>"` for an observation with a protocol peer, and `scripts/accept_files.sh FILE …` with no `--manifest` for the empty-manifest observation of whole acceptance files. A gap with `NoImplementation` at a registered address is the expected outcome of a computational statement there. An internal error or a reader gap is a failed observation.

A computed attainment (SC-015; [plan](plan.md#computational-milestones)) is observed with the manifest of the category implementations of its milestone: the statement holds as a computed result. An observation with a protocol peer does not establish it.

## Delivery, proofs, trials and last-phase resources

The order of delivery, proofs, frozen trials and final performance is that of the [task list](tasks.md#execution-order) and the [completion milestones](plan.md#completion-milestones). T105 publishes and builds the compatible delivery tuple **before** the final measurements and independent assessments of that tuple. A correction during assessment follows the repair rule of the task list ("Dependencies and repair").

Performance is last. Preserve the original 99-root 3×3 `subspaces.kernel`, its full prefix and strictly-under-60-second total on the measured host. Preserve RX-LIFT's full 22-binding prefix and shared 200,000-heartbeat preparation/evaluation limit. Include required semantic/selection/lowering, planning, actual computation, admission, publication and observation-descriptor work; installation/build are reported separately. No hidden warmup, smaller matrix/root set, shorter context, changed tolerance or higher final limit manufactures success. Higher-limit functional debugging does not discharge these final measurements.

The existing [lifecycle observations](https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6706903869) and [inert-observation/exact-liveness controls](https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6707377395) remain actual-boundary obligations. The lifecycle phase that observes them is specified in the [notebook contract](contracts/notebook-session.md), section 6.

## Fixed inputs of the final assessments

V1 requires **153 permanent readings**, **134 positive extension questions in 14 files** (105 original plus 29 completion), the protected negative/environment controls, **RX01–RX10 and distinct RX-LIFT**, and **17 connected assertions** in four real-engine workflows spanning at least three areas. All required continuations and both fresh contributor-choice extension directions remain required. Complete readings of 153 permanent questions do not make every later full-B0 algorithm a new V1 execution requirement. Keep every ID visible, including unreadable, unavailable, wrong and unreached cases; a failed prerequisite does not produce a measured dependent result. [Specification, SC-001–SC-012][spec]

| Selected file | Positive questions |
|---|---:|
| `rx-lift-prescribed-stages.cas` | 26 |
| `rx-lift-source-comparison.cas` | 8 |
| `rx01-selected-orders.cas` | 4 |
| `rx02-complete-core-action.cas` | 7 |
| `rx02-two-subsets.cas` | 2 |
| `rx03-complete-automorphism-arrows.cas` | 14 |
| `rx03-cyclic-automorphisms.cas` | 12 |
| `rx04-square-bound.cas` | 7 |
| `rx05-carrier-diamond.cas` | 13 |
| `rx06-reindexing.cas` | 10 |
| `rx07-f9-transport.cas` | 17 |
| `rx08-ordinary-kernel.cas`, staged from the independently assessed clarification | 7 |
| `rx09-successor-series.cas` | 6 |
| `rx10-fixed-execution-question.cas` | 1 |
| **Total** | **134** |

The original RX08 source and its seven-question ambiguity control remain separate from the positive clarification. RX05 runs all four declaration environments. RX09 retains the exact negative admission observation. RX10 retains the same complete question under its six success/failure conditions and its callable/session controls. The retained runner verifies source hashes against `scripts/probes/fixed_question_export_inputs.json`; its counts do not establish mathematical correctness. [Fixed source selection and controls][runner]

| Original input | SHA256 / revision |
|---|---|
| RX-LIFT prescribed source | `a5568912e5869e36c60d9450f3bb3c97e0f43e869f820b1da225d16db940746a` |
| Permanent `linear_algebra.cas` | `90e04dbc4bcde8d201448ee5e2c2a974eaddfa1d828554cf559f350bba30e927` |
| Original six-cell `notebooks/kernel-v1.ipynb` | `25bae8c383936d8522d763b0bedfb4435dd52314de894c78729fce5c41834b6c` |
| Hash-pinned engine requirements | `9b660283e5d1b0bd07c62d7752b9e0dddb3f4b9bca9870a1f10882602d4c6648` |
| Notebook requirements | `8c27163fa2d4bc0196af8ffde739c7a53093f94ad15fa0b33d1cbcd4b4558bbf` |
| RX-LIFT computational specimen | leaves `a1d72cfa1daf5cff15300d71f889459c7953e374` |
| Connected workflow computational specimen | leaves `2c8b9040ea68513c34817f5c7b6fa5a5ce6b1252` |
| Existing set registrations used by the connected workflows | leaves `865df49ad0b0b133d5bcfd282f380aa213eb5fff` |

### Environment

The environment is the research container `sage-research` (Linux x86_64). It holds SageMath 11.0.beta5 as a source build in `/sage`, with the interpreter `/sage/.venv/bin/python3` (Python 3.14.10), GAP 4.16.1 through Sage `libgap`, PARI 2.17.4, Singular 4.4.1, Maxima 5.49.0, SymPy 1.14.0, python-flint 0.9.0, Julia 1.12.7 with Oscar 1.8.2, and Macaulay2 1.24.11; it holds no passagemath. The interpreter imports pydantic 2.14.1, and the v2 SDK of the contract at `a0417b0` declares `pydantic>=2.14.3`: T326 pins it in the image. Lean and Lake come from `elan` with the toolchain of `lean-toolchain` (Lean 4.33.0 and Mathlib v4.33.0 at `db584cd6d46c92f209a44c0f1c829460d327499d` on the kernel branch until T105 ports them to the image toolchain, #90). Standard Bash, Git, Python 3, curl, tar, GNU time and `uv` are available. [Lean distribution documentation][lean] [uv commands][uv]

### RX-LIFT

The first-stage driver of T041 runs the following ten suffixes of `reconstructed_extensions_20261024.complete.lift.`, in one shared harness session:

```text
first_inverse_on_carrier
first_inverse_on_scalar
first_defining_map
first_backward_action
first_nonidentity_coordinate
first_full_pairing
first_whole_factorization
first_factor_comparison
first_factor_sample_one
first_factor_sample_two
```

Each selected question has **one shared 200,000-heartbeat preparation/evaluation budget**; the first retains **all 22 preceding bindings**. The last two reader cases occur at original lines **73 and 76** with **32 preceding bindings**. No question may reset the budget between preparation and execution. A first-question or through-ID prefix is a diagnostic only.

**The complete RX-LIFT obligation is larger than those ten questions.** The fixed 134 execution runs all **26** questions of `rx-lift-prescribed-stages.cas` and all **8** of `rx-lift-source-comparison.cas`, including successive lifts, complete equations, nonzero final factors, and later applications. Passing the ten-question diagnostic alone does not establish full RX-LIFT completion. [Original source, probe, and fixed runner][rx]

### The 3×3 performance specimen

Its original source is `tests/acceptance/linear_algebra.cas`, with
`W := span({(1,0,1),(0,1,1)})` over `ℚ³`,
`N := [1,1,-1;0,0,0;0,0,0]` in `Mat₃(ℚ)`,
and question `subspaces.kernel` asking `W = N.ker()`, together with the original preceding bindings. “99 roots” identifies its original trace graph; it is not a polynomial root count, nor a mandate that the replacement's internal representation have the same node count.

**Present limitation:** the existing file measures interpretation/identity only. Its successful exit cannot establish complete computation or the full under-60-second requirement. None of the three inspected frozen manifests supplies the exact accepted `mor.sets.matrix_ker` operation. RX's `fun.arrows_modules.kernel` on `cat.arrows_modules_r` is a different accepted operation, although its implementation contains useful established-engine computation. The workflow diagnostic supplies matrix rows; the existing symbolic leaf supplies span. Combining those names does not provide a matrix-kernel binding or a proof that different source operations coincide. [RX manifest][legacy-manifests] [Workflow manifest][workflow-manifest] [Existing manifest][existing-manifest]

The selected implementation work is a native-v2 production binding of a category task, in the leaves repository's existing `backends/` area, to **the existing** `mor.sets.matrix_ker`, with Sage `M.right_kernel()` and the exact current coordinate/scalar interface. Use the existing tuple/row, span and equality operations needed by the original question, with no overlapping registration priorities. The production profile at `examples/kernel-v1/benchmark-leaves.json` is planned operational configuration, not a new mathematical specimen, relation or oracle. It must retain the actual returned subset/subspace and all public operations needed by the original equality assertion. Source `LinearAlgebra.ker` and `span` fix their meanings. Any use of a basis/normal-form encoding or a conversion from the arrow-kernel interface must consume its independently formalized interpretation/derivation first; a basis tag, engine method name or equal dimensions supplies no such relation. A direct binding to the existing matrix-kernel operation needs no invented equivalence to the arrow operation.

The execution mode of the benchmark (T103: `CAS_BENCH_EXECUTE=1` with `CAS_BENCH_REPORT_OUT`) must fail unless the original complete assertion actually holds, its returned data/continuation checks succeed, and **total elapsed time is strictly below 60 seconds on the measured host**. Start its total before reading/building the complete original binding scope; include semantic analysis, graph construction, compilation, provider startup/negotiation, actual computation, result validation and publication. Record each phase and the complete selected question/source/manifest identity. Do not use precomputed results from the interpretation-only invocation, reset the timer between phases, silently run twice, or retry a failed effect. Build/dependency installation occurs before this run and is reported separately. The existing parent `/usr/bin/time` measurement is retained alongside the internal phase total. All failures and missing observations remain failures.

Do not use the default `matrices.kernel` 2×2 example, a 66-root substitute, or the existing wrapper's 180-second diagnostic cap to pass this requirement. Do not inflate the RX budget either. [Existing benchmark][benchmark] [Specification FR-040][spec]

### Connected workflows and the notebook

The four connected workflows are the unchanged `examples/kernel-v1/*.cas` files with **17** named assertions, each holding exactly once with a completed backend dispatch: **8 selected-arithmetic**, **2 finite-pullback**, **3 matrix-iteration** and **4 presentation-transport**. The actual V1 notebook is the original six-cell `notebooks/kernel-v1.ipynb`; the eight-code-cell `demo.ipynb` is a different demonstration. The independent harness `cas-harness` has a computation-only mode (`--computation-only`), an actual engine observation (FR-050). The generated `questions.json` and `question_readings.json` hold 142 of the 153 admitted IDs (FR-110). [Workflow wrapper][workflows] [Current harness][main-harness]

## Sources

[spec]: spec.md
[runner]: https://github.com/dzackgarza/lean-cas-dsl/blob/016d3d34e526297034c7e5907a3da14368176b36/scripts/ci_kernel_candidate.py
[rx]: https://github.com/dzackgarza/lean-cas-dsl/blob/016d3d34e526297034c7e5907a3da14368176b36/scripts/probes/rx_lift_runtime.lean
[benchmark]: https://github.com/dzackgarza/lean-cas-dsl/blob/ea7b115c28b090648a479f85a4d95d02ce2d4888/benchmarks/question_identity.lean
[workflows]: https://github.com/dzackgarza/lean-cas-dsl/blob/016d3d34e526297034c7e5907a3da14368176b36/scripts/ci_kernel_workflows.py
[main-harness]: https://github.com/dzackgarza/lean-cas-dsl/blob/ea7b115c28b090648a479f85a4d95d02ce2d4888/CasTools/Harness.lean
[lean]: https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/
[uv]: https://docs.astral.sh/uv/reference/cli/
[legacy-manifests]: https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/a1d72cfa1daf5cff15300d71f889459c7953e374/diagnostics/extensions-20261024/leaves.json
[workflow-manifest]: https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/2c8b9040ea68513c34817f5c7b6fa5a5ce6b1252/diagnostics/v1/leaves.json
[existing-manifest]: https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/865df49ad0b0b133d5bcfd282f380aa213eb5fff/leaves.json
