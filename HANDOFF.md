# V1 kernel MVP: authoritative integration handoff

## 1. The task

Finish the usable V1 kernel of `dzackgarza/lean-cas-dsl`, including the mathematical interfaces and computational contracts it needs. Deliver a working computer algebra system whose supported extension mechanisms let a new leaf author implement registered operations through the public contract. Ordinary leaf work must not require repeated repairs to generic kernel infrastructure.

The assignment includes implementation, integration, actual computation, independent extension experiments, and delivery. Continue beyond the interrupted build and beyond passing isolated probes. The completion conditions below define the whole task.

Source conversation: [Finish Kernel MVP Work](https://chatgpt.com/c/6adc8d51-f270-83ea-ac4d-bcb9911c54d8). This handoff was prepared on 2026-10-25 from the conversation's user instructions, its attached mandate as printed in tool output, its active-branch interruption record, and current GitHub source. The final recorded activity was an integrated consumer build and investigation of `CasGates.KernelPurityProbes`. No final successful build or MVP completion appears at that boundary.

Work primarily in the Pro cloud container. The rack connector's home-directory access is available for necessary supporting material. It is not authorization to move the entire build and execution workload to the user's server. Save and push coherent source changes throughout the work. Verify published source by fetching it back and comparing the complete tree. Preserve evidence separately from source so a container restart does not destroy the only copy.

## Current continuation state — 2026-10-25

The published restart source was fetched and verified at `29d3d60500cf1e4d2b49de0355ec8017eaa836bd`.
The old cloud checkout was inspected before automatic scratch cleanup removed it.
Its clean local integrated tree matched that published checkpoint. A surviving clean
repair commit `a290701b016f1682de56c4f6de01cf45aa36a9d1` supplied the missing public
`LeanCategories.Catalogue.FamilyFibration` import in `KernelPurityProbes`.
That one-line source correction is reconstructed in this commit with its ownership
record. The purity predicate and every positive and rejection control are unchanged.
The names have not moved: Realization owns the transport field and domain helper;
FamilyFibration owns `totalCat` and `reindexFunctor` and publicly imports Realization.
The gate's private import closure did not export those names to the probe.

The earlier `integrated-consumers-29d3d60.log` continues past the probe failure and
ends with `fatal library error, lookup self`. Its stale `status: running` record
is not a successful or active build. No matching process survived inspection.
No post-import-repair build or RX10 execution was recovered.

Work now uses `/workspace/scratch/735f437b0adf/lean-cas-dsl`, with toolchain and
packages restored in the same cloud workspace. The latest independently saved
evidence archive, Library `libfile_94b086b3c1308191b67e0c34e0d4c364` version 25,
was recovered intact (22,722,153 bytes; 863 ZIP members) and extracted beneath
`evidence-archive/restored`. Existing records are retained with their original
paths and producer identities; new runs use separate output paths. Runtime-only
path rebinding changes no mathematical input, registration, or expected outcome.
The selected notebook revision in the committed package manifest is
`4c6c2a77abcc717513a65ca35723ed428647e1bd` (`worker` subdirectory).

This source checkpoint does not discharge the completion conditions below.
The next checks are the explicit-import probe, coherent consumers and native
execution surfaces, the unchanged RX10 and fixed mathematical inputs, then the
final API, connected workflows, independent assessments and frozen trials.


## 2. Completion conditions

All rows must be discharged at a coherent final source combination. Earlier observations identify what to preserve and rerun; they do not establish results for the latest candidate.

| Required result | Acceptance condition | State at interruption |
| --- | --- | --- |
| Integrated kernel | Kernel, contract, mathematical dependencies, relevant probes, gates, tools, native executables, and notebook surface build together. Preserve applicable PR #63/#64 behavior within the PR #65-derived implementation. | Latest published kernel is `29d3d605`; its consumer build has a concrete purity-probe failure. No complete green final build. |
| Registry-derived interpretation | Mathematical choices come from accepted declarations. Dependent parameters, selected structures, tuple/destructured binders, closed maps, refinements, and admission use generic paths. Preserve genuine ambiguity. | Substantial implementation and earlier passing reader checks exist. Current full consumers and fixed extension readings remain to be established. |
| Compositional resolution | New objects acquire old applicable operations; new generic operations reach old objects. Object and morphism actions preserve comparisons, actual parameters, reindexing, and refinements. | Generic machinery exists. Final independent trials and compositional arguments remain required. |
| Computational transport | Nonidentity transport, symbolic and opaque callables, successive computations, exact endpoints, and session ownership work with actual returned data. | Earlier connected runs passed. Latest candidate requires reruns, including RX10. |
| Complete structured results | Computed kernels, cokernels, subobjects, limits, and lifts expose their required defining maps and permit later operations. Creation comparisons work through accepted general data. | Prescribed-lift action-data repair is integrated. Its scoped checks pass in the record. Full fixed structured-result and successive-lift trials remain open. |
| Stable public contract | Every advertised V1 form has complete requests, replies, dependent parameters, validators, ownership rules, and worked examples. A leaf author can implement it from public material alone. | Contract source exists. Final API generation and sufficiency checks against the final source combination remain open. |
| Permanent mathematical meaning | Independently compare every admitted question's complete typed meaning. Keep revision provenance separate from meaning. Preserve protected assertions and the independent migration/admission boundary. | Earlier complete permanent reading/review exists. Final candidate export and independent assessment remain required. |
| Correct failures | Distinguish invalid mathematics, ambiguity, absent implementation, unavailable backend, malformed reply, well-formed wrong answer, and internal/resource failure. A change of leaf must not change the question. | Earlier RX10 exposed real defects. Final fixed-question conditions, successful callable return, and session/reuse controls remain open. |
| Useful CAS | Run connected real-engine workflows through the existing execution surface. Reuse intermediate values and structured outputs; include nonidentity transport and inherited operations. Verify notebook execution where used. | Earlier demonstration passed at an older source. Current native binaries, notebook output, and final demonstration need verification. |
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

### A. Recover the actual source and close the interrupted build

Recovery of the surviving source and archive is recorded above. Preserve that recovered state and inspect only newly relevant source or processes before editing. Read `INTENT.md`, `AGENTS.md`, `CONTRIBUTING.md`, and applicable source/style guidance. Fetch the active branches and check their current tips; the SHAs in this handoff are verified restart anchors, not permission to overwrite newer work.

The latest kernel checkpoint verified on GitHub is:

```text
branch: work/kernel-v1-20261023
commit: 29d3d60500cf1e4d2b49de0355ec8017eaa836bd
tree:   84c7cf4f61c7057a9bc6dc905a1cc2ffc3de168c
```

Inspect `kernel-verification-20261025/integrated-consumers-29d3d60.log` in the old cloud workspace if it survives. Its last recorded output reports that `CasGates.KernelPurity` built, followed by these failures in `CasGates/KernelPurityProbes.lean`:

```text
48:6 Unknown constant CasCatalogue.CategoryFamilyRealization.transport
49:6 Unknown constant CasCatalogue.CategoryFamilyRealization.totalCat
50:6 Unknown constant CasCatalogue.CategoryFamilyRealization.reindexFunctor
53:4 Unknown constant CasCatalogue.CategoryFamilyRealization.canonicalDiscreteCommRingTransport
57:0 the kernel-purity gate accepts ...domainTransport
     (carries no mathematics expected): []
```

The current published probe still has these references. Diagnose their declaration visibility and ownership against the selected upstream `LeanCategories/Catalogue/CategoryFamily.lean`, its module exports, and the gate's imports. The final conversation described former-namespace references, but the recorded searches also show the `CasCatalogue.CategoryFamilyRealization` namespace in upstream uses. A namespace rename is therefore not an established repair. Find the actual exported declarations and repair the probe's access to them.

Preserve the distinction the probe checks: registered categorical plumbing is allowed; a domain-specific commutative-ring transport helper remains forbidden. Retain the rejection controls. Do not loosen the purity predicate, expand exemptions, or drop the failing control. Check whether the final `domainTransport` error follows from the unresolved declaration before treating it as a separate gate defect.

Finish all consumers of the repaired candidate and then the required native/tool/notebook build. Record the full source combination and unchanged source state for each run. If the old build is still active, do not mutate its inputs. Use isolated source/build locations for a new candidate.

### B. Run the unchanged bindings and complete interpretation exports

Use the fixed inputs and reconstructed drivers described below. Read their reports, not just their process exit status. A diagnostic may exit successfully after writing failed bindings.

The most recent complete binding diagnostic recorded these unresolved consumers on an older candidate:

- Prescribed-lift `expectedF`: ordinary definitional-equality budget exceeded.
- Source-comparison `i0`: interpretation failed.
- RX06: the complete reindexed map failed admission.
- RX08: the constrained whole map failed admission.

Later admission, context, endpoint, and refinement repairs exist. Rerun the same expressions before deciding which defects remain. Repair generic owners; do not change the fixed questions to fit the implementation.

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

| Repository / role | Branch | Restart revision |
| --- | --- | --- |
| `lean-cas-dsl`: kernel, language, runtime, assertions, tools | `work/kernel-v1-20261023` | `29d3d60500cf1e4d2b49de0355ec8017eaa836bd` |
| `lean-categories`: independently supplied base interfaces | `work/kernel-v1-interfaces-20261023` | `9508da173de86670c4e0c8a4632e2df7d2335949` |
| `lean-categories`: mathematical extensions and evidence repairs used by recent consumers | `work/kernel-v1-independent-extensions-20261023` | `82d1370de372a00a86391b74fc2566c9547dfcb6` |
| `lean-cas-dsl-leaf-contracts`: protocol and API export | `work/kernel-v1-contract-20261023` | `90d7d3f1833cff39b77024dcee2dc43213e623ad` |
| `lean-cas-dsl-leaves`: existing workflow specimen | `work/v1-contract-diagnostic-20261023` | `2c8b9040ea68513c34817f5c7b6fa5a5ce6b1252` |
| `lean-cas-dsl-leaves`: independent callable-form specimen | `work/kernel-v1-independent-leaf-20261024` | `fa0856dfc365c497a25e4a94019a1cb08b79c4d1` |
| `lean-jupyter-kernel`: existing notebook worker | Read selected package lock and runtime override | `4c6c2a77abcc717513a65ca35723ed428647e1bd` (`worker`) |

The kernel, both mathematical branches, contract, and independent leaf tips above were checked live during handoff preparation. The workflow-specimen revision comes from the published handoff and demonstration documentation. Verify its actual selected tree before running.

`lean-cas-dsl/main` remains `6e67b1e1dd118811c8cb443cc558221095e98573` at inspection. The active work branch contains the substantive implementation. The source integrates that main with `b0/kernel` at `4bcd912`, retaining the PR #65 architecture and the applicable PR #63/#64 obligations. Do not start again from main or replay old branches wholesale.

`HANDOFF.md` at the current kernel tip has useful evidence references but an obsolete opening source table and accumulated older runtime/status paragraphs. Prefer exact source and producer records for present state. In particular, its opening kernel `b814a19` entry is older than the verified tip.

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
