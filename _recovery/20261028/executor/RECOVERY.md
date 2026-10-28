# Executor lifecycle recovery — 2026-10-28

Recovery stopped at the user's instruction to push all work and pause. This directory is a source-recovery draft, **not a rebuilt or complete replacement for the lost worktree**. No live checkout file was changed and no Lean command was run during recovery.

## Exact recovery

- `exact/OriginalViewLifecycleEngineering.pre_diagnostic.lean` matches the previously recorded SHA-256 **2b6a4857928f115d8e4c1528644b14839789a30796f5b0ac68526b11d80cda85** byte for byte.
- `exact/OriginalViewLifecycleEngineering.lean` applies the exact subsequently recorded diagnostic-message patch. Its recovered SHA-256 is **eabe087f5b5355ac9177f67097d744a7e65dc10204a3e1dc73862ad0761b3b7b**. This is the full version known to this agent's 2026-10-27 successful four-control slice; this agent has no record of later modifications to it.
- `patches/01-callable-frame.exact-operations.patch` and `patches/02-refreshed-endpoint-receipt.exact-operations.patch` reproduce the authored apply-patch operations preserved in this agent's tool inputs. Only the target path was made relative. Both replay successfully against a **separate** copy of published `3a4b84e18d644662ee75238716c4861097b2f9dc`.
- The additional `exact/*.fragment.lean` files reproduce source snippets visible in retained successful-session tool outputs. They are exact excerpts, not full-file recoveries, and no original whole-file postimage hash is available for them here.

The first authored patch adds an explicit internal `ActionDataTemplate.callableFrame`, preserves its original map and complete endpoint receipts through rendering/validation/observation, and marks this pure frame complete once the original map is complete. It retains the existing public `typedMap` encoding.

The second fixes object-action observation overwriting a refreshed actual comparison receipt with the pending receipt. It checks the complete selected comparison, validates the refreshed two directions and exact returned endpoint packet/owners, and retains the current receipt.

The endpoint-position excerpts are the compiler agent's observed final source: direct codec endpoint fields retain their exact packet positions; wrappers/composition prefix those positions; action/formal/reference endpoints remain pathless. The runtime scope annotates only those selected positions after exact packet, supplier and full formal checks.

## Draft layout

`base/` contains untouched source bytes read with `git show` from published `3a4b84e18d644662ee75238716c4861097b2f9dc` for Realize, ComputationalData and Trace.

`candidate/` is **only** that base plus the two exact authored Realize patches and the exact recovered original-view engineering module. The saved endpoint-position and original-view fragments have **not** been integrated into it. ComputationalData and Trace in this draft are still the published base. In particular, the recovered engineering module needs missing Trace/view/ownership integration before it can compile or pass.

`patches/known-authored-slices.git.patch` is a standard unified diff of the already-written candidate against the saved base, including the recovered engineering module. It is not a coherent full-kernel recovery patch.

`evidence/file-manifest.json` records hashes of the recovery text files. `evidence/original-view-source.json` records the successful historical hash match. `evidence/historical-validation.json` is a transcription of retained tool results, not recovered original build output and not a current verification receipt.

## Precise missing bytes and integration gaps

1. **Full original-view Trace implementation is missing.** The retained summary records `Node.valueView(receiver)`, `Node.constructionApexView(receiver)`, and `Node.dataFieldView(receiver, expectedType, fields : Array (Name × Nat))`; full `Node.mapTermsM`, question/term traversals, `Trace.aliasProduced`, strict legacy `Trace.alias`, and `Trace.valueOrigin` postimages are not available here. The known behavior was: aliases require full type/value definitional equality under rollback, record an explicit fresh value-view producer instead of copying an operation Node, and `valueOrigin` follows only validated value-view links with cycle rejection. Do not treat this prose as exact source.
2. **`checkedDataFieldView` full source is missing.** The recovered runtime handler refers to it. The retained summary says it independently checks `DeclaredAdmission.projectionPath?`, the full expected type and projected value, and derives a public record path from a fresh symbolic source. Its exact implementation must still be recovered or reimplemented and tested.
3. **Runtime view integration is incomplete.** Exact handler and `captureDataFieldValue` excerpts are saved. The new `realizeFreshWith` callback declarations/call-site additions for `capturedMapEndpoints` and `callableHasSetsContext`, along with complete surrounding source, have not been recovered into the draft.
4. **Prepared-producer memoization is missing.** The known change stored every closed `realizeUnobserved` result under the exact selected Expr handle and made the outer `realize` miss path use `realizeUnobserved`. This shared one captured invocation across views while keeping independently addressed equal producers separate. Exact source/comments for those changes are not recovered here.
5. **Completed-result ownership guards are incomplete.** The retained summary reports eight observation boundaries plus the prospective known-actual path checking data owners before completed-data short-circuits. Visible earlier snippets included `realizeValueObservation`, `realizeObjectObservation`, `realizeArrowObservation`, `realizeCallableObservation`, `realizeOperationObservation`, and `frameObservedMorphism` (checking input/source/target). The exact full insertion list and full-file postimage are missing; do not infer that the draft restores these guards.
6. **`CompletedObservationOwnershipEngineering.lean` is not fully recovered.** Its known historical full-file SHA-256 is **3b5c03580ff0c6555bb98857cf66d1c064d9a4ec140c0cd2d5f57eb04ce92543**. The prior thread displayed only a prefix, so no fabricated full file has been written. It tested live/foreign/expired observation, direct and prospective map/value/record reuse, and portable output reuse after an opaque input owner's session ended.
7. **Earlier occurrence and completed-result integration across other modules is missing.** The lost index also changed Semantic, OperationAgreement, QuestionComparison, RoutedResultPlan, SelectedLift, SimpleServiceRequest, StructuredProjection, LiftedSubobjectData, Language, ContextParameterProbes and ProducerOccurrenceProbes. Their complete source patches were not authored by this agent and are not present in retained exact inputs.
8. **Later unpublished commits are outside this retained source context.** No exact source is available here for the requested `160b` stop/reuse cursor, intrinsic composition, literal-functor changes, or `aab` endpoint-priority changes. No such change has been guessed or reconstructed. This directory must not be labelled as a recovery of those commits or of the complete lost `59ffe`/`595a4`/`31882`/`50fa`/`160b`/`aabdf` sequence.
9. **Historical complete-source hashes are identity clues only.** Before the authored frame patch, the recorded Realize source hash was **f97910e8204ee0c77cceff858554f9826403b01039c7650b3f4ee648da1cb253** and Trace was **03d646731ebc786b19721cbc1f6b84b290b7d84e42bba3ed23e6f1d5959ff646**. Neither full postimage has been recovered here. Final successful full-file hashes were not printed in this agent's retained outputs.
10. **Two reported follow-ons were not repaired in this slice.** The proposed explicit subset-extent Node/runtime migration was still awaiting the parent Trace API decision. Completed construction execution still cached a bare apex as well as its selected producer key; the handoff identified occurrence-isolation risk for distinct construction producers with equal formal apexes. Do not present those notes as implemented repairs.

## Historical verification boundary

The original full source (now lost) passed `focused-build-1793143294392299960`, exit 0, 404.47 seconds, with `changedDuringBuild: []`. The verified slice comprised ComputationalData, Realize, OriginalViewLifecycleEngineering, CompletedObservationOwnershipEngineering, EndpointComparisonOccurrenceProbes and PositionedInterfaceScopeProbes. It used contract `34bb8abbdbb49699015f63840cf86ed67f438003` and the existing protocol fixture.

The earlier diagnostic isolated the projection bug precisely: selected value, clean category/endpoints, owner and one dispatch were correct; only `actualData` was false. The original fix and unchanged controls then passed. Those historical facts do **not** establish that the partial recovered candidate currently compiles or passes. No original validation log or full successful source bundle was restored by this agent.
