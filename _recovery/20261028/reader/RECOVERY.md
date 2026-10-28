# Reader recovery after the workspace reset

This is a newly written recovery record. It is not a restored execution log or a claim that the recovered source has been rebuilt in the new executor. All Lean work remains held. No live repository source or index was modified.

## Exact recovered content

These recovered bytes match hashes recorded before the reset:

| File | SHA-256 | Status |
|---|---|---|
| `reader-ordered-evidence.patch` | `79e4d99ccae5bb6a9123d4e8889afeb9c6f8339db699cee2d8b4f7bf11ad598b` | Exact final source patch |
| `reader-evidence-view-engineering.patch` | `86a496c383838334e4849a69f19779a5ac6afc38135b0583345a576f632c3956` | Exact final additive-control patch |
| `EvidenceViewEngineering.lean` | `5c1b96d212540e5cba2fd46cda333336686decd2148bec2ebc2d342ab606d37a` | Exact final control source |
| `EvidencePresentation.aabdf4b.lean` | `3dd5a6c9449237728a11ed2fdd04d136cc21f5c64b823811a82eaf7588a8cd3b` | Exact lost aabdf preimage, before ordered-view patch |
| `EvidencePresentation.final.lean` | `ea1f8a4b718987bf3046e4b908509c405afe07f636664f76ca1996c903f75454` | Exact final postimage |
| `ProofRefinement.final.lean` | `1822f4ba4395db521acc0e6af8c517f565bc26718dd0eadfd9a9e5ecfcc0c5e6` | Exact final postimage |

The two Language fragment files and source-patch-segments.json are explicitly partial sources recovered from retained tool inputs. They are not complete Language.lean files. The final patch is exact, including its original hunk alignment. Fragment-based difflib initially selected an equivalent blank-line alignment; restoring the historical alignment produced the original final hash.

## Required baseline and missing earlier work

The final patch was prepared against kernel `aabdf4b6e61e31d9d7f2651ffdae7e85f95270f5`, whose complete Language.lean had SHA-256 `095ce98f9e3e7889e83ea42d8b0656ba249c59496b22ba458b9185ffd7115a19`. Its final postimage after this patch was `09418a2f490ec26f5a90a5323318cb174a14914cb4267a510801bb9a342c26d0`.

The fresh published-base checkout is `3a4b84e18d644662ee75238716c4861097b2f9dc`. Its ProofRefinement.lean already matches the lost aabdf preimage `7cb2193811cbea259af2828693843289261e08d73e2dacf4fa33ca61f040d93a`. Its Language.lean and EvidencePresentation.lean are earlier source; applying the recovered final patch alone does not restore all intervening reader work.

The following earlier raw patch bodies are absent from this agent's retained post-compaction context and have NOT been fabricated:

- `/tmp/reader-parameter-selection-boundaries.patch`
- `/tmp/reader-operation-supplier-continuity.patch`
- `/tmp/reader-typed-parameter-original-route.patch`
- `/tmp/reader-supplier-continuity-control.patch`, including the complete 138-line ReaderSupplierContinuityEngineering control
- Full intermediate 595/3188/50fa input-provenance, selected-source recovery, speculative-cache isolation, action-declaration/dependency, and selector implementation patches

Only their design summaries, names, historical results, and some exact small fragments remain. In particular, the final aabdf inference correction explicitly typed `children : Array Value` and replaced `originals.push source` with `Array.push originals source`; those two edits are not a substitute for the missing preceding implementation. Recording-service/tool-history recovery is still required for exact restoration of those earlier patches. Reimplementing them later must be labeled new candidate work and revalidated.

## Historical verification, not rerun after reset

- Live reader gate `1793153942203537442`: 17/18 passed at aabdf, with only original series and matrix admission cases remaining; 532 owned artifacts authenticated.
- Final guarded prototype `1793156355399505569`: passed in 5.18 seconds, including original-first/type fallback, shared heartbeat context, assignment/message isolation, malformed/open/wrong/internal failures, valid auxiliary retention, rejected auxiliary nonleakage, concealed sorry refusal, and new-assumption refusal.
- Final exact three original admissions through the proposed establish, `1793156426001408875`: passed in 9.36 seconds at unchanged shared question budgets; an independent synchronous safe-definition kernel check validated the original limit, series, and Type-valued matrix Invertible targets.

The full log/receipt files were lost with the workspace. These historical identifiers and outcomes are preserved from the retained messages; this file does not impersonate those lost artifacts. The fixed integrated reader/failure gates must still run after complete source and toolchain restoration.

## Final correction's design

The same registered provider first receives the exact original target, then checked stored-field and closed-Type views only after ordinary rejection. No mathematical-name case is added and no heartbeat allowance is reset. Tagged/internal failures and malformed results cannot select a new view. Failed attempts restore caller metavariables and ordinary messages; only a checked successful environment may be committed, preserving valid auxiliary theorems. New returned constants must exist in the checked environment, and Lean.collectAxioms refuses concealed sorryAx or assumptions absent from the original checked environment. Explicit class-synthesis consumers retain their earlier type-visibility behavior.

Apply the recovered source and control patches under the shared source lock only after restoring/reconciling their baseline. No source has been applied by this recovery task.

