# Kernel MVP pause checkpoint — 2026-10-28

The owner requested: **Push all work and pause.** No build or implementation
worker remains active. This directory preserves recovered implementation drafts,
original trial inputs, and provenance; it is not an integrated release or an
acceptance result. Do not automatically import or execute a `candidate` file.

## Published source

- Kernel: `60829a1f7db040f6a8ae394777c0a10bc00d3946` on
  `dzackgarza/lean-cas-dsl`, branch `work/kernel-v1-20261023`, tree
  `7631c8218e33056e4ca20430d8d03839e0457b15`.
- Independent upstream interface: `206045848e028950bd01470aea1871af058c4843`
  on `dzackgarza/lean-categories`, branch `work/ordered-products-20261028`,
  tree `83ba841d2e67dc9b6546a8d45c5de5ad7a3526fe`.

Both branches were fetched back and their complete trees compared with the
staged local sources. Both local source checkouts were clean afterward. The
kernel checkpoint retains the exact recovered final evidence-presentation
patches, based on the surviving published `3a4b84e` source. The upstream
checkpoint contains six byte-exact recovered Lean files; its two documentation
additions are explicitly reconstructed, not claimed byte-identical.

## What is preserved here

- `reader/`: exact ordered-evidence source/control patches and recovered full
  evidence-presentation/proof-refinement files, plus partial Language fragments.
- `product/`: exact declared-product module, component-schema engineering
  control, product execution patch and contract-export patch; recovered
  ObjectPresentation source and a labelled schema reconstruction helper.
- `executor/`: exact recovered callable-frame and endpoint-receipt patches,
  original-view engineering source, retained excerpts, and an incomplete
  candidate containing only the identified slices.
- `runtime/`: thirteen unchanged archived trial inputs/runners, source and
  compiler/cache provenance, and unexecuted reconstruction drafts for the
  external verification runner. Reproducible dependency checkouts, binaries,
  downloaded archives and caches are deliberately not duplicated in Git.
- Root manifests: exact recovery hashes, source publication trees and patch
  simulation results. Absolute workspace paths are historical locations and
  must be rebound explicitly in another workspace.

The current kernel passed the existing permanent-assertion inventory check,
reuse-record and no-leaves checks, and all sixteen source-guard self-tests.
No kernel, contract or mathematics-owner module has been compiled after the
workspace replacement. The recovered external runtime scripts are unvalidated
drafts; `lake.sh` and the scratch-diagnostic runner remain unrestored. The
restored external dependency tuple is contract `34bb8abb`, mathematics
`3bd4d3d9`, Mathlib `db584cd6`, and official Lean 4.33.0. The newly published
upstream source has not been selected for a new build.

## Work that did not survive completely

The workspace replacement removed the unpublished kernel checkpoints
`59ffe654`, `595a4c7`, `31882df`, `50fa5a0`, `160b47e`, and `aabdf4b`,
contract checkpoints `6b216b5` and `1147199`, their local bundles, and the latest
runtime logs/artifacts. Their complete history and source trees are not present
in this recovery. Earlier historical passing verdicts do not apply to the
current source and their absent logs have not been fabricated.

Missing source includes the complete original-view/Trace traversal, prepared
producer memoization and completed-observation ownership integration; selected
supplier and speculative-cache recovery; shared operation-source acquisition;
and the later connection-retirement, intrinsic-composition, original literal
functor-action and complete endpoint-priority repairs. Some exact slices and
design records survive in the per-area recovery inventories. The full final
Language/component/schema patch and prior contract framing changes are also
incomplete. Distinguish exact recovered bytes from any future reimplementation.

## Resume boundary

Continue the generic KM1–KM9 mechanisms, retaining `completeRoutes`,
`ProofRefinement.construct`, and `executePrescribedLift`. Reconcile the missing
source with these recovered patches, preserve mathematical ownership and fixed
questions, and verify one exact integrated source tuple. Then rebuild the public
tools, run the four connected real-engine workflows and the ten independently
fixed extension trials. No assertion, expected answer or resource budget was
changed during recovery. Kernel-MVP readiness remains unestablished.
