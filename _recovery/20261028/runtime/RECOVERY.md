# Runtime recovery at pause

The user requested that all work be pushed and paused. No runtime process is active. No guarded verification or kernel build was started after the reset.

## Restored inputs

- Thirteen fixed-trial input and runner files were recovered verbatim from the historical v45 archive. Every member matched its archived members.json hash and byte count. fixed-input-recovery.json gives the original paths and provenance. The files remain read-only.
- The source archive is 79,250,338 bytes, SHA-256 cb4b501dbe4bed8f7a10d86946892a69a8e585af0bb92b4e12b0db0a2b7d5d06. Historical verdicts in it are not new candidate evidence.
- No recent aabdf/160b/50fa kernel or 114 contract checkpoint, usable compiler, or compiled kernel artifact survived in the inventoried older workspace. The inventory reports preserve these findings. Parent source recovery is separate.

## Reproducible prerequisites

The official Lean 4.33.0 release was downloaded and verified against GitHub's published SHA-256 4b3fb03c29a1e0a253fb1d11f9bae3725f19a0dc6fc09b3ea16d2c9df3349e2c. Its compiler reports commit d8b18978322de05a8f3dba51ef03cf5461676c17.

All fourteen dependencies were fetched at the exact revisions in published kernel 3a4b's manifest, with an external path override. This restores an explicit historical tuple, not a latest-main integration. Contract 34bb and mathematics 3bd remain selected. Their source states are recorded in the final summary.

Mathlib's official cache restored 3,561 requested module artifacts successfully; selected dependency sources remained unchanged. Only cache-tool dependencies were compiled. No kernel, contract, or mathematics-owner module was compiled.

## External tooling drafts

artifact_hash.lean, runtime_state.py, artifact_consistency.py, focused_build.py, and protocol_focused_build.py were reconstructed from the prior tooling specification. These new copies have not been executed or syntax-validated. The lake.sh wrapper and scratch-diagnostic runner have not yet been restored. The scripts are drafts for review after work resumes, not verification evidence.

## Files to publish

files-to-preserve.json lists recovery text, receipts, logs, fixed original inputs, and bootstrap/tooling source with hashes. Reproducible dependency checkouts, binary archives, compiler binaries, downloaded cache, and extracted cache copies are excluded. Do not publish them as recovered source or acceptance evidence.
