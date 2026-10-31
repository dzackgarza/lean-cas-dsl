# PR 67 Language merge conflict: bounded source recommendation

## Recommendation

Retain the candidate's complete `toElement` numeral block and transplant the
upstream rigid-head mismatch guard into its existing named-family trial, scoped
to `k == 0`. Keep `familyLandsIn` and `zeroElement` outside that guard. The exact
proposed source change is saved in `pr67-language-proposed-resolution.patch`.

This combines the actual upstream change with the candidate's owner and ambiguity
repairs. Taking the upstream side of the whole conflict would discard those
repairs; taking the candidate side without the guard would discard the upstream
optimization. No unrelated optimization is proposed.

## Exact reviewed inputs

| Role | Commit | Language SHA-256 |
| --- | --- | --- |
| Merge base | `6e67b1e1dd118811c8cb443cc558221095e98573` | `43762768f9ed6f39a1239ad8c9c7d76385c84514175b30eebafcd3b7f4ba1364` |
| Fetched upstream main | `95de265e5a6d61909703a3193f0a1c952e12131f` | `2bf5fb20276bfd0fb9f24f884e8df76e8f962288676348e12122f3a094ea101b` |
| Published candidate | `8f454d6b56445eb3fb22c28aa281de973b9be4b7` | `8274994012a3cc93e0441c70df827aa1ac83c2095f52867a9dbce3c1fd9077ba` |
| Local equivalent | `5e948913e71cdcb1c2b5d3ba9a95d1d47f3c13ca` | `8274994012a3cc93e0441c70df827aa1ac83c2095f52867a9dbce3c1fd9077ba` |

The published and local candidates have the same complete tree:
`a6f6f3569c1b6386c9ee5a4a158ac2ed27dc2eb8`. `git merge-base` returns the base above.
The upstream range contains exactly one commit and changes only
`CasCatalogue/Language.lean`, with 17 additions and 5 deletions.

All source was read using immutable Git objects available from
`/tmp/kernel-record-consumer-20261026`. A read-only, three-argument
`git merge-tree <base> <candidate> <upstream>` inspection confirms exactly one
textual conflict, in the numeral portion of `toElement`. Its output is preserved
in `pr67-language-merge-conflict.txt`. This command did not create or apply a
merge, update a branch/index, or modify the worktree.

## Upstream behavior to preserve

Upstream `Language.lean:4643-4661` inspects the registered zero morphism family's
uninstantiated result type before attempting parameter reading:

1. Create the declaration constant with fresh universe metavariables and inspect
   its telescope.
2. If `homEnds?` exposes a target, reduce that target and the independently fixed
   object with transparency `.all`.
3. Skip the family trial exactly when the reduced family target is `.forallE`
   and the reduced object is `.const`.
4. For every other shape, including no recognized morphism endpoint, preserve
   the ordinary trial.

The optimization applies only to numeral zero and only to this named-family
trial. It does not bypass nullary operation selection and does not suppress the
following `familyLandsIn` fallback. It does not broaden `.const` to a constant
application or an arbitrary head name.

## Candidate behavior to preserve

The candidate's `toElement` at lines 7036-7128 contains the repaired owner paths
that overlap the upstream hunk:

- Existing elements are coerced to the independently selected carrier.
- A complete selected structure, or its actual registered structural action,
  supplies a numeral owner. Carrier equality does not manufacture missing
  structure.
- Competing inherited numeral constructions must agree as points, otherwise
  semantic ambiguity is raised.
- Contextual and registered named numeral searches retain their full owners.
- The numeric token can name a registered nullary operation for every `k`, with
  the existing terminal-source and complete-application checks.
- Both named-family calls retain `parameters` and
  `callableAddress := some point.id.raw`.
- Anonymous admission, original-domain proof checking/restaging, constants, and
  registered inclusions remain in their existing order.

`parameterCompatible` at lines 972-976 discards only declared invalidity;
ambiguity and interpreter failures survive. `applyOperation` at lines 7870-7943
retains the selected complete receiver, complete application candidates, checked
operation comparisons, and ambiguity when the candidates are not connected by
accepted comparisons. None of these paths is replaced by the proposal.

## Precise integration

Within the candidate's existing
`state.morphisms.find? (name == pointName && category == category.id)` branch,
immediately after extracting the named object's retained `parameters`:

- For `k == 0`, perform the exact upstream target/object head inspection using
  `point.declaration` instead of the old local name `zero.declaration`.
- Run that inspection within the candidate's existing `parameterTrial` helper.
  This retains only the Boolean result and discards speculative elaborator
  state. It adds no catch that could swallow ambiguity or interpreter errors.
- For nonzero `k`, use `false` directly and perform no new family inspection.
- Wrap the existing profiled family trial and its successful application in
  `unless rigidMismatch`.
- Leave `familyLandsIn point.declaration X` at the original outer indentation.

The candidate's `semanticObject` at lines 874-877 simply returns the retained
object handle. The guard therefore consults the exact already selected object;
it does not choose a different owner, infer an actual object from JSON, or
substitute a carrier for a complete structure.

The proposal changes only this contiguous family-trial block. The candidate's
425,722-byte prefix and 133,684-byte suffix are identical by construction.
No source outside `CasCatalogue/Language.lean` is included in the proposed patch.

## Existing generic guard is not an exact substitute

The candidate already calls `incompatibleTypeShapes` at the beginning of
`applyFamily` (lines 4855-4862), before reading supplied parameters. That helper
is isolated and deliberately conservative: after reduction it recognizes rigid
inductive and primitive quotient type heads, and leaves unresolved projections
or eliminators inconclusive.

It overlaps the upstream optimization on common Pi-versus-inductive cases, but
it is not identical. Main's `.const` case includes a bare constant whose
declaration is not an inductive or quotient type; the candidate helper may
return false for such a head. Moreover, main skips the outer family trial itself.
Therefore "already covered" is not a sufficient reason to drop the actual
upstream change. Keep the existing generic helper unchanged and preserve the
upstream check at its corresponding zero-family boundary.

## Proposal hashes and verification limits

- Proposed resolution patch SHA-256:
  `7e8c7b4ed22a976769d6c1777d66142dc6411310f03f3f4c3ba9df9d92db58e9`.
- SHA-256 of the complete Language source that would result from this proposal:
  `b6abf9666adb41d4409f8a5647cddfbe3aa8b48c181ea080a88aab7de84ec250`.
- Preserved upstream-only patch SHA-256:
  `3a2ff705bbe7f28cd0ac00ce9c509269f3f0c27f820c302d2152ac8eaaaeb131`.
- Preserved merge-conflict inspection SHA-256:
  `d52ba5f383c5be905bea8971c22fa828c2c3787d64f271e3e852075c76e2e355`.

The proposed source exists only as a review patch computed from the immutable
candidate. It has not been installed, committed, compiled, tested, published,
or applied to any native/canonical/candidate worktree. No compiled artifacts,
gate imports, assertions, review authority, acceptance authority, or trusted
configuration were changed. Root owns any concrete merge and its subsequent
validation. This is an independent engineering source recommendation, not a
completed merge or authoritative acceptance result.
