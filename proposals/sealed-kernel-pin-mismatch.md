# Proposal: the sealed kernel does not compile against the sealed pin

Raised by the orchestrator, 2026-09-30, under `custodian/CONTAINMENT.md` step 3. This branch fails
verification by construction. It changes nothing. It names an obligation that is inconsistent
under the sealed boundary.

## The inconsistency

- The seal fixes lean-cas-dsl at `0ba53dab`. That revision includes the orchestrator's kernel
  commit `1fbcd5c`, which was committed with validation pending. It reads the admission's
  registered evidence: `CasCatalogue/Language.lean:2048`, `let some evidence := entry.evidence`.
- The seal fixes `lean_categories` at `c06aeedc`. At that revision `ObjectEntry` has no field
  `evidence`. It was added in `lean-categories` `646f4a7`, an orchestrator commit to the registry
  schema. Checked with `git show <rev>:LeanCategories/Catalogue/Registry/Entry.lean`: 0 matches at
  `c06aeedc`, 1 at `646f4a7`.
- So `CasCatalogue.Language` cannot elaborate at the sealed state, and neither can anything
  downstream of it: `CasGates`, `CasAcceptance`, `CasDsl`. No Lean build was run to confirm this.
  The claim rests on the two source reads above.

The cause is the orchestrator's: it banked kernel code that needed an unpinned upstream change.

## Resolutions (each changes the boundary; the orchestrator adopts none)

1. Re-pin `lean_categories` to `646f4a7`: the evidence schema, with no evidence rows. The
   commits after it (`011d0be`…`01b2f89`, membership evidence) are quarantined
   (`gov-quarantine-evidence`) and are excluded. Under this pin every admission has no evidence,
   so every admission is refused, and the statements that need one become invalid rather than
   established by kernel tactics. `646f4a7` is itself orchestrator-authored registry code: it
   needs a judgment by someone other than the orchestrator.
2. Revert the kernel part of `1fbcd5c` (`establish` running registered evidence, and the removal of
   the tactic battery). That restores a kernel that proves domain membership itself, which the
   owner has ruled out ("Teaching the kernel about math should BE IMPOSSIBLE").
3. Keep the sealed state and record that it does not build, until an accepted re-pin exists.

The orchestrator's reading is that only 1 is consistent with the owner's text. Whether 1 is
accepted is not the orchestrator's decision.
