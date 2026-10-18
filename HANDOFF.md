# Undone work — 2026-10-13

Resume from source checkpoint `49f5944fb0f187be492b519d5c773c93099cc2a8`.
The owner requested a checkpoint and handoff; implementation is stopped.
The working tree was clean before this report. Preserve the concurrent central
Lean dependency migration in that revision; the owner explicitly approved
coordination with it.

## Next source repairs

1. **Repair question-identity construction for expanded contextual terms.**
   The anonymous prime-factor and matrix-kernel readings are repaired at
   `6a962cf` through the existing formal admissions, retained constructor
   parameters and exact zero family. The unchanged claims now read.

   The matrix trace exposes a separate production blocker: 99 roots cause
   2,097,785 recursive encoder calls before collapsing to 640 canonical nodes.
   `custodian/FINDINGS.md` and `JOURNAL.md` record separated timings and two
   falsified repair routes. The canonical DAG remapper removes the independent
   root-key traversal and preserves the legacy byte format, but exact
   production interpretation still takes 149.890 seconds: source-root and
   operation-field encoding each cost about 65 seconds. Pre-encoding fields
   did not unify those raw expressions and was reverted. Preserve the complete
   identity and its proof and binder quotient. Do not replace it with a digest,
   timeout increase or weaker trace. Owning work unit: lean-cas-dsl#66.

2. **Obtain the formal repair for selected-carrier matrix-unit evidence.**
   Diagnosis completed 2026-10-18: `Units.invertibleEvidence` succeeds for the
   matrix over literal `ℚ`, but fails for the definitionally equal selected
   rational-ring carrier. `Units.evaluateNumerals` does not suffice; a valid
   `change` to the underlying `ℚ` matrix makes the unchanged evidence succeed.
   The formal evidence tactic must normalize the selected-object construction
   before selecting its field/unit route. This is an upstream implementation
   defect, not missing mathematics or a kernel admission to reformulate. The
   earlier full report's six inverse failures remain blocked on
   lean-categories#92.

## Required validation and acceptance

3. **Run the complete computation-only acceptance inventory at the final
   repaired source.** Commit repairs first. Update own-organisation requires
   to latest `main` before each build/harness run and record the resolved
   inputs. Launch each required long run once with a durable log, source
   revision and identifiable process. Use
   `/home/dzack/gitclones/lean-cas-dsl/.venv/bin/python` explicitly for Sage/GAP
   execution from a temporary checkout.

   No full acceptance harness has run at `608c607` or the current checkpoint.
   `.tmp/b0-completion-20261013/harness-9370ee5.json` is a diagnostic baseline,
   not acceptance of the current source.

4. **Demonstrate all 15 required registered computations.** The prior report
   has 12 frozen IDs holding, but only 11 with nonempty dispatch;
   `sets.eq.rev_rev` has zero dispatch. The three `lattices.discriminant.*`
   cases remain gaps, with no applicable cokernel registration in the
   installed latest-main leaf inputs used by that report. Check current
   inputs and preserve the required registered-execution obligation.
   The orchestrator does not implement leaves or restore old dependency pins.

5. **Obtain independent question-preservation and B0 acceptance.** Work through
   the remaining obligations in `specs/computational-core-plan.md`, including
   protected negatives, required arguments and independent extension trials.
   Use `custodian/SETUP.md` for authoritative deployment operations.
   Candidate output must not regenerate authoritative interpretations or
   acceptance records. Source integration and successful compilation do not
   constitute independent approval or B0 acceptance.

6. **Publish the final source and reconcile hosted checks with its exact SHA.**
   Inspect current local/remote revisions first, preserving the concurrent
   migration. Use normal publication gates; earlier hosted results are not
   results for this checkpoint. Publication of the current checkpoint was
   not verified during handoff.

## Process and workspace state needed to resume

- No CAS build, acceptance harness or diagnostic from this stream remains
  live at handoff. A separate Lake build was observed as PID `2728436`, with
  cwd `/home/dzack/research/computations/experiments/lean_category_dsl_spike`;
  recheck its existence and ownership before touching shared dependencies.
- The existing full-build record for `608c607` is
  `.tmp/b0-completion-20261013/build-608c607.log`, with exit record `0`,
  `build-608c607-inputs.json` and `build-608c607-process.json`.
  This record prevents mistaking an absent process for an interrupted run;
  it does not validate later source or discharge acceptance.
- `/tmp/lean-cas-dsl-final-608c607` is detached at `608c607`. Its
  `.lake/packages` points to `/home/dzack/.local/share/lean/v4.33.0/packages`
  and `.lake/build` points to this checkout's build directory. Coordinate
  shared-cache builds; do not recursively delete through these links.
- `.tmp` contains diagnostic source, worktrees and recoverable compressed
  harness binaries. Inventory ownership and remaining consumers before
  cleanup. Do not treat the subtree as disposable because of its size.
- The management connector returned `WORKSTREAM_PAUSED`; no usable
  coordination token was obtained. Resume through its normal authorized
  route rather than bypassing that state.

The governing boundaries remain `INTENT.md` and `specs/architecture.md`:
kernel/controller work here; independently authored mathematics upstream;
permanent acceptance assertions owned by the acceptance role; opaque leaves
owned by the leaf role. The full approved B0 task remains unfinished.
