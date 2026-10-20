# Undone work — priorities corrected 2026-10-20

Resume from the current committed source, preserving concurrent changes and the
shared Lean dependency setup. The controlling order is
[POC-first execution](specs/computational-core-plan.md#execution-priority-finish-the-poc-owner-correction-2026-10-20).
Do not resume the former encoder/reader latency optimization loop.

## Next: complete POC execution and functional gaps

1. **Run the complete unchanged computation-only inventory at a committed
   candidate.** Build the integration targets with `B0_INTEGRATION=1 just build`,
   then run the harness through the existing recipe. Update own-organisation
   requires to latest `main` before each build/harness run and record resolved
   inputs. Launch each required long run once with a durable log, source revision
   and identifiable process. Use this repository's `.venv/bin/python` for
   Sage/GAP execution from a temporary checkout. Obtain all per-assertion outcomes
   before selecting another optimization; a failing result is useful diagnosis,
   not a reason to omit that assertion or defer the inventory indefinitely.

   The recorded contextual encoder defect was repaired in `024bb72`; the 2×2
   encoding passes fell to milliseconds. The 3×3 reading completes under the
   ordinary heartbeat budget after the subsequent reader repairs. Its roughly
   102-second complete question benchmark is not an obstacle to starting the POC
   run. These two diagnostic identities are preserved; complete preservation
   and execution remain to be established. Issue #66's integrated obligations
   remain open, but proposed low-single-digit latency is not its next task.

2. **Repair actual functional blockers against the B0 table.** Complete missing
   generic composition, parameter/presentation transport, structured results and
   subsequent operations, application/admission, and contract handling as exposed
   by the complete run and required probes. Reuse existing implementations and
   focused evidence. Repair cost only if it prevents a required run from
   completing, then return to that run.

   The recorded selected-carrier matrix-unit evidence failure belongs upstream
   (lean-categories#92). Recheck whether the supplied latest-main input repairs it.
   If absent, keep its six inverse readings visible and continue independent
   work. The kernel worker neither changes nor commissions upstream mathematics.

3. **Demonstrate all 15 required registered computations.** The October 13 report
   had 12 frozen IDs holding, but only 11 with nonempty dispatch;
   `sets.eq.rev_rev` had zero dispatch. The three `lattices.discriminant.*`
   cases were gaps, with no applicable cokernel registration in the
   installed latest-main leaf inputs used by that report. Check current
   inputs and preserve the required registered-execution obligation.
   The orchestrator does not implement leaves or restore old dependency pins.

4. **Complete question preservation alongside functional repairs, then obtain
   independent extension trials and B0 acceptance.** Work through
   the remaining obligations in `specs/computational-core-plan.md`, including
   protected negatives, required arguments and independent extension trials.
   Use `custodian/SETUP.md` for authoritative deployment operations.
   Candidate output must not regenerate authoritative interpretations or
   acceptance records. Source integration and successful compilation do not
   constitute independent approval or B0 acceptance.

5. **Publish the final source and reconcile hosted checks with its exact SHA.**
   Inspect current local/remote revisions first, preserving the concurrent
   migration. Use normal publication gates; earlier hosted results are not
   results for this checkpoint. Publication of the current checkpoint was
   not verified during handoff.

## Historical process and workspace observations (2026-10-13; recheck before use)

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
