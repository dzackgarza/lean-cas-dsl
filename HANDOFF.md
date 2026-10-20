# B0 handoff — stopped by owner, 2026-10-20

B0 remains unfinished. The owner stopped this run because usage was being consumed without a completed, discernible end-to-end result. The goal is paused. Resume only on a new owner instruction.

## Start here

The construction source is on `b0/poc-independent-role-integration` at
`4bc36b61e15ac2bd0abab2a48317d1423ee1b0fe` before this documentation checkpoint.
Use `/home/dzack/gitclones/lean-cas-dsl-functional-repair` for its existing compiled cache;
`/home/dzack/gitclones/lean-cas-dsl-poc-independent` holds the integration branch.
Both have the same construction code. Compare revisions before editing.

The original `/home/dzack/gitclones/lean-cas-dsl` checkout contains unrelated,
uncommitted `CasCatalogue/Language.lean` changes. Preserve them. Their saved patch
still matched `/tmp/b0-poc-32c3897/original-language-restored.patch` before stopping.
Do not merge the construction branch over that dirty file. The last verified published
kernel main was `8be6fe8db2b46b0882de7de444b701390c7fe22e`; recheck the live remote.

## First unfinished obligation: obtain the complete actual inventory

The computation-only native run at `4bc36b6` was terminated on the owner's stop
instruction (exit 143). **It produced no complete per-assertion report.**
`/tmp/b0-poc-4bc36b6/harness.json` is empty. Do not count this run as acceptance,
question preservation, or evidence that all 153 admitted identities read.

The process has stopped; PIDs 532337 and 541776 were terminated. All delegated agents
are finished. Interruption status is `/tmp/b0-poc-4bc36b6/interruption.json`.
Other restart artifacts in that directory:

- `source-inputs-before-native.json`: exact source/dependency revisions and hashes.
- `loaded-artifact-hashes-before-native.json`: executable and imported artifact hashes.
- `harness-build.log`: completed native harness build.
- `harness.log`: interrupted run log, not a completed outcome inventory.

Resolved inputs for that attempt were mathematics `805208138f016368f6a4eac415f25f3922a5807d`,
contract `c6e78eb2e5939e58b6f18b5fc456320c65f10186`, leaves
`0cfb83ac60f896d65c5ca3cfc7d38a07b1d7ec73`. Contract and leaf source were published;
the construction kernel branch was not published during this stop.

After explicit resumption, refresh latest-main dependencies and rebuild the actual harness
if required. Run the complete unchanged admitted inventory, preserving every failure and
unreadable assertion. Use a new report filename:

```bash
just track-main
lake build cas-harness
CAS_SAGE_PYTHON=/home/dzack/.local/bin/sage-docker-python \
CAS_GAP_PYTHON=/home/dzack/gitclones/lean-cas-dsl/.venv/bin/python \
lake exe cas-harness --computation-only \
  --report /tmp/b0-poc-4bc36b6/restarted-harness.json \
  > /tmp/b0-poc-4bc36b6/restarted-harness.log 2>&1
```

Record actual inputs before and after execution. Keep source, dependencies and compiled
artifacts fixed during the run. The ordinary harness invocation permits proof discharge;
`--computation-only` is required here. Verify all admitted IDs, complete questions and
propositions, and the frozen 15 required computations' actual dispatches before selecting
further repairs. Do not replace that result with another profiling project.

## Remaining required validation and functionality

1. Run the unchanged independently authored `tests/acceptance/b0-required-positives.cas.proposed`
   through production `#cas_tests ... computing`, retaining all original bindings. Use a fresh
   scratch wrapper/report rather than overwriting previous evidence. The latest F9 coefficient-map
   registrations have not been tested by central assertions. The last five-case diagnostic predates
   them: product held; four F9 cases failed. That is not a result for the latest leaf revision.
2. Re-run the complete source gate and same-candidate protected negatives. The latest dependent
   Realize build passed (`/tmp/lean-cas-focus.UsL2u7.log`, 455.58 seconds), and the native harness
   built; neither discharges acceptance. The last complete source gate, at `3e0f982`, failed
   FunctorActionDataProbes, StructuredReconstructionProbes, BinderReaderProbes and LiftProbes.
   Receiver binding and binder-probe scope corrections are in the current source, but their full
   dependent source gates were not all rerun. Keep every required check.
3. Preserve complete question meaning independently across **every admitted identity**, including
   proof proposition types, binders, parameters, selected structures, maps and routes. Existing
   reports under `tests/acceptance/interpretation-comparison-5410e70*.md` are bounded assessments,
   not authoritative migrations or a completed assessment of the interrupted run. Extract opaque
   questions without runtime outcomes for the acceptance author. Never regenerate authoritative
   expectations from candidate output.
4. Address the two compositional boundaries below. Then freeze the candidate and complete the
   independently chosen extension trials and arguments in the governing plan. No complete set of
   frozen trials or independent B0 acceptance exists.
5. Publish the actual final source through the authorized path and reconcile exact-SHA hosted
   checks. Earlier main/CI outcomes do not apply to this construction candidate. Protected evaluator
   activation and independent acceptance remain separate operations (`custodian/SETUP.md`).

## Unfinished compositional boundaries

**Route enumeration:** all seven kernel consumers use public `SemanticState.routes` with its
ordinary fuel 32. The source review establishes only bounded simple-route enumeration, not a
complete extension argument. A possible kernel correction is to derive a finite reachable-vertex
enclosure from actual public `edgesFrom`, verify closure, and use its vertex count as a sufficient
simple-path bound. At this tuple, active unary constructors are Arrow/Core and inspected edges do
not grow their outer spine; inert Subobjects tails do not recursively lift edges. This is a
read-only proposal, not implemented or verified. Do not substitute a larger arbitrary constant,
assume future non-growth, or claim it proves equivalence of cyclic walks.

**Constructed coherence:** `LiftProbes` still rejects the direct formed-module forgetful route
versus the fixed-value/carrier route under Arrow. The consumed constructor interface has action
on functors but no general action on cells, and `comparisonsFrom` matches exact route segments.
Record/consume the missing accepted formal input without inventing mathematics in the kernel,
weakening the positive, or commissioning upstream work from this downstream failure.

`CellSyntax` separately instantiates registered cells and their actual components. Ordinary method
execution computes its selected route. Dropped comparison IDs alone do not prove a wrong-data
transport bug; the required alternate-route/nonidentity computational transport argument is still
unestablished. Preserve that distinction.

The unchanged completion contract is `INTENT.md`, `specs/architecture.md` and the B0 table in
`specs/computational-core-plan.md`: required registered computations and positives, all admitted
questions readable, full question preservation, protected negatives, independent trials/arguments,
independent acceptance and exact-revision publication. No overall completion percentage was
established.
