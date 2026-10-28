# Kernel V1: current handoff

Continue through [PR #67](https://github.com/dzackgarza/lean-cas-dsl/pull/67) on
`work/kernel-v1-20261023`. [Issue #10](https://github.com/dzackgarza/lean-cas-dsl/issues/10)
and the [current delivery sequence](specs/computational-core-plan.md#current-delivery-sequence-2026-10-29)
own the work order. #66 owns complete mathematical interpretation; #69 owns computation and subsequent mathematical use;
#24 owns integration and independent acceptance. #23/#82 review construction requirements
and exact mathematical inputs alongside that work.

## Source and actual input dependency — 2026-10-28 UTC

The audit inspected candidate `4c33b5747f539dd2ca8ba169bcded6868c52812f`. Its manifest selects
`lean-categories` `3bd4d3d9695f288749c860368174462c4d689b7c` and contract
`34bb8abbdbb49699015f63840cf86ed67f438003`. Upstream mathematical main was
`8782c22ba613a022a84a1e910b6489cc2503e29a`. The candidate consumes constructor-comparison
interfaces from pending [upstream #93](https://github.com/dzackgarza/lean-categories/pull/93)
and [#94](https://github.com/dzackgarza/lean-categories/pull/94), not yet present on that main.
Reconcile and independently assess the existing source through its own authority before
claiming latest-main integration. This is an actual input dependency, not a request to
reinvent the mathematics or a new permanent pin policy; unrelated work can continue.

The first RX-LIFT slice itself also uses #94's `DegeneratePlaneLifts` and
`DegeneratePlaneFactorization` declarations and their import closure, identified in #69.
Verify those exact inputs through the existing independent authority and input policy;
this does not require every unrelated deliverable in the pending upstream PRs.

The latest candidate-workflow result inspected,
[run 40652257963](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40652257963) at
`60829a1f7db040f6a8ae394777c0a10bc00d3946`, failed the combined consumer build.
Later documentation commits do not supply a fresh build or mathematical acceptance result.
Gates and the candidate workflow have different branch filters and evidence artifacts;
the [check instructions](specs/computational-core-plan.md#running-checks) describe them.

## Next work — 2026-10-29

1. Fix the existing first-stage RX-LIFT construction's complete meaning and exact accepted
   inputs (#66 with #23/#82). Keep its independently fixed question, prerequisite bindings,
   imports and budgets; this does not require all 153/134 readings before replacement.
2. Work #66/#69 together: build the actual production dependencies, compute the construction
   and required nonidentity comparison, and use its supplied inclusion/factor in the next
   mathematical question. Reuse adequate machinery and remove the paths superseded for that use.
3. Before extending coverage, establish preservation for the operations actually used and
   public-only unchanged-consumer use (#69/#24). Exercise the successive-lift/source-comparison
   controls when extending to that composition; one first result is not proof of all mechanisms.
4. Complete the remaining readings, constructions and observations through the surviving
   implementation, then establish the full combined build, public API, notebook and #24's
   unchanged independent acceptance and frozen extension trials.

Repair only the retained dependencies or minimal temporary blockers needed to run the first
production computation. Do not restore all legacy consumers, optimize the old interner or
retrofit every old result record before the replacement. Preserve required validation and
hostile controls at its boundary; adapt engineering fixtures that call removed private helpers.
Actual supplied maps, endpoints, owners, lazy/fused execution and distinct failure meanings
remain required. Full acceptance is a delivery condition, not a prerequisite to refactoring.

Stop expansion if the next operation still needs missing construction data, invented
identity associations or another context/ownership recovery path. The first two working
days test the construction and its later use; the 1–2 weeks are an allocation, not a delivery
forecast established by the stalled history.

## Selected implementation sources

The implementation route is fixed in [cc-realize-2cat](specs/reuse/cc-realize-2cat.md):
adapt PolyFun's specified suspension/return transitions into the existing checked
selected-plan/`InvocationExecution` owner, keep its plan builders, validators, lift fold and
dispatcher, and remove the migrated path's recursive/recovery/completion alternatives.
Use [Lean's named public application/binder APIs](specs/reuse/cc-dsl-language.md) for #66;
ordinary execution skips unused audit export while retaining preparation checks.
#24 reuses the independently authored `diagnostics/extensions-20261024` package's rational
lift/factor implementation through the current contract. Do not replace it with the simpler
finite-graph backend or rewrite its algorithms. The exact upstream declarations still need
their independent acceptance and permitted availability; source choice does not supply those.
No new external evaluator or Hex foundation dependency is required to finish this assignment.

The contract integration work is also concrete: #24 records existing lift/map helpers on
contract source `34bb8abb` that are absent from inspected contract main `3382e4e0`, and the
independent leaf adapter must consume the public actual-image metadata. Reconcile and publish
that existing contract work through its owner; adapt the public leaf boundary without
rewriting rational algorithms or restoring recipe recovery. Complete that conformance before
freezing the unchanged-target trial. Source selection does not establish runtime compatibility.

## Preserved history and retired tracking

The [integration handoff](https://github.com/dzackgarza/lean-cas-dsl/blob/work/kernel-v1-20261023/HANDOFF.md)
retains the owner assignment, complete scope and dated source/execution records. Its old session
checkpoints are provenance, not current pass results. Superseded PRs #63/#64 preserve their
branches; their behaviors continue in #66/#69/#24. PR #70 remains a separate trusted-base
input-retrieval repair. Research #71–#81 are consolidated records; closure is not runtime success.

The [historical B0 handoff](https://github.com/dzackgarza/lean-cas-dsl/blob/e15540381dedb93b17ce3d534170beb2d375f62d/HANDOFF.md)
is preserved at its original revision. Its local-only branch, old K queue and owner-action
command are not current continuation instructions. Preserve existing user work; do not recreate
that historical branch. Main's implementation is not made equivalent to the integration candidate
by this documentation.
