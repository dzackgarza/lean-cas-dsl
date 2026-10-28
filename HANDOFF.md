# Kernel V1: current handoff

Continue through [PR #67](https://github.com/dzackgarza/lean-cas-dsl/pull/67) on
`work/kernel-v1-20261023`. [Issue #10](https://github.com/dzackgarza/lean-cas-dsl/issues/10)
and the [current delivery sequence](specs/computational-core-plan.md#current-delivery-sequence-2026-10-28)
own the work order. #66 owns reading/export; #69 owns retained result execution and reuse;
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

The latest candidate-workflow result inspected,
[run 40652257963](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40652257963) at
`60829a1f7db040f6a8ae394777c0a10bc00d3946`, failed the combined consumer build.
Later documentation commits do not supply a fresh build or mathematical acceptance result.
Gates and the candidate workflow have different branch filters and evidence artifacts;
the [check instructions](specs/computational-core-plan.md#running-checks) describe them.

## Next work

1. Reconcile inputs and recover the compiling combination with a measured focused edit/check loop.
2. Run the coupled #66/#69 trial: the same prepared question, complete selected dependent
   interpretation, and actual retained structured-result/nonidentity-comparison/defining-map reuse.
3. Before broad migration, establish transition preservation and public-only source use feeding
   an unchanged target consumer. Delete the replaced execution/recovery path.
4. Complete supported families and all unchanged #24 delivery/frozen-acceptance conditions.

Stop expansion if the chain still needs another context/identity recovery mechanism.
The first two working days test this replacement; the 1–2 weeks are an allocation, not
a delivery forecast established by the stalled history.

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
