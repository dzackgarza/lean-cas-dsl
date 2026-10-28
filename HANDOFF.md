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

The latest candidate-workflow result inspected,
[run 40652257963](https://github.com/dzackgarza/lean-cas-dsl/actions/runs/40652257963) at
`60829a1f7db040f6a8ae394777c0a10bc00d3946`, failed the combined consumer build.
Later documentation commits do not supply a fresh build or mathematical acceptance result.
Gates and the candidate workflow have different branch filters and evidence artifacts;
the [check instructions](specs/computational-core-plan.md#running-checks) describe them.

## Next work — 2026-10-29

1. Interpret the existing difficult composite with its full parameters, selected structures,
   domain hypotheses, diagram and independently fixed relation (#66).
2. Compute its structured construction and required nonidentity comparison, then use the
   supplied defining morphism in the next mathematical question (#69).
3. Before extending coverage, establish preservation under the claimed substitutions,
   compositions, comparisons and prescribed lifts/reindexing. Include a public-only source
   contributor whose result the unchanged target consumer can use (#69/#24).
4. Complete those obligations across all promised V1 constructions, then establish #24's
   unchanged full independent observations and frozen extension trials.

Reconcile the actual inputs, recover a compiling combination and measure a focused edit/check
loop as supporting prerequisites. Remove the replaced recovery/completion paths. Preserve
actual supplied maps, endpoints, owners, lazy/fused execution and distinct failure meanings.
An implementation state or a number of migrated consumers is not the mathematical result.

Stop expansion if the next operation still needs missing construction data, invented
identity associations or another context/ownership recovery path. The first two working
days test the construction and its later use; the 1–2 weeks are an allocation, not a delivery
forecast established by the stalled history.

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
