# Implementation plan: categorical research language

Feature context: `001-categorical-research-language`.

Read the current issue-owned design in this order:

1. [Base implementation plan and artifact index](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6664354269).
2. [First-use and extension-scope amendment](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6684992506).
3. [Runtime amendment: suspension captures and staged/committed completion](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6684996781).
4. [Task amendment: predecessors, early trial, repair and evidence reentry](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6685591815).
5. [G1 replacement: exact extension-closed route representation and source-directed agreement](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6693871042).

Item 5 replaces the snapshot-specific structural-closure algorithm and the named task algorithm descriptions. Item 4's task IDs, predecessor graph and repair transitions remain unchanged. Unmentioned requirements remain binding.

Read the [counterexample and its precise hypotheses](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6693321613) and the [architectural alternatives](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6693443847) with the replacement. Exact structural closure, checking supplied whole-family agreement, and universally deciding agreement of all routes are different obligations. The replacement supplies the first algorithm and specifies the evidence-directed interface; it does not supply the rejected universal semantic classifier or establish full agreement coverage merely by generating a route grammar.

The executable reference and its tests are `scripts/probes/structural_routes_reference.py` and `scripts/probes/test_structural_routes_reference.py`. They are engineering references, not the production Lean adapter, a released leaf API, or independent mathematical acceptance.

## Artifact index

| Artifact | Canonical issue-owned content |
|---|---|
| `research.md` | [Base research](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6664331639), with the G1 sources, alternatives and replacement above |
| `data-model.md` | [Base model](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664275536), with the runtime amendment above |
| `contracts/mathematical-input.md` | [Base mathematical-input contract](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664276482), with the interpretation amendment and G1 replacement above |
| `contracts/computational-runtime.md` | [Base runtime contract](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6664277464), with the runtime amendment above |
| `contracts/notebook-session.md` | [Base notebook contract](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6664296914), with the runtime amendment above |
| `quickstart.md` | [Base validation guide](https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6664297919), with the amended task/reentry order above |
| `tasks.md` | [T001–T064](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6684546229), [T065–T110](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6684571141), task amendment 1, and replacement §6 above |

The constitution, independently fixed scope, required positive outcomes, comparisons, budgets and author boundaries are unchanged. An unresolved interpretation cannot pass a required positive. The earlier Phase 1 disposition and the reference tests are not a full implementation-readiness or acceptance verdict. This file is a navigation pointer, not a competing work order.
