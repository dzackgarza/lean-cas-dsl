# Implementation plan: categorical research language

Feature context: `001-categorical-research-language`.

Read the current issue-owned design in this order:

1. [Base implementation plan and artifact index](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6664354269).
2. [First-use and extension-scope amendment](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6684992506).
3. [Runtime amendment: suspension captures and staged/committed completion](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6684996781).
4. [Task amendment: predecessors, early trial, repair and evidence reentry](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6685591815).
5. [G1 replacement: exact extension-closed route representation and source-directed agreement](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6693871042).
6. [G1 comparison discovery: permitted evidence syntax, fair search, exact checking and extension-uniform positive completeness](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6697729346).
7. [Completed whole-family coverage and nonvacuous selection design, proofs, integrated reference and task refinements](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6705288299).

Items 5–7 replace the snapshot-specific closure and complete the named comparison/coverage/task algorithm descriptions. Item 4's task IDs, predecessor graph and repair transitions remain unchanged. Unmentioned requirements remain binding.

Read the [counterexample and its precise hypotheses](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6693321613) and the [architectural alternatives](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6693443847) with the replacement. The adopted design is exact reading representation with source-directed evidence and selection, not a silently restricted projection calculus or a universal-total semantic quotient. A selected member and complete checked coverage are distinct prerequisites; neither a pairwise proof nor vacuous coverage authorizes implicit execution.

The executable references and tests are `scripts/probes/structural_routes_reference.py`, `scripts/probes/test_structural_routes_reference.py`, `scripts/probes/agreement_search_reference.py`, `scripts/probes/test_agreement_search_reference.py`, `scripts/probes/coverage_reference.py`, and `scripts/probes/test_coverage_reference.py`. They are kernel-internal engineering references, not the production Lean adapter, a released leaf proof API, or independent mathematical acceptance.

## Artifact index

| Artifact | Canonical issue-owned content |
|---|---|
| `research.md` | [Base research](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6664331639), with the G1 sources, alternatives, route, discovery and coverage arguments above |
| `data-model.md` | [Base model](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664275536), with the runtime amendment above |
| `contracts/mathematical-input.md` | [Base mathematical-input contract](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664276482), with the interpretation amendment and G1 records above |
| `contracts/computational-runtime.md` | [Base runtime contract](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6664277464), with the runtime amendment above |
| `contracts/notebook-session.md` | [Base notebook contract](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6664296914), with the runtime amendment above |
| `quickstart.md` | [Base validation guide](https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6664297919), with the amended task/reentry order above |
| `tasks.md` | [T001–T064](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6684546229), [T065–T110](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6684571141), task amendment 1, route §6, discovery §8 and coverage §6 above |

The constitution, independently fixed scope, required positive outcomes, comparisons, budgets and author boundaries are unchanged. An unresolved interpretation cannot pass a required positive. Positive-evidence completeness must not be reported as universal-total agreement completeness. Implementation and independent acceptance remain distinct from completed design/remediation. This file is a navigation pointer, not a competing work order.
