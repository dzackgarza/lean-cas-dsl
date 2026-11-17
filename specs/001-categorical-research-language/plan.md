# Implementation plan: categorical research language

**Work priority (owner correction, 2026-11-17):** follow the [fixed execution queue](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6726232237). Complete the fast inner development feedback loop (T016 / #84) before resuming feature work. Work only on the first unfinished task; parallel work must directly serve it. Advancement requires its complete existing criteria. Reordering or a repair transition requires a dated change to the queue and matching repository plan before implementation resumes. Final mathematical/runtime benchmarks remain after functionality, and every original completion and independent-author requirement remains in force. The queue and owning task entry record current status and evidence.

Feature context: `001-categorical-research-language`.

Read the [current consolidated implementation plan](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6664354269) against the [clarified specification](spec.md) and [permanent constitution](../../.specify/memory/constitution.md). The [authoritative handoff's fixed execution queue](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6726232237) governs the active implementation order. The identical dated queue below is its repository record; source-to-result requirements remain mandatory at their assigned task ranks.

| Artifact | Issue-owned design, assignment and evidence |
|---|---|
| `research.md` | [Current Phase 0 source investigation and architectural decision](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6708266418) |
| `data-model.md` | [Consolidated retained-context, selection and value model](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664275536) |
| `contracts/mathematical-input.md` | [Consolidated mathematical-input and generic interpretation contract](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664276482) |
| `contracts/computational-runtime.md` | [Consolidated computational execution contract](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6664277464) |
| `contracts/notebook-session.md` | [Consolidated notebook/session contract](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6664296914) |
| `quickstart.md` | [Current validation entrypoint and preserved command recipe](https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6708322175) |
| `tasks.md` | [Part 1: kernel functionality](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6684546229) and [Part 2: leaf delivery, proofs, assessment and performance, after functionality](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6684571141) |

The current consolidated bodies replace the older conflicting design and task wording. Earlier G1 discovery/coverage proposals are historical research, not additional operative selection requirements. The research record identifies the reusable structural algorithm and the rejected general gateway.

This file indexes the issue-owned work. The constitution, mathematical execution model,
feature scenarios and local contract requirements remain maintained repository requirements.
Implementation decisions, task state and validation remain in the owning issues; no production
acceptance follows from a planning review.

## Required model at implementation entry

Read [the mathematical execution model](../architecture.md), constitutional C23 and
[MM001–MM012](spec.md#mathematical-model-acceptance) before applying the issue-owned plan.
The local source, runtime, session and data-model contracts state the same preservation boundary.
Each implementation change must reach its original public mathematical continuation. Work state
and evidence remain issue-owned; this requirement supplement creates no new implementation lane.

The [development boundaries](../../AGENTS.md#development-boundaries) and
[focused commands](../../CONTRIBUTING.md#focused-development) apply to that same implementation.
They specify boundaries for source preparation, actual request binding, generic execution and final assembly;
they do not authorize preserving reconstruction machinery behind those interfaces.

## Committed execution order — owner correction of 2026-11-17

**Only rank 1, T016 / #84, is active. All later feature work is paused.** This is the fixed task execution order, not the order of issue groups. Each ID retains its complete existing definition, acceptance obligations, owner boundaries and checkbox in [Tasks Part 1](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6684546229) or [Tasks Part 2](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6684571141). The five historically checked tasks T001, T002, T003, T005 and T006 are not repeated below; T024/T025 remain retired. All 103 existing unfinished IDs occur exactly once.

Work proceeds only on the first unfinished task in this order. Parallel work must directly serve that task. Advancing requires its full existing completion criteria; this ordering does not mark any task complete. Reordering or entering a repair transition requires an explicit dated change to this queue and the matching repository plan before implementation resumes. A failed later check returns to the responsible existing task under that recorded correction, preserving the original required reruns and independent-author boundaries.

**Rank 1 completion:** make the actual inner source-edit → affected imports and executable dependencies rebuilt → same unchanged public check loop fast, and record comparable before/after timings on the same source/input/toolchain/host and public check, including the check outcome. T016 includes the requested single streaming focused build, separately requested profiling, probes rebuilding imports, explicit one-time SDK setup, production/test target separation, and justified dependency cuts. Commands, a cached no-edit check, a stale-import check or a reduced test do not establish completion. #85 and #90 may supply work only when it directly removes a measured dependency or setup cost from this active loop; #90 is not a second active task. The owner explicitly promotes this existing T016 correction ahead of its recorded T012 completion edge by using the already implemented baseline; T012 remains unfinished and its full definition is unchanged.

After T016, the order below is a stable dependency ordering of the existing authoritative task definitions: retain their recorded order where dependencies permit, honor every remaining `After` input and the complete Part 1 functionality condition F, then execute the existing independent delivery, proof, extension and acceptance obligations. Removing an already transferred reconstruction path remains part of its responsible functional task; the later T051/T064 entries do not authorize retaining a competing path. Final mathematical/runtime benchmarking T103 remains after actual functionality and the required delivered implementations.

1. **T016 — #84: measured fast inner feedback loop (ACTIVE).**
2. T007
3. T008
4. T009
5. T010
6. T011
7. T012
8. T030
9. T031
10. T053
11. T054
12. T055
13. T056
14. T017
15. T018
16. T021
17. T020
18. T026
19. T032
20. T033
21. T019
22. T027
23. T013
24. T042
25. T038
26. T034
27. T035
28. T036
29. T037
30. T050
31. T043
32. T044
33. T046
34. T048
35. T049
36. T057
37. T058
38. T059
39. T060
40. T061
41. T065
42. T066
43. T067
44. T068
45. T069
46. T073
47. T074
48. T075
49. T022
50. T023
51. T028
52. T083
53. T084
54. T085
55. T086
56. T087
57. T088
58. T089
59. T090
60. T091
61. T092
62. T093
63. T097
64. T098
65. T099
66. T100
67. T101
68. T051
69. T064
70. T104
71. T105
72. T004
73. T015
74. T029
75. T040
76. T041
77. T045
78. T047
79. T063
80. T071
81. T072
82. T077
83. T094
84. T095
85. T102
86. T014
87. T039
88. T052
89. T062
90. T070
91. T076
92. T096
93. T078
94. T079
95. T080
96. T081
97. T082
98. T103
99. T106
100. T107
101. T108
102. T109
103. T110

**Issue-group order is separate:** #84, #90, #85, #66, #69, #23, #86, #82, #24, #19, #3, #34, #68, #8, #13, followed by closed historical #11/#12. It groups related tracking records and does not grant permission to skip or parallelize task ranks. #24 retains complete original acceptance; no functional or benchmark requirement is lowered.
