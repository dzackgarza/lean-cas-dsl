# Specification Quality Checklist: Categorical Mathematical Research Language

**Purpose**: Validate specification quality and completeness before `speckit-plan`.

**Created**: 2026-11-05 (Asia/Taipei). **Revalidated**: 2026-11-25 (Asia/Taipei), against the specification of the same commit as this file: 16 user stories, FR-001 to FR-142, SC-001 to SC-029 and MM001 to MM012.

**Feature**: [Feature specification](../spec.md).

A checked item records review of the **specification**, not conformance of the implementation, mathematical formalization, completion of independent trials or delivery of V1 or full B0. The reviews of 2026-11-05 and 2026-11-07 covered FR-001 to FR-040 and SC-001 to SC-012 at their recorded revisions; git history keeps their records. The reviewer-owned `checklists/architecture.md` has its own markers and is not approved by this checklist.

## Content Quality

- [x] CQ-01 No implementation details (languages, frameworks, APIs).
- [x] CQ-02 Focused on user value and stakeholder needs.
- [x] CQ-03 Written for the intended non-implementation stakeholders.
- [x] CQ-04 All mandatory sections completed.

## Requirement Completeness

- [x] RC-01 No unresolved clarification markers remain.
- [x] RC-02 Requirements are testable and unambiguous.
- [x] RC-03 Success criteria are measurable.
- [x] RC-04 Success criteria are technology-agnostic.
- [x] RC-05 All acceptance scenarios are defined.
- [x] RC-06 Edge cases are identified.
- [x] RC-07 Scope is clearly bounded.
- [x] RC-08 Dependencies and assumptions are identified.

## Feature Readiness

- [x] FRQ-01 All functional requirements have clear acceptance criteria.
- [x] FRQ-02 User scenarios cover primary user flows.
- [x] FRQ-03 The specified feature covers the measurable outcomes defined in Success Criteria.
- [x] FRQ-04 No implementation details leak into the specification.

## How the criteria apply to this project

- Mathematical researchers and independent mathematical and computational contributors are the intended stakeholders. Precise categorical mathematics is domain content, not an implementation choice.
- Naming `lean-categories` as the independent mathematical authority, the no-proof leaf boundary, the notebook surface and the fixed acceptance IDs preserves explicit project requirements. It selects no runtime language, framework, internal API, representation, transport or architecture.
- Paths, commands and tools that an owning issue fixes as a product contract are requirements of that issue: the Sage inventory observer and its parsers (#20), the Python client (#68), the trace classes (#8), the interpreter path and kernelspec of the advertised installation (#34), and the spellings and commands of the spike rows. Leaves-spec rows, task numbers and milestones belong to the plan and the task list.
- The feature-readiness outcome item is assessed as coverage and evaluability of the specified outcomes, not as a claim that unimplemented software has passed them.
- Scope is the complete product with its delivery assignments: V1 (#24), full B0 and the classified Sage coverage (#19 to #23), and the research and client work of M5. Scenarios refer to independent source questions and create no replacement oracle.

## Evidence of the revalidation of 2026-11-25

| Item | Evidence |
| --- | --- |
| CQ-01, FRQ-04 | The requirements state mathematical meaning, user behaviour, authority boundaries and the acceptance constraints of the owning issues. FR-042 states the computational milestones and points to the plan for the rules of order and of statement ownership; FR-100 names the groups implementation without its leaves-spec rows and tasks. |
| CQ-02 | Sixteen stories cover connected calculation, complete constructions, selected and higher structure, exact and infinite work, both growth directions, independent computation, the notebook, discovery, development feedback, category implementations, full B0 and the Sage coverage, the Python client, installation, unit groups, diagnostics and the research harvest. |
| CQ-03 | Domain terms are defined by the context, the key entities and the cited mathematical sources; no knowledge of internal modules is needed to read a story. |
| CQ-04 | Clarifications, prioritized stories with independent tests and Given/When/Then scenarios, edge cases, functional requirements, key entities, success criteria, quantifiers, traceability, assumptions and the mathematical-model scenarios are present. |
| RC-01 | The specification holds no `[NEEDS CLARIFICATION]` marker or template placeholder. The owner answers of 2026-11-07, 2026-11-15, 2026-11-22 and 2026-11-25 are integrated in the stories and requirements. |
| RC-02 | Each requirement has a unique ID and an observable outcome. This revalidation corrected US10 scenario 4 and FR-014, which read as a ban on any algorithm that no engine exposes, to the established-implementations policy of constitution 4.0.1, and added FR-141 and FR-142 for the spike rows G17 and G32. |
| RC-03 | The success criteria preserve exact inventories, zero-dispatch and zero-accommodation outcomes, the original budgets, the 300-second feedback bound, the computed attainment `2 * 3 = 6 in ℤ` and zero-disposition counts. |
| RC-04 | The criteria concern fixed questions, observed results and preserved meaning. The 300-second bound of SC-013 and the repository paths of SC-020 and SC-025 are the owning issues' product contracts. |
| RC-05 | All sixteen stories have scenarios tied to original questions and fixed assignments; the kernel checkpoints and the computed attainments are distinct observations. |
| RC-06 | The edge-case table covers selected structures, missing data, choices, competing routes, outcomes, infinite extent, lifetime and exposed specimens; US9 to US16 state their failure cases in their scenarios. |
| RC-07 | V1, full B0, the classified Sage coverage and M5 keep distinct scopes and completion conditions; the computational milestones have V1, V2 and V3. |
| RC-08 | Assumptions name the authority, the delivery assignments, the independent mathematical dependencies, the authorship and input boundaries and the repository documents. |
| FRQ-01 | Every FR has a task whose check or acceptance condition observes it (task list, scope table and Trace fields). |
| FRQ-02 | Positive connected use, permitted choices, growth and computed category results stand beside the missing-data and failure cases. |
| FRQ-03 | Every SC is in the Trace of the tasks that observe it; semantic safety, conditional composition and complete delivery keep separate quantifiers. |

## Notes

A failing item requires a specification update through `speckit-specify` or `speckit-clarify` before `speckit-plan`. The constitution governs where a criterion and a constitutional obligation differ.
