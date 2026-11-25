# Research records of the roadmap planning (snapshot of 2026-11-25)

These files are the evidence behind the plan and the task list. Each is a reading of fixed
revisions and is not kept current. The plan and the task list state the decisions; a record here
gives the facts and the sources that a decision used.

| File | Content | Revisions read |
| --- | --- | --- |
| `scaffolding.md`, `scaffolding.json` | The 100 registered categories of lean-categories, their structural functors and classifier forgets, the layer of each category above `cat.sets`, the 51 categories with no structural chain to sets, the independent directions. | lean-categories `443fba9`; published catalogue at mathematics revision `3f8aedf` |
| `workload-routes.md`, `workload-routes.json` | For each of the 287 workload statements (153 permanent, 134 extension): the catalogue rows that it reads and the categories on its route; the statements that each set of categories makes computable. | kernel branch readings; catalogue `3f8aedf` |
| `existing-leaves.md`, `existing-leaves.json`, `existing-leaves.categories.json` | The 115 registrations of lean-cas-dsl-leaves, their engines and routines, their owner categories, the hand-rolled algorithms, and the evaluation that the kernel performs itself. | lean-cas-dsl-leaves `8b181d7`; contract package `ef3771d` |
| `engine-survey.md` | Survey of computational engines for each family of categories, with versions, licences, sources, gaps, and what the research container holds. | upstream versions of 2026-11-25 |
| `upstream-inputs.md` | The evidence for the lean-categories issues #190 to #200 (tasks T128 to T138) and for the inputs that are present upstream. | lean-categories `443fba9` |
| `milestones.md`, `milestones.json` | The computational milestones of the plan: the categories, statements and moved registrations of each, the routes of the 18 statements of the K3 and K14 files, and a probe of countable sets in the container Sage. | the records above; Sage 11.0.beta5 in the research container |
| `kernel-row-decisions.md` | The decisions for the "connect or delete" and "keep or move" rows of the task list, and the rows that do not match the kernel source at its tip. | kernel branch `fc7fdf8` (source of `7661292`) |

## Planning work that these records feed and that is not written yet

The task of the planning session is the full roadmap, across all repositories, in Spec Kit form,
with no decision left for implementation time. This list is what remains. Take the items in order.

1. **M3, M4 and M5.** 58 requirements of the issues #19 to #24, #66, #69, #82, #85, #91, #68, #34,
   #3, #8 and #13 have no task or only a partial one. Add their requirements to `spec.md` and their
   tasks to `tasks.md`.
1. **Sibling repositories.** lean-categories, lean-cas-dsl-leaf-contracts, lean-cas-dsl-leaves and
   lean-jupyter-kernel have no Spec Kit documents. Each needs a constitution, a specification, a
   plan and a task list for its part of the roadmap. In lean-categories, the rule LC-17 and the rule
   near `TODO.md:122` stop a consumer's workstream from doing the upstream tasks T118 to T138
   there; they must agree with constitution C21 and the authorship rule of this repository.
1. **Validation guide.** `quickstart.md` names passagemath 10.8.13. The research container holds
   Sage 11.0.beta5 as a source build and no passagemath.
