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

## Planning work that remains

The roadmap of the five repositories is in their Spec Kit feature directories. These items remain.

1. **Contract task list.** The table "Kernel consumers" of lean-cas-dsl-leaf-contracts
   (`specs/001-released-contract-v2/tasks.md`) names the kernel task T104, which the computational
   milestones T200 to T224 replace. Its row moves to those tasks.
2. **Leaves task list.** lean-cas-dsl-leaves (`specs/001-category-implementations/tasks.md`) has no
   survey and implementation pair for the unit group of #3, which lean-cas-dsl T155 assigns to
   `backends/gap_groups.py`.
3. **Owner questions.** Q1 (infinite cardinals) and Q2 (the user-visible form of diagnostics) of
   `plan.md`.
