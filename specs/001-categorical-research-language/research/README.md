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
| `milestones.md`, `milestones.json` | The grouping of the categories into 25 computational milestones that the category tasks of the task list replace: the categories, statements and moved registrations of each group, the routes of the 18 statements of the K3 and K14 files, and a probe of countable sets in the container Sage. `category-scope.json` reads its order and statements. | the records above; Sage 11.0.beta5 in the research container |
| `rows-audit-A.md`, `rows-audit-B.md`, `rows-audit-C.md` | Three readings of the correction rows of the task list against the committed kernel source: a verdict (holds, moved, changed, repaired) and the current location of each row, the provider-requested path against C23, the reader forms of `CasCompiler/Syntax.lean` and the removal steps of the old path. The task lines of Part 1 hold their results. | kernel branch `fc7fdf8` (source of `7661292`) |
| `kernel-row-decisions.md` | The decisions for the "connect or delete" and "keep or move" rows of the task list, and the rows that do not match the kernel source at its tip. | kernel branch `fc7fdf8` (source of `7661292`) |
| `spike-inventory.md`, `spike-inventory.json` | The 157 computations, 18 ceilings and 38 features of the first spike, each with its source; the workload statements that carry each computation or a proposed statement with its catalogue rows and route; the features mapped to FRs and user stories; the rows of the 18 K3 and K14 statements; the catalogue rows that the catalogue lacks (14 for computations, 4 more for ceilings). | `SPEC.md` `73bfb11`; spike commits `eca90be` to `32e6872`; acceptance notebook `9c7d438`; catalogue `3f8aedf` |
| `category-scope.md`, `category-scope.json`, `category_scope.py` | One entry for each of the 38 categories that a computation needs, in structural order: its rows with kind, owners, parameters, version (V1, V2) and the statements that need each row; its milestone, engine family and existing registrations. `category_scope.py` regenerates the JSON from the records above (`uv run category_scope.py`). | the records above |

## Planning work that remains

The roadmap of the five repositories is in their Spec Kit feature directories. These items remain.

1. **Contract task list.** The table "Kernel consumers" of lean-cas-dsl-leaf-contracts
   (`specs/001-released-contract-v2/tasks.md`) names the kernel task T104, which the computational
   milestones T200 to T224 replace. Its row moves to those tasks.
2. **Leaves task list.** lean-cas-dsl-leaves (`specs/001-category-implementations/tasks.md`) has no
   survey and implementation pair for the unit group of #3, which lean-cas-dsl T155 assigns to
   `backends/gap_groups.py`.
