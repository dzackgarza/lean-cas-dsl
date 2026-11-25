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
| `kernel-row-decisions.md` | The decisions for the "connect or delete" and "keep or move" rows of the task list, and the rows that do not match the kernel source at its tip. | kernel branch `fc7fdf8` (source of `7661292`) |

## Planning work that these records feed and that is not written yet

The task of the planning session is the full roadmap, across all repositories, in Spec Kit form,
with no decision left for implementation time. This list is what remains. Take the items in order.

1. **Computational milestones.** `plan.md` names three milestones and "later milestones", and T104
   holds all leaf work in one task whose specification is written "when it starts". Write the
   complete list from `scaffolding.json` and `workload-routes.json`: each milestone with its
   categories, the statements that it makes computable, its engine from `engine-survey.md`, its
   upstream tasks, and the existing registrations of `existing-leaves.json` that move into it. Give
   each milestone its own task. Facts that the list must use:
   - only 49 of the 100 categories have a structural chain to sets; the order of the other 51
     (cardinals, arrow and core categories, refinements) needs a stated rule;
   - a ring reaches groups, and the list of the ring milestone in `plan.md` omits groups;
   - 15 statements stay within sets, the order categories add 2, and the chain to rings adds 50;
   - cardinality statements need `cat.core_sets` and `cat.cardinals`;
   - the recorded readings name ring rows, and the kernel report of 2026-11-22 reads ℤ as a
     commutative ring and ℚ as a field; decide which reading the milestone list uses and say so.
2. **Correction rows.** The correction tables of `tasks.md` describe the kernel source of
   `9165255`. `kernel-row-decisions.md`, section G, lists rows that are stale at `fc7fdf8`. Apply
   its decisions C to F (derivation path through `CasCompiler/PublishedSource.lean`; the moves out
   of `CasCatalogue/`; removal of the two repaired limit rows and of item (4) of the T007 note;
   the recursion guard by the parent chain of a request; two new rows of kernel computation,
   `CasCompiler/SourceRing.lean:67-73` for T036 and `CasCompiler/SourceLimit.lean:415-420` for
   T048). Then check every other row against the tip.
3. **M3, M4 and M5.** 58 requirements of the issues #19 to #24, #66, #69, #82, #85, #91, #68, #34,
   #3, #8 and #13 have no task or only a partial one. Add their requirements to `spec.md` and their
   tasks to `tasks.md`.
4. **Sibling repositories.** lean-categories, lean-cas-dsl-leaf-contracts, lean-cas-dsl-leaves and
   lean-jupyter-kernel have no Spec Kit documents. Each needs a constitution, a specification, a
   plan and a task list for its part of the roadmap. In lean-categories, the rule LC-17 and the rule
   near `TODO.md:122` stop a consumer's workstream from doing the upstream tasks T118 to T138
   there; they must agree with constitution C21 and the authorship rule of this repository.
5. **Validation guide.** `quickstart.md` names passagemath 10.8.13. The research container holds
   Sage 11.0.beta5 as a source build and no passagemath.
