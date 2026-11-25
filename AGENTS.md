# Constitution and issue references

**Work order:** execute the unchecked tasks of the [task list](specs/001-categorical-research-language/tasks.md#execution-order) in document order. Phase 0 comes first and is preserved throughout functional work: the fast feedback loop (T114/#84, done), then its timing records, test-run logs and application logs (T112, T127; FR-043). Complete functionality precedes final mathematical/runtime performance, proofs and assessments ([C21](.specify/memory/constitution.md#c21-fast-development-feedback-first-final-performance-after-functionality)). A task that needs a declaration missing from lean-categories has a task before it that names the lean-categories issue: do that task in lean-categories, then return ([execution order](specs/001-categorical-research-language/tasks.md#execution-order)). Kernel checks observe kernel behaviour with a protocol peer or an empty manifest; a computed mathematical result is leaf work and belongs to the [computational milestones](specs/001-categorical-research-language/plan.md#computational-milestones) (constitution C22, C23). M1 closes on F; its [checkpoints](specs/001-categorical-research-language/plan.md#m1-checkpoints) close one at a time before F. The [completion milestones](specs/001-categorical-research-language/plan.md#completion-milestones) group complete delivery outcomes; they do not replace task order. The [issue-tree mapping](specs/001-categorical-research-language/plan.md#issue-tree-and-task-order) gives the same phase owners and actual completion inputs; check `itree next` against the task source on resumption.

**Spec Kit workflow:** change the constitution, the specification, the plan and the task list only through the matching `speckit-*` skill, in this order: `speckit-constitution`, `speckit-clarify` or `speckit-specify`, `speckit-plan`, `speckit-tasks`. Finish with `speckit-analyze` before the commit. A direct edit of one of them leaves the others in conflict.

**Source location:** the kernel source (`CasCompiler/`, `CasRuntime/`) is on branch `integration/kernel-v1-20261106` (PR #87), which pins Lean 4.33.0 and Mathlib `v4.33.0`. `main` pins the toolchain and Mathlib of the research image ([#90](https://github.com/dzackgarza/lean-cas-dsl/issues/90)). PR #87 merges after the kernel branch is ported to those pins; #90 owns the port and records which Mathlib the running container holds. The two branches carry the same governing documents: the constitution, this file, `CONTRIBUTING.md` and `specs/`. An edit to one of them is committed on both branches.

Read the [project constitution](.specify/memory/constitution.md) before the
applicable issue requirements. It is the permanent repository authority for
cross-architecture obligations. The constitution, mathematical execution model, local
contribution rules and the Spec Kit feature directory (specification, plan, research, data model,
contracts, validation guide, checklists and tasks) are maintained repository documents.
Preserve their complete requirements through merges and migrations.
Work records, diagnostics and evidence remain in their owning issues; changes to constitutional
requirements follow its amendment rules.

- [Current handoff](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6726232237)
- [Spec Kit feature: specification, plan, contracts and tasks](specs/001-categorical-research-language/)
- [Roadmap and work records](https://github.com/dzackgarza/lean-cas-dsl/issues/10)
- [Actual selected cells, permitted choices and required-data errors](specs/001-categorical-research-language/contracts/mathematical-input.md)
- [Independent mathematical authority and computation-only leaf requirements](specs/001-categorical-research-language/spec.md)
- [Current task assignments and role/input conventions](specs/001-categorical-research-language/tasks.md)
- [Requirements-quality review and marker ownership](specs/001-categorical-research-language/checklists/architecture.md)
- [Architecture, ownership and evidence](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574949858)
- [Contribution policies](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6574924066)
- [Interpretation](https://github.com/dzackgarza/lean-cas-dsl/issues/66)
- [Execution](https://github.com/dzackgarza/lean-cas-dsl/issues/69)
- [Independent acceptance](https://github.com/dzackgarza/lean-cas-dsl/issues/24)
- [Construction inputs](https://github.com/dzackgarza/lean-cas-dsl/issues/23)
- [Higher coherence](https://github.com/dzackgarza/lean-cas-dsl/issues/82)
- Goals, plans and handoffs: section "Goals, outlines and plans" of `~/ai/AGENTS.global.md`

**Owner-design reconstruction source:** [owner design statements in summary, #91 record A](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942015918) · [mathematical contract and unresolved functorial issues, record B](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942060158) · [source-checked current implementation map, record C](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942116552). The maintained [architecture](specs/architecture.md) reconstructs the owner's constructor-as-functor and category-as-implementation-unit model. Do not replace an unresolved mathematical category/morphism action with a kernel or backend heuristic; the current source, not old audit function names, determines what remains to repair.

## Required mathematical model

Before changing interpretation, execution or a category interface, read
[the mathematical execution model](specs/architecture.md) and constitutional C1–C8, C22–C23.
The local explanation and feature contracts are maintained requirement documents; issue records
own work assignments and evidence. A source implementation is not authority to weaken either.

- Resolve the independently declared mathematical operation and its complete dependent interface
  before selecting a provider. Category membership and method applicability come from that source.
- Generate the public category implementation view from accepted mathematical declarations and
  the released contract. Reuse existing exporters and ports; a port is not the complete category
  interface, and generated documentation is not a second semantic registry.
- Realize functor object and morphism actions through public target constructors and exact selected
  endpoints. Inherited methods use the formal composite, with its actual domain and comparisons.
- Apply refinements only through formal classifiers, rules and evidence. Retain chosen structures
  separately from existence proofs; permit simultaneous refinements.
- Carry selected bindings, morphisms, cones, comparisons and dependent inputs forward. Preserve
  computational occurrence identity even when formal expressions are equal.
- Use common source preparation for all public requests, including deferred and provider requests.
  Keep runtime execution generic and mathematical computation in leaves, as C22 requires.
- Diagnose a lost association at the boundary that discarded it. Repair the producer and consumer
  together and delete its recovery substitute. Do not improve expression matching, global endpoint
  lookup or apex recognition as a replacement for retained mathematical data.
- Check the extension consequence: a new category with immediate functors leaves existing category
  implementations unchanged; a new generic method leaves existing applicable leaves unchanged.
  Verify the original mathematical continuation, not only dispatch or helper behavior.

## Development boundaries

Apply the [source-to-result correction](specs/001-categorical-research-language/tasks.md#required-source-to-result-correction--functional-work-after-t016-2026-11-17)
to each functional task. Preserve the dependency cuts already made while
correcting the mathematical relationship; moving recovery code into another file does not repair it.

- Checked source families and `ProgramBoundary` do not import runtime ownership or value storage.
  Actual operand binding and response admission belong to runtime request preparation.
- Source rules share the typed reading context and import only the mathematical mechanisms they
  use. The complete reader assembles those rules; transport and lifecycle code do not import it.
- Runtime execution consumes prepared operations. Provider-requested calls use the same source
  preparation as direct calls; a runtime module must not rebuild their mathematical applications.
- Production targets build the connected public implementation. Compiler/runtime test targets are
  separate, and tests never provision packages during Lean elaboration or name a developer's
  absolute interpreter path.
- The loop of each change is `just loop "<test module of the changed mechanism>" [touched
  acceptance files]` ([feedback loops](CONTRIBUTING.md#feedback-loops), limit 300 s). Then check
  its original public consumer the same way. The long run, `just milestone "<reason>"`, is for a
  batch of changes, a push or a handoff; it is not the check of one change. `just stop` stops a
  build that its caller left behind. Profiling is explicit and no prior profile is required to
  finish a slow functional build.
- Assess encapsulation from actual imports, public declarations and affected consumers. Neither
  file counts nor moving a function establishes an independent compilation boundary. Preserve
  executable metaprogram dependencies when narrowing public imports.
- Keep mathematical, public computational and physical software dependencies distinct. Shared
  code/engines remain permitted under C22; unrelated optional implementations must not be required
  for an unaffected consumer. A current failed, missing or stale run cannot inherit prior success.

The full production, notebook, mathematical and independent-extension obligations remain with
their existing owners. Focused checks establish only their exercised properties. Independent
extension trials keep the kernel, released contract, old consumer and expectations frozen under
C12; adding another kernel case to accommodate an extension fails that candidate.
