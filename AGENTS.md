# Roles (read before anything else)

You are either the **orchestrator** or a subagent with exactly one role
([specs/architecture.md](specs/architecture.md), "Authors: one role per agent"):
- The orchestrator owns policies, gates, compliance, this repository's kernel and language, and
  the leaf contract. It delegates the rest.
- The formalization subagent writes `lean-categories` only.
- The acceptance subagent writes `tests/acceptance/` only.
- The leaf subagent writes leaves only.

No agent writes in two roles. Information flows formalization → tests → implementation, never
back. An owner correction is committed into its owning document, or a gate, in the turn it is
given (CONTRIBUTING, "A correction is encoded where it will be read"). Open governance nodes
(`gov-*` in [the plan](specs/computational-core-plan.md)) precede all other work.

# Architecture contract (read first)

[`specs/architecture.md`](specs/architecture.md) owns the separation of concerns:
- `lean-categories` owns all mathematics;
- this repository derives the language from `lean-categories`' pinned release and owns no ontology;
- leaves only realize operations that are already formal;
- `research` owns no ontology.

Every plan node and edit conforms to it. In practice it forbids the following.

* **Missing mathematics goes upstream.** If you need a category, functor, classifier, operation
  or coherence that is not formal, stop. Formalize it in `lean-categories`, or open the request
  there. Then release, re-pin, and continue here.
  - Never coin it in this repository: a leaf, a probe, the notebook or the kernel.
  - The semantic registry is `lean-categories`' (`LeanCategories.Catalogue`). `normalized_registry`
    refuses every module outside it, and `SemanticProjectionProbes` checks that every semantic row
    here was written upstream.
* **Never shape semantics by computability.** Do not add, remove, narrow or weaken a semantic row,
  domain or result type because a backend can or cannot compute something. A backend's limits
  restrict its realization only.
* **Leaves contribute zero mathematics.** A leaf registers realizations of registered operations
  on presentations, and nothing else. If writing a leaf seems to need a new method, placement,
  forwarding or edge, the defect is upstream. Fix it there, never in the leaf.
* **Acceptance assertions are permanent.**
  - Write the expected value from a proof, a citation or an independent oracle before running
    anything. Never take it from the implementation under test.
  - Never edit an admitted assertion because an implementation changed. Add new assertions
    instead.
  - Only an upstream correction to the mathematics changes an assertion, in the commit that
    re-pins it.
* **Failures stay stratified.** The five kinds are:
  1. semantically invalid;
  2. `NoImplementation`;
  3. unavailable or crashed;
  4. malformed output;
  5. wrong answer.

  Never collapse one kind into another. Never turn a gap into a fallback, a default or a nearby
  answer.

# Where the work is (read second)

About 90% of the work is formalizing the mathematical API in `lean-categories`: categories,
objects, elements and methods, the last usually as functors, with surface names. That is where the
API is designed. Next comes the permanent test suite here, written in the DSL. Leaves are
mechanical, external, long-tail work.
- Never write or extend a leaf to make a test pass, and never chase a realization of a specific
  operation as progress.
- The leaves live in `lean-cas-dsl-leaves` and the leaf contract in `lean-cas-dsl-leaf-contracts`
  (`specs/architecture.md`, "Packages"). Leaves, including probes, belong to the leaf repository
  and are written by the leaf subagent. That this repository still requires `cas_leaves` and has a
  `CasLeaves/` directory is a defect (`gov-no-leaves-here`), not a licence. The orchestrator never
  writes, ports or polishes a leaf. A probe's finding reaches the kernel, the contract or
  `lean-categories` as a request.
- A leaf never sees the tests. It depends only on the leaf contract (`CasContract.Leaf`) and the
  catalogue, and the harness runs the suite over installed leaves (`just harness`).
- The contract is the kernel's: change it together with the kernel, release it, re-pin it in the
  leaves and here. Development builds link `.lake/packages/{cas_leaf_contracts,cas_leaves}` to the
  working trees, as for `lean_categories`.

# Search before authoring (gate-enforced)

Before writing any Lean definition for a plan node, search the formalization corpus
(`python <lean-categories>/scripts/formalization_corpus.py search '<query>'`, several spellings;
it indexes Mathlib, infinity-cosmos, agda-categories and more) and write
`specs/reuse/<node>.md` with `## Queries`, `## Owner` (the existing declarations that own the
mathematics), and `## New code` (only what no dependency supplies). `just build` runs
`scripts/check_reuse_records.py` and fails when the plan's **Next** node, or a node delivered from
2026-09-30 on, has no such record. Categories, functors, natural transformations, whiskering,
pasting, adjunctions and limits are Mathlib's (`Cat` is a strict bicategory; `CatCommSq`,
`TwoSquare`); never write a second calculus of them. Failure of record: `cc-cells`, 2026-09-29.

<!-- agent-memory:start -->
# Agent memory

This repository uses the central agent memory vault at `/home/dzack/.agent-memory-vault`.

Project memory key: `projects/github.com__dzackgarza__lean-cas-dsl/index`.

Repository `.agents` and `.hermes` paths are symlinks to the same vault-owned project directory.

Before changing architecture, search both project and global memory:

```bash
agent-memory search --scope both "<task or subsystem>"
```

Record durable repo-specific lessons with:

```bash
agent-memory add --scope project --type decision --title <title> --content <content>
agent-memory add --scope project --type trap --title <title> --content <content>
agent-memory add --scope project --type advice --title <title> --content <content>
agent-memory add --scope project --type context --title <title> --content <content>
agent-memory add --scope project --type reference --title <title> --content <content>
```

Plan work is card-backed. Create and update plan cards with `agent-memory plan add` and `agent-memory plan update`, not `agent-memory add --type plan`.

Use `agent-memory retrieve <key>`, `agent-memory update <key>`, and `agent-memory delete <key>` for memory CRUD.

The vault should be committed at all times. Treat staged or unstaged vault changes as an ephemeral error state. Before normal memory work resumes, load the bundled vault-maintenance skill with `agent-memory maintain skill vault-maintenance` and follow its referenced check, repair, and commit workflows.

Move reusable lessons during maintenance with:

```bash
agent-memory maintain move <key> --to global/advice
```
<!-- agent-memory:end -->
