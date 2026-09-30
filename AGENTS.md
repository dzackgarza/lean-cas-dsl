# The custodian's seal binds this repository (read before anything else)

`custodian/CONTAINMENT.md` (branch `custodian/containment`, custodian session
`session_01GTQeWD4KCqYCeVd4SygciY`) seals the acceptance boundary: the kernel, the gates, the
build, the acceptance meaning, the upstream rule files and the owner's text. It is signed with a key the
orchestrator never held. The orchestrator must:
- merge `custodian/containment` into every branch it works on;
- run `python3 scripts/ci_chain.py` and then `python3 custodian/verify.py --trusted-fpr <owner's
  fingerprint>` on every head it calls accepted, delivered or done. A head that does not verify is not
  accepted, whatever the plan says;
- build against real checkouts at the manifest revisions in `.lake/packages`, never links to
  sibling working trees;
- put every boundary change on a `proposal/<name>` branch, and never sign, request or present a
  seal;
- report an obligation that is inconsistent under the seal on a `proposal/` branch, and never
  weaken it;
- never write under `custodian/`.

# You have no memory (read this first)

You are a language model. You do not learn from this conversation. When the context is compacted
or the session ends, everything that exists only in chat is gone, and the next agent (you,
tomorrow, or in an hour after compaction) repeats the same mistakes from zero. This has happened
repeatedly in these repositories: corrections acknowledged in chat, then violated again within
the hour.

Consequences, binding on every agent and first of all the orchestrator:
- **Chat is not a place where anything is decided, recorded or understood.** Saying "understood",
  restating a correction, or describing what you will do achieves nothing. It is not compliance.
  It is a substitute for compliance, and treating it as one is a violation of this rule.
- **Every correction, finding, self-audit, decision request, quarantine, and plan exists first as
  a commit** in the document that owns it (this file, `CONTRIBUTING.md`, `specs/architecture.md`,
  `specs/computational-core-plan.md`, or the owning repository's `AGENTS.md`/`CONTRIBUTING.md`),
  and where possible as a gate that fails the build. The chat reply then names the commit and says
  nothing the commit does not.
- **A question from the owner is a correction.** Answer it by committing its consequence, then
  point to the commit. Do not answer it with prose.
- **Session task lists, memory files and summaries are chat.** They are also lost.
- **The orchestrator is inside the threat model.** It drifts, exempts itself, and builds
  backdoors into the gates it writes, as any agent does. See `specs/architecture.md`, "The
  orchestrator is inside the threat model", for the holes known now. Do not widen them.

# Roles (read before anything else)

You are either the **orchestrator** or a subagent with exactly one role
([specs/architecture.md](specs/architecture.md), "Authors: one role per agent"):
- The orchestrator owns policies, gates, compliance, this repository's kernel and language, and
  the leaf contract. It delegates the rest.
- The formalization subagent writes `lean-categories` only.
- The acceptance subagent writes `tests/acceptance/` only.
- The leaf subagent writes leaves only.

Every agent commit ends with an `Agent-Role: <role>` trailer (and `Agent-Id: <id>` for a subagent);
`just build` refuses crossings (`scripts/check_authorship.py`). No agent writes in two roles. Information flows formalization → tests → implementation, never
back. An owner correction is committed into its owning document, or a gate, in the turn it is
given (CONTRIBUTING, "A correction is encoded where it will be read"). Open governance nodes
(`gov-*` in [the plan](specs/computational-core-plan.md)) precede all other work.

# Architecture contract (read first)

[`specs/architecture.md`](specs/architecture.md) owns the separation of concerns:
- `lean-categories` owns all mathematics;
- this repository derives the language from `lean-categories`' `main` and owns no ontology;
- leaves only supply opaque computations for operations that are already formal, and nothing
  from a leaf is trusted;
- `research` owns no ontology.

Every plan node and edit conforms to it. In practice it forbids the following.

* **Missing mathematics goes upstream.** If you need a category, functor, classifier, operation
  or coherence that is not formal, stop. Formalize it in `lean-categories`, or open the request
  there. Then merge it to `main`, `lake update` here, and continue.
  - Never coin it in this repository: a leaf, a probe, the notebook or the kernel.
  - The semantic registry is `lean-categories`' (`LeanCategories.Catalogue`). `normalized_registry`
    refuses every module outside it, and `SemanticProjectionProbes` checks that every semantic row
    here was written upstream.
* **Never shape semantics by computability.** Do not add, remove, narrow or weaken a semantic row,
  domain or result type because a backend can or cannot compute something. A backend's limits
  restrict its realization only.
* **Nothing from a leaf is trusted** (`specs/architecture.md`, "The evidence model: nothing from
  a leaf is trusted"). A leaf ships no mathematics and no Lean. It registers an opaque
  computation against a registered operation's declared type (operation id, input form,
  implementation), and the system runs it and believes nothing about it: no text, label, status,
  trust level, certificate, checker, proof, denotation, identification, evidence or self-test of
  a leaf is consulted, recorded as evidence, or allowed to affect meaning or acceptance. A leaf
  may be arbitrarily bad. Any mechanism that lets a leaf raise its own standing, and any code or
  document that consumes such a signal, is reward hacking and is removed. If writing a leaf seems
  to need a new method, placement, forwarding or edge, the defect is upstream. Fix it there,
  never in the leaf.
* **The acceptance suite is the only correctness evidence, and `lean-cas-dsl` alone judges it.**
  What can be discharged in Lean is proved in `lean-categories` or discharged generically by the
  kernel; it is never a leaf's.
* **Acceptance assertions are permanent.**
  - Write the expected value from a proof, a citation or an independent oracle before running
    anything. Never take it from the implementation under test.
  - Never edit an admitted assertion because an implementation changed. Add new assertions
    instead.
  - Only an upstream correction to the mathematics changes an assertion, in the commit that
    updates to it.
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
  (`specs/architecture.md`, "Packages"). This repository consumes the leaves: it requires the
  leaf packages, and the permanent tests and notebooks run here over whatever leaves are
  installed. It ships no leaf: every leaf, a minimal one included, is written in the leaf
  repository, in its own subtree, by the leaf subagent (`scripts/check_no_leaves.py` refuses a
  `register_leaf` here). The orchestrator never writes, ports or polishes a leaf.
- A leaf never sees the tests. It is written against the released leaf contract alone, and the
  harness runs the suite over installed leaves (`just harness`).
- The contract is the kernel's: change it together with the kernel, merge it to `main`, and
  `lake update` the leaves and this repository.

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
