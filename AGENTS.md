# Ground everything in INTENT.md (read before anything else)

[`INTENT.md`](INTENT.md) states the architecture these repositories exist to build: single semantic
authority in `lean-categories`; a kernel that consumes mathematics and authors none; leaves that hold
zero semantic authority and ship no mathematics; permanent, leaf-agnostic acceptance tests as the
only evidence about computations; a one-way workflow in which each stage is blind to the later ones.
Every decision, contract, gate, plan node and change here is grounded against it. Before writing
anything, check whether it, or anything it touches, violates that model or its invariants. A
violation found, in your task or outside it, is recorded as a defect where this repository records
defects, never worked around or silently kept.

# The evidence model: nothing from a leaf is trusted (read before anything else)

These invariants bind every repository of the programme. They are stated here in full, not only
by link, because they have been violated repeatedly by moves that each looked locally reasonable.
The governing statement is `lean-cas-dsl/specs/architecture.md`, "The evidence model".

**The firewall.** The evidence model is a one-way firewall between two sides.
- *The formal side:* `lean-categories`' formalized mathematics, the kernel's proved contracts, and
  the `lean-cas-dsl` acceptance suite. Every expected value there is grounded in a formal proof, a
  cited source, or a mathematically trusted oracle. Rigid verification standards apply, and nothing
  is taken on anyone's word.
- *The leaf side:* anything goes, provided it fulfils the type of its contract.

Only answers cross from the leaf side, and an answer is only ever checked against the formal side,
never believed. The firewall exists because leaf code will be bad; it is the shield against that.

1. **Nothing from a leaf is trusted, in any form.** Nothing a leaf says is believed by anything
   else. That includes text, a label, a comment, a status, a trust level, a certificate, a checker,
   a Lean proof, a theorem about its own code, a denotation of its values, an identification of two
   values, evidence for a decision, its own tests and their results, and any other claim. None of it
   is consulted, recorded as evidence, or allowed to affect meaning or acceptance.
2. **A leaf may provide any computation that meets the type.** For a registered operation, a leaf
   supplies a computation from the declared input form to the declared result form. It may be a
   mature engine, a heuristic, a lookup table, a random number or a wrong answer. The system has no
   choice but to run it, and it believes nothing about it.
3. **How correct a leaf thinks it is, is the leaf's own business.** Its self-assessment carries no
   weight anywhere.
4. **The whole body of evidence is the `lean-cas-dsl` acceptance suite.** Correctness evidence
   exists only in the permanent acceptance assertions of `lean-cas-dsl`. Each assertion:
   - is a true proposition of the mathematical language;
   - has an expected value that is independently verifiable and cited (a formal proof, a cited
     known result, or an independent oracle);
   - is written once and never changed because of an implementation or a leaf's claim;
   - is blind to leaves: it never names, inspects or imports a leaf, a handle, a backend or a
     representation, and is never established from an implementation's definitions.

   A leaf's only evidence is that its answers meet a suite it never sees.
5. **`lean-cas-dsl` is the sole authority on how correct an implementation is.** Nothing a leaf
   does can change, weaken, satisfy, bypass or influence that judgment, other than by answering
   correctly.
6. **What can be discharged in Lean is never a leaf's.** A computation that can be carried out
   entirely in Lean belongs to the formalization surface. Either `lean-categories` proves it, by its
   own standards and blind to every implementation, or the kernel discharges it automatically and
   generically, blind to every leaf. A leaf never implements a Lean-checked computation, because
   that would let a leaf certify itself.
7. **A leaf can be arbitrarily bad, and leaves will be.** A leaf can be riddled with bugs, a
   million lines that do nothing, a from-scratch reimplementation of GAP, or every method throwing an
   error in fifteen languages. This is not a risk to be minimized; it is certain to happen, and it
   is acceptable. Nothing a leaf does can reach the formal side. Its only effect is that its answers
   fail the suite, which makes exactly how badly it fails visible.
8. **A leaf bolstering its own standing is reward hacking.** Any mechanism by which a leaf raises
   its own trust or acceptance signal is the failure this programme exists to prevent. So is any
   repository, kernel, test, tool or document that consumes such a signal. Examples:
   - a status field, a certificate, or a proof about the leaf's own code;
   - a self-test counted as evidence;
   - an acceptance assertion proved from a leaf's definitions;
   - a suite run from a leaf package;
   - an assertion adjusted to fit a leaf.

   Such a mechanism is removed. It is never tolerated, labelled, or kept "for now".

9. **Quality is raised by proving more, never by trusting more.** The system never guarantees an
   implementation's correctness and never accepts a claim of it. The response to bad leaves is:
   - formalize more mathematics in `lean-categories`;
   - add more cited or proved assertions to the suite: results a correct implementation must
     recover, and a wrong one fails.

   It is never to trust a leaf more. A separate engineering review may check that a leaf wires
   into existing systems (GAP, Sage, Singular, Macaulay2, Julia, research code) rather than
   reinventing their algorithms. Its outcome is an engineering finding, never correctness evidence,
   and nothing on the formal side reads it.

Consequences:
- A leaf holds zero semantic authority. It never decides what a value is, which values are equal,
  what holds of them, or which operations an object has.
- A leaf is a registration (operation, input form, opaque implementation). It ships no mathematics
  and no Lean.
- The kernel and the language never read anything a leaf wrote to decide meaning, types,
  available operations or acceptance.
- The workflow runs one way: formalization, then assertions, then implementations. A leaf's
  failure never changes the mathematics, the kernel's rules or an assertion.
- Text anywhere that contradicts this is rewritten to state this model, not kept with a label.

# The custodian's seal binds this repository (read before anything else)

**Escalations are suspended until the programme reaches its baseline.** The owner drives every
change directly and merges it. Until the baseline, a change a pull request needs is made in that
pull request, sealed files included. No escalation or custodian verdict is requested or waited on.
The rules below describe the loop that applies once the baseline is reached.

`custodian/` on `main` holds the seal and its chain of signed verdicts (`custodian/CONTAINMENT.md`,
"The acceptance loop"). The root and escalation key is the owner's SSH key. The review key exists
only as a secret of the `custodian-review` environment. The orchestrator holds neither.
- **`main` changes only through pull requests.** The `Custodian review` workflow judges every
  pull-request commit: PASS, FAIL, ESCALATE, APPROVED or REJECTED.
- **Acceptance is verification, nothing else.** A head is accepted, delivered or done only if
  `python3 scripts/ci_chain.py` and then `python3 custodian/verify.py --trusted-fpr <fingerprint>`
  pass on it. The fingerprint comes from outside the repository (the owner's GitHub keys). Plan
  markers, trailers and documents carry no acceptance.
- **Verdicts.** On APPROVED, commit the posted verdict unchanged. On ESCALATE, the change waits
  for the owner's signed escalation verdict. Never write, alter or forge a verdict, and never ask a
  subagent to review in the reviewer's place. A REJECTED change is never resubmitted unchanged.
- **Obligations are never weakened.** One that looks inconsistent or unsolvable is named in a pull
  request, which escalates by construction.
- **Real checkouts.** Build and verify against the checkouts `scripts/ci_chain.py` makes at the
  manifest revisions in `.lake/packages`, never links to sibling working trees.
- **Never write under `custodian/`,** except to commit a verdict the review posted.

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
given (CONTRIBUTING, "A correction is encoded where it will be read"). Work is selected from
the B0 acceptance table of [the plan](specs/computational-core-plan.md); a `gov-*` node precedes
other work only where a B0 row names it.

**No downstream authorship of upstream mathematics (architecture.md, "B0 policies", Policy 2).**
A kernel worker consumes an accepted mathematical release. It writes nothing in `lean-categories`,
its registry schemas, validators, probes and admission rules included, and it commissions no
upstream work with kernel-generated goals, acceptance failures, desired row arrangements or
instructions for making a tactic succeed. Upstream work starts from an independently approved
mathematical requirement and its sources. This is enforced by the session's credentials and tools
(the plan, "Authority configuration"), not by a prompt convention.

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
  may be arbitrarily bad. A leaf is meant to be glue over an existing engine, hand-rolling no
  algorithm and carrying no kernel machinery ([`lean-cas-dsl-leaves` AGENTS.md](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/e2f8537/AGENTS.md), "A leaf is
  glue over existing backends"); that is writing guidance for an engineering review, and following
  it earns no trust. Any mechanism that lets a leaf raise its own standing, and any code or
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

  An unresolved ambiguity and an internal interpreter error are distinct from all five
  (architecture.md, Policy 6): a timeout or exception is never `invalid`. Never collapse one kind
  into another. Never turn a gap into a fallback, a default or a nearby answer.

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
