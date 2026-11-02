# Ground everything in INTENT.md (read before anything else)

Use the available working environment and its selected Lean and engine installations.
The [shared math container guide](https://github.com/dzackgarza/ai-review-ci/blob/main/SAGE-CONTAINER.md#use-the-image)
documents the existing image and launchers when they are needed. Rebuilding or moving a
usable environment is not a prerequisite to the implementation work.

[`INTENT.md`](INTENT.md) states the architecture these repositories exist to build: single semantic
authority in `lean-categories`; a kernel that consumes mathematics and authors none; leaves that hold
zero semantic authority and ship no mathematics; permanent, leaf-agnostic acceptance tests as the
only evidence about computations; a one-way workflow in which each stage is blind to the later ones.
Every decision, contract, gate, plan node and change here is grounded against it. Before writing
anything, check whether it, or anything it touches, violates that model or its invariants. A
violation found, in your task or outside it, is recorded as a defect in the issue that owns the
affected work, never worked around or silently kept.

[`CONTRIBUTING.md`](CONTRIBUTING.md#behavioural-contribution-policies) governs work selection,
research, decomposition, evidence and continuation. Preserve the requested obligation across
those steps; neither a partial result nor its accurate description completes the parent task.

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

# Current work

Follow the current user instructions and the decisions in the relevant issues:

- [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10): roadmap, priorities and delivery order.
- [#85](https://github.com/dzackgarza/lean-cas-dsl/issues/85): the replacement decision and its required outcome.
- [#66](https://github.com/dzackgarza/lean-cas-dsl/issues/66) and
  [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69): implementation assignments and continuation.
- [#24](https://github.com/dzackgarza/lean-cas-dsl/issues/24): independent acceptance.

These issues contain the current work orders and requirement decisions. Repository documentation
describes policies, interfaces, source and verification; update it to reflect issue decisions.
It does not supply a separate queue or supersede those decisions.

# Implementation authority

Make changes through **forward commits**, preserving existing history and unrelated user work.
Proceed within the assigned mandate without requesting authorization already given. Record an
unavailable operation and its exact error, and continue the substantive work that remains available.
A successful compile by itself does not discharge the unchanged positive assertion and its
same-candidate protected negatives.

An explicit current owner instruction governs work immediately. Recording it
makes it durable; recording, merging, or signing it does not create its authority.
An assistant proposal is not an owner instruction. A question is not automatically
a new rule.

Record work and requirement decisions in their owning issues, and update affected documentation.
Routine recording does not create a documentation PR, approval request, plan node, separate build,
or waiting period. Preserve unrelated working-tree changes and use ordinary commits.

Send material instruction corrections to every active session performing the
affected work. Do not wait for a merge or restart to correct its task brief.
This applies to the orchestrator and controller workers; it does not authorize
sending downstream implementation details to formalization or acceptance authors.

"Needs an owner decision" means a specific choice remains outside the approved
mandate. Before using that description, identify the undecided choice and why
the existing instruction does not settle it.

**Owner ruling (2026-10-29): the owner decides what affects the end-user
experience; agents decide architecture.** Internal representations, module
structure, value encodings, the reader's implementation, deletion lists and line
caps are agent decisions. Make them from the evidence and the requirements, and
do not escalate them. Escalate a choice only when it changes what a user writes,
sees, or can compute, and state it in those terms.

A refused administrative operation is instead an execution dependency. Report
the exact operation and permission required, without presenting new policy
alternatives or asking for authorization already given.

The author may propose, implement and test a controller or gate correction as
construction source. It may not accept or install its own replacement as the
authoritative judge, fabricate independent approval, alter mathematical acceptance
to fit the implementation, or declare B0 accepted. Source integration is not a
change to the independently accepted evaluator or release.

# You have no memory (read this first)

You are a language model. You do not learn from this conversation. When the context is compacted
or the session ends, everything that exists only in chat is gone, and the next agent (you,
tomorrow, or in an hour after compaction) repeats the same mistakes from zero. This has happened
repeatedly in these repositories: corrections acknowledged in chat, then violated again within
the hour.

Consequences, binding on every agent and first of all the orchestrator:
- **Chat is not a place where anything is recorded or understood.** An owner's decision given
  there governs at once. Record work decisions in their owning issues and update affected
  documentation so the next agent has the current instruction.
  Saying "understood", restating a correction, or describing what you will do achieves nothing.
  It is not compliance.
  It is a substitute for compliance, and treating it as one is a violation of this rule.
- **A decision that must outlive the chat goes to its existing owner:** work, priority and
  requirement decisions belong in their issues; stable policies and technical descriptions belong
  in the corresponding documents, updated to reflect those decisions. An owner's explicit decision
  is authoritative when given, not when committed; an owner's question is answered, and is not by
  itself an instruction;
  your own proposal is not an owner decision (policy 2). An ordinary defect yields a code
  correction and a test, not a new policy, plan node or documentation pull request. Recording a
  decision or updating a description uses ordinary issue updates and commits, without creating an
  approval transaction; a branch, pull request, review or signature is used only where it performs
  a needed decision or validation (policy 2).
- **Session task lists, memory files and summaries are chat.** They are also lost.
- **The worker directive (owner replacement, 2026-10-02; architecture.md, "The policies").**
  - The assigned obligation and accepted input revisions are supplied by the controller from the
    assigned issue. They are not reconstructed from a session summary, a recent failure, or the
    worker's previous claims.
  - Complete the assigned generic mechanism against its full acceptance. Source checkpoints
    preserve work; they do not complete the assignment or authorize selection of an easier
    successor.
  - Use only the role's supplied inputs and operations. An unavailable authority operation is not
    obtained by another connector, credential, public fetch, shared context, or message to another
    author.
  - The worker does not draft another role's instructions. The launcher supplies that role with
    its independently assigned requirement and permitted inputs. Downstream goals, expected
    answers, row designs, and implementation-shaped reformulations are not dispatch payloads.
  - Submit source and findings through the assigned repository and review channel. Do not create
    new policies, plan rows, progress ledgers, exemption procedures, or review transactions to
    process an ordinary defect.
  - An unavailable operation blocks only consumers of its missing input. Continue the assigned
    substantive work that remains executable; the controller selects another existing obligation
    only when the actual dependency requires it.
  - Record explicit work decisions in their owning issues and update affected documentation
    without changing unrelated instructions. Do not treat a question, an assistant proposal, or
    publication of a document as a new grant of authority.
  - Completion, accepted releases, and independent approval are outputs of the protected
    acceptance operations. They are not fields the worker may set.

  A handoff preserves actual source and evidence and links the issue that owns continuation;
  it does not create a new prerequisite or release the agent from continuing authorized work.
- **Reports identify the actual result and remaining work.** Distinguish completed implementation,
  engineering checks and independent acceptance. State an unavailable operation and its exact
  error when it blocks work. Use [`JOURNAL.md`](JOURNAL.md) for substantive implementation
  records and `HANDOFF.md` for source and evidence pointers; neither assigns work or acts as an
  acceptance mechanism.
- **The orchestrator is inside the threat model.** It drifts, exempts itself, and builds
  backdoors into the gates it writes, as any agent does. See `specs/architecture.md`, "The
  orchestrator is inside the threat model", for the holes known now. Do not widen them.

# Roles

You are either the **orchestrator** or a subagent with exactly one role
([specs/architecture.md](specs/architecture.md), "Authors: one role per agent"):
- The orchestrator owns policies, gates, compliance, this repository's kernel and language, the
  leaf contract and, in a controller session during B0 construction, the custodian's controller
  (`custodian/`). The
  launcher assigns the other roles from their independently approved requirements.
- A kernel implementation delegate works within the assigned kernel/contract scope and has no
  independent mathematical or acceptance authority. Delegation does not remove the parent
  agent's responsibility for integration and completion.
- The formalization subagent writes `lean-categories` only.
- The acceptance subagent writes `tests/acceptance/` only.
- The leaf subagent writes leaves only.

No agent writes in two of those roles. `b0-authority` must enforce that separation through
permitted inputs and operations, not a label an author declares about itself. Until the actual
configuration is verified, this is an implementation obligation, not a claim of containment.
Information flows formalization → tests → implementation, never back. The assigned issues supply
the obligations. Dependencies are actual: a governance node blocks only the work whose correctness
or authorized acceptance depends on it, and a blocked item names that dependency (policy 5).
An approved objective delegates its implementation; owner escalation is for a change of requirement or
authority only (policy 2). Review is independent, informed and correctable (policy 6).

**Owner ruling (2026-10-10).** This separation is a rule about what each agent is permitted to do, not a technical gate on what it is able to do. An agent may hold a credential or tool capable of more (for example the shared GitHub token); it does not use it to write outside its role, and acceptance does not wait on removing such capability. A breach of the rule is a defect in the agent's conduct, recorded and repaired, not an argument that `b0-authority` is unreachable.

**No downstream authorship of upstream mathematics (architecture.md, "B0 policies", policy 1).**
A kernel worker consumes an accepted mathematical release. It writes nothing in `lean-categories`,
its registry schemas, validators, probes and admission rules included, and it commissions no
upstream work with kernel-generated goals, acceptance failures, desired row arrangements or
instructions for making a tactic succeed. Upstream work starts from an independently approved
mathematical requirement and its sources. The author uses only its role's permitted inputs and
operations, even when shared credentials or tools can do more (owner ruling, 2026-10-10).
A breach is recorded and repaired as conduct; removing that capability is not an acceptance
prerequisite. Independently protected acceptance operations remain separate from construction.

# Architecture contract (read first)

**Own-organization delivery consumes the latest `main`** of `lean-categories`,
`lean-cas-dsl-leaf-contracts`, `lean-cas-dsl-leaves` and `lean-jupyter-kernel`. Resolve that
selection explicitly for integration and record the revisions actually loaded. A diagnostic
branch or historical source anchor is not a permanent delivery pin or an accepted release.

The local-development clarification in [#83](https://github.com/dzackgarza/lean-cas-dsl/issues/83)
preserves one dependency selection across
repeated diagnostics and a before/after comparison. Do not refresh dependencies between those
observations or before every local build. Refresh explicitly outside the comparison, then
rebuild affected imports and re-establish the relevant results at that selection. Final
delivery still requires the latest-main combination and its independent acceptance.

[`specs/architecture.md`](specs/architecture.md) owns the separation of concerns:
- `lean-categories` owns all mathematics;
- this repository derives the language from `lean-categories` at its latest `main` and owns no
  ontology;
- leaves only supply opaque computations for operations that are already formal, and nothing
  from a leaf is trusted;
- `research` owns no ontology.

Every plan node and edit conforms to it. In practice it forbids the following.

* **Missing mathematics is an upstream dependency.** If a category, functor, classifier, operation
  or coherence is missing, stop only its dependent operation and record the missing accepted
  input in the existing obligation. The independent upstream author works from the approved
  mathematical requirement and its sources; the kernel worker neither commissions nor briefs it.
  Consume `lean-categories` at its latest `main`. Continue source work that does not require the missing input.
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
  to need a new method, placement, forwarding or edge, record the missing semantic input.
  Its independent upstream author owns any mathematical repair; never invent it in the leaf.
* **The acceptance suite is the only correctness evidence, and `lean-cas-dsl` alone judges it.**
  What can be discharged in Lean is proved in `lean-categories` or discharged generically by the
  kernel; it is never a leaf's.
* **Acceptance assertions are permanent.**
  - Write the expected value from a proof, a citation or an independent oracle before running
    anything. Never take it from the implementation under test.
  - Never edit an admitted assertion because an implementation changed. Add new assertions
    instead.
  - Only an independently accepted upstream correction changes the mathematical assertion,
    with the release that corrects it. A meaning-preserving change of syntax, serialization or
    proof artifact is not a new question; its comparison or migration is independently assessed
    without changing the proposition, expected answer, required execution or assertion inventory.
  - Hashes and role variables are bookkeeping, not admission authority. Construction workers
    never regenerate authoritative records from their candidate's output.
* **Failures stay stratified.** The five kinds are:
  1. semantically invalid;
  2. `NoImplementation`;
  3. unavailable or crashed;
  4. malformed output;
  5. wrong answer.

  An unresolved ambiguity and an internal interpreter error are distinct from all five
  (architecture.md, policy 3): a timeout or exception is never `invalid`. Never collapse one kind
  into another. Never turn a gap into a fallback, a default or a nearby answer.

# Repository boundaries

Missing mathematics is an upstream dependency of its actual consumers. The kernel consumes the
accepted mathematical API and independently fixed questions.

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
- The contract is the kernel's: develop it with the kernel and integrate the compatible source.
  The leaves and this repository build against its latest `main`.

# Search before choosing an implementation boundary

Follow CC-REUSE and CONTRIBUTING's behavioural policies. Frame the question around the required
capability and its downstream uses, then inspect Lean, installed dependencies and relevant
reference implementations. Searching for a library that reproduces the current reader's entire
combination of responsibilities does not establish a need for bespoke code. Ordinary term
formation, binding and substitution must use Lean's elaborator and term machinery; mathematical
selection and comparisons remain explicit.

Mathematical definitions and proofs retain their upstream ownership and formalization-corpus
research requirements. Record consequential reuse decisions and concrete contract gaps in the
existing owning reuse files. Do not introduce a new node or research artifact for each repair.
Categories, functors, natural transformations, whiskering, pasting, adjunctions and limits retain
their accepted mathematical owners; the kernel does not author a second calculus of them.

# Scratch and worktrees stay outside the repository

`.tmp/` holds only `.tmp/harness.json`, written by `just harness`. Experiment binaries, object
files, logs and probe copies go in the session's scratch directory, never in the repository. A git
worktree is created outside the repository (`git worktree add ../lean-cas-dsl-<branch>`) and removed
with `git worktree remove` once its branch is merged. Failure of record: 2026-10-10/11, 2.3 GB of
saved harness executables, logs and worktrees with full Lake package copies left in `.tmp/`.

# Builds and checks

Follow [Construction and verification](specs/computational-core-plan.md#construction-and-verification).
Obtain completed Lean diagnostics for the actual edit, build the changed module when a consumer
needs a fresh artifact, then run the relevant original question through the production path.
Use the available persistent Lean server or targeted compiler/build commands. Reuse unchanged
artifacts and keep dependency selection fixed within the comparison.

Preserve the original question, prerequisite bindings, imports, shared execution context and
budgets. A reduced diagnostic can locate a defect; it cannot replace the required original
computation. Retain the relevant ambiguity, distinct-producer, comparison, ownership and
hostile-reply controls required by the assigned issue.
Do not raise heartbeats, fabricate the state under test, or weaken an assertion to obtain a pass.

Local feedback does not wait for publication or CI. Source checkpoints may be red when stated
accurately; they do not complete the obligation. Full combined compilation, public interfaces,
notebook execution, required real-engine workflows and independent acceptance remain delivery
requirements. An existing useful compiler/runtime loop is sufficient to resume implementation;
no new persistent workspace, recovery demonstration or tooling programme is required.

For documentation-only changes, inspect the affected text, links and consistency; do not run a
Lean build. Engineering checks and source inspection establish only their actual properties,
not independent mathematical acceptance.

<!-- agent-memory:start -->
# Agent memory

This repository uses the central agent memory vault at `/home/dzack/.agent-memory-vault`.

Project memory key: `projects/github.com__dzackgarza__lean-cas-dsl/index`.

Repository `.agents` and `.hermes` paths are symlinks to the same vault-owned project directory.

When the existing vault is available, search project and global memory for relevant history:

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

The assigned issues contain the current work decisions. Memory is supplementary context;
an unavailable vault or an absent plan card does not block authorized work or create another
planning deliverable. Verify decision-critical historical claims against their primary sources.

Use `agent-memory retrieve <key>`, `agent-memory update <key>`, and `agent-memory delete <key>` for memory CRUD.

The vault should be committed at all times. Treat staged or unstaged vault changes as an ephemeral error state. Before normal memory work resumes, load the bundled vault-maintenance skill with `agent-memory maintain skill vault-maintenance` and follow its referenced check, repair, and commit workflows.

Move reusable lessons during maintenance with:

```bash
agent-memory maintain move <key> --to global/advice
```
<!-- agent-memory:end -->
