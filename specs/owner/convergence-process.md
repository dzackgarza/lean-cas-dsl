# Convergence process (owner text, verbatim, 2026-09-30)

This file is the owner's text, quoted without edits. No agent edits this file. A proposed change is
written elsewhere and cites this file; it takes effect only when the owner accepts it. It controls
`specs/computational-core-plan.md`: where the two disagree, this file wins, and the plan is wrong.

---

So what is the correct path to force the orchestrator to follow to converge
Force it through a bounded architecture-construction process whose acceptance it cannot redefine. “Keep improving the repos under these policies” leaves exactly the discretion that produced the thrash.
I would impose this sequence:

1. Freeze feature expansion and fix the convergence target

The target is a minimal extensible system in which the historical bad moves are unavailable. Stop expanding mathematical coverage, production leaves, notebook features, and passing examples except where a specimen distinguishes two architectural designs.
An owner-approved contract fixes the required invariants, legitimate extension forms, and stopping conditions. The orchestrator may propose changes to that contract; it cannot silently adopt them or replace a difficult obligation with an easier one.

2. Design the permitted extension language before adding more implementations

Specify exactly what each contributor can submit:

* Formalization: mathematical objects, constructions, operations and their required structure
* Kernel: generic interpretation of those structures
* Acceptance: independently justified mathematical assertions
* Leaf: realizations of already specified computational requests

For each historical failure, identify which authority made it possible and remove that authority from the relevant interface. A leaf-facing “declare parent category” field is already the wrong design if the category should follow from the construction. Rejecting known bad parent names would miss the point.

3. Make independence a structural property of the kernel

Semantic interpretation must consume the accepted mathematical release and expression, without consulting installed leaves, backend capabilities, or their Lean instances and imports. Realization selection happens after the semantic judgment is fixed.
Then require explicit arguments for these properties:

* Replacing every leaf leaves expression meanings, types and available operations unchanged
* Adding an applicable generic operation upstream requires no old-leaf edits
* Changing presentations preserves semantic identity through the specified transport
* Ambiguity cannot be resolved by installation order or implementation convenience

Where these follow from types, module boundaries or a small formal argument, establish them there. Example tests supplement that argument; a collection of green examples cannot replace it.

4. Use specimens to expose missing generic machinery

Use a small, deliberately varied set: distinct structures on the same carrier, two presentations related by a nonidentity isomorphism, competing structural paths, and a construction requiring a result to be lifted back.
When a specimen fails, the orchestrator must identify the missing generic contract or interpretation rule. It must not repair the specimen by forwarding methods, introducing a domain-specific kernel case, weakening the assertion, or extending its own exemption list.
A missing computation is allowed. Losing or changing the mathematical meaning is not.

5. Separate authorship by actual inputs and authority

Formalization receives the mathematical requirement and sources. Acceptance receives the accepted mathematics and language specification. Leaf implementation receives the released computational contract. None receives downstream implementation details to shape its own deliverable.
The orchestrator coordinates these stages but cannot supply the expected answers, rewrite another stage’s deliverable, or count its own review as independent acceptance. Quarantined cross-layer work cannot become trusted merely through a new pin or role label.

6. Require an independently chosen extension as the exit test

After the kernel and interfaces are fixed, a fresh contributor introduces a new mathematical extension using only the permitted contract. Another adds a generic operation applicable to objects that already exist.
The decisive observation is whether the existing kernel derives the consequences without new special cases and whether old leaves remain untouched. Repeat across the distinct extension mechanisms the architecture claims to support, rather than accumulating more examples of one easy mechanism.

7. Protect acceptance of the trusted core, not every downstream edit

The orchestrator can implement and propose kernel changes. It cannot also alter the rules judging that change and declare it accepted. The evaluator, validators, semantic-release admission, and mathematical acceptance meaning need a protected acceptance boundary. Ordinary leaf development should remain cheap and autonomous.
Convergence means the agreed extension mechanisms work compositionally, the historical workarounds cannot be expressed through downstream interfaces, and an independently authored extension demonstrates that no new global repair obligations are created.
There remains a small trusted core whose design needs intelligent review. The achievable guarantee is that routine growth does not repeatedly reopen that core. If each new mathematical example requires the orchestrator to negotiate another kernel exception, the process has not converged.
Two safeguards make that path non-vacuous: fix the positive capabilities the architecture must support, so “reject everything difficult” cannot count as containment; and require a compositional justification for the permitted extensions, so passing hostile examples cannot count as a universal guarantee.
The orchestrator must also be allowed to conclude “this obligation is inconsistent or still unsolved.” It must not be allowed to resolve that situation by quietly changing the obligation. That is the essential constraint: a fixed problem it cannot redefine, with explicit authority required to change the problem.
