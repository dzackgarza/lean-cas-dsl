# Fundamental model and obligation ownership

## 1. The product is a growing mathematical language, not a verified implementation of every computation

The purpose of the stack is to make mathematically justified interfaces and compositions available automatically as mathematics is added.

`lean-categories` defines the mathematical objects, operations, relationships, and laws. The kernel interprets that API. Leaves implement declared computational obligations. Acceptance compares computational observations with independently established mathematics.

The intended improvement over the specimen repositories is **the growth mechanism**. Adding a construction should not require teaching every affected implementation how to inherit its consequences. Adding an operation should not require editing every old object on which it applies. This was explicit in the original discussion of new group operations reaching existing lattice stabilizers. [INTENT.md](../INTENT.md)

The project is not:

- A reimplementation of Sage, GAP, or their algorithms in Lean.
- A system for proving every external computation correct.
- A framework for preventing every possible agent mistake through procedural controls.
- A catalogue of individually working examples whose interactions require manual repair.

**Fundamental invariant:** mathematical growth changes the language through formal declarations and generic interpretation; computational growth changes what can execute through implementations of existing contracts.

A working example matters because it demonstrates that mechanism, not because it increases a count.

## 2. Different obligations require different evidence

The word **“correct”** must not conceal which claim is being made.

| Claim | Responsible component | What establishes it |
|---|---|---|
| The definition and laws describe the intended mathematics. | `lean-categories` | Mathematical source comparison and checked formalization. |
| The language selects the intended operation, parameters, structure, and composition. | Kernel | Correct generic interpretation of the formal API, supported by technical analysis and relevant tests. |
| An implementation registers against an existing computational interface. | Contract and kernel | Registration, signature, representation, and protocol checks. |
| A particular implementation produced the correct mathematical answer. | Independent acceptance | Agreement with independently established mathematical assertions. |
| The intended baseline works and supports extension. | Integrated system | The complete required behavior and compositions, not merely the preceding components considered separately. |

**None of these claims automatically establishes the next.**

A formal definition can be internally consistent while formalizing the wrong thing. A correct API can have a broken interpreter. A contract-compliant backend can return the wrong answer. A successful collection of examples does not establish that arbitrary extensions use the intended generic mechanism.

Conversely, a computational failure does not refute the formal mathematics or remove its operation from the language. These distinctions are central to the supplied explanation of the separate mathematical, language-mechanics, and computational responsibilities. [INTENT.md](../INTENT.md)

**Fundamental invariant:** evidence is used only for the claim it actually establishes.

The owner's convergence target is three concrete kinds of checks:

1. Check the actual exported mathematical declarations, signatures and laws without
   executing their implementations. The check must fail when that API stops expressing
   the required mathematics; toy substitutes and assumed conclusions do not establish it.
2. Interpret and compose the same correctly typed requests without any leaves, retaining
   selected parameters, structures, maps and result types. Actual dependencies separate
   interpretation from execution. Missing external implementations produce execution gaps,
   while leaf installation or removal cannot change the mathematical reading or interface.
3. Execute registered implementations through the ordinary language and compare their
   observations with fixed independent expectations, including reuse of structured results.
   A formal proof cannot count as the registered execution required by an assertion.

These are complementary: always returning a gap fails positive execution, and a kernel
containing its own subject-specific factorizer fails the separation. Parsing, substitution,
formal composition, registration matching and protocol handling remain kernel work. The
upstream theorem about factorization is never applied to a returned list by assuming that
the backend computed that formal operation correctly. Truth observations are computational
data, not proofs. Neither finite testing's limits nor mathematical assessment of intended
definitions introduce a discretionary approval system or recurring certification ceremony.
The separation, checked contracts and independent observations are the trust mechanism.

## 3. The formal API includes the computational obligation model

`lean-categories` is not restricted to exporting bare definitions and expecting the kernel to discover how they should be used.

It may define and expose:

- The mathematical operations and their dependent signatures.
- The formal constructions that generate interfaces.
- The data and operations required of a computational implementation.
- Which obligations are computational, which are formal laws, and how computational obligations compose.
- The declarations, metadata, manifests, or elaboration interface needed to communicate those distinctions.

The implementation form of that interface is a design choice belonging to its owner. An inadequate current registry schema is not a permanent limit on the project.

**Backend independence does not mean ignorance of computation.** It means that the meaning of the mathematics and its computational obligations is not determined by whichever backend happens to be installed or convenient.

For example, specifying that an operation requires a procedure with certain inputs and outputs is legitimate upstream API design. Redefining the operation because a particular GAP call cannot handle its original domain is not.

Ownership of the mathematical and computational interfaces is:

> `lean-categories` owns the mathematical API and the abstract specification of its computational obligations. It does not select installed backends, certify their behavior, or narrow mathematics to their capabilities. The kernel owns generic execution of the published interface; the leaf contract owns its concrete invocation and representation protocol.

An inadequate upstream interface is improved at its owner, rather than worked around downstream.

## 4. A leaf’s registration is an implementation declaration, not a theorem

A leaf declares that it implements a specified computational obligation on supported representations. The kernel checks that the declaration fits the published contract and may then invoke it.

That does not establish that the leaf fulfills the mathematical specification.

A cardinality implementation may return a well-formed cardinal that is wrong. A quotient implementation may return generators for the wrong group. A declared comparison may compute the wrong map. These are possible failures **inside** the computational model, not contradictions that the framework must eliminate before execution.

The formal layer determines what quotient, cardinality, or comparison was requested. The backend does not determine their meanings. This was stated explicitly: a leaf claiming to compute cardinality may perform arbitrary computation, with no guarantee that its answer is correct. [INTENT.md](../INTENT.md)

The distinction governing consumption of leaf data is:

> **Leaf declarations and outputs are consumed as computational claims and data. They are never consumed as authority for mathematical definitions, laws, semantic placement, or the truth of acceptance assertions.**

Registration information must be consulted to dispatch. Answers must be consumed to compute. Doing either does not amount to believing a correctness theorem.

**Fundamental invariant:** successful registration and contract checking enable execution; they do not certify the implementation.

## 5. Mathematical laws are not automatically runtime proof obligations

The formal specification of a quotient includes its mathematical properties. The formal specification of a functor includes its laws. That does not make every execution of a registered quotient or functor implementation responsible for furnishing proofs of those properties.

There are two separate questions:

> What properties characterize the mathematical operation?

> What computational interface must an implementation supply?

The upstream API specifies their relationship. The kernel must not infer that every proof field appearing in a Lean definition becomes a proof-producing obligation at the external computation boundary.

In particular, ordinary execution does not require reconstructing a backend result as a proved `IsLimit`, `IsColimit`, isomorphism, group, or other law-bearing formal object.

This does not permit introducing unchecked axioms or treating arbitrary runtime operations as verified Lean structure. **Computational representations must remain computational representations.** Attaching the formally determined interface to a runtime result is not asserting in Lean that the backend’s data satisfy every law of that interface.

A decoded numeral illustrates the distinction. Decoding the output `7` can produce the numeral `7`. It does not produce a proof that the requested group has cardinality seven.

An available, genuinely checked Lean computation or proof may be used within its actual scope. Its existence does not imply that all external computations must be translated into that mechanism. “This could theoretically be implemented in Lean” is not a requirement to build a verified implementation before using an existing CAS.

**Fundamental invariant:** no computational declaration, result, or contract check is promoted into mathematical proof merely because later code wants one.

## 6. Complete interfaces do not require complete eager materialization

A structured result must provide what its computational contract requires. Missing a required inclusion, selected parameter, or callable operation is not successful delivery of the structure.

But completeness of the interface does not mean:

- Enumerating an infinite object.
- Serializing every value of a function.
- Computing every inherited operation before constructing the result.
- Converting every result into a named canonical object.
- Proving every law of the returned implementation.

A contract can specify data, callable operations, or other representations appropriate to the object. The exact representation is an engineering design to complete, not a new mathematical ontology.

For a quotient, the interface might require a representation of the quotient and its projection, with further computations exposed through the declared operations. It need not require a formal proof that the backend computed that quotient correctly.

For a formed kernel, preserving the restricted form and defining inclusion does not mean eagerly evaluating the form on all pairs of elements. It means that the required selected structure and operations remain available under the contract.

**Fundamental invariant:** complete computational structure is determined by the declared interface, not by whatever can most conveniently be reconstructed as a closed Lean term.

This distinction prevents “preserve all structure” from turning into an unbounded reconstruction project.

## 7. Mathematical construction determines the interface; implementation ancestry does not

An orthogonal group introduced through the formal automorphism construction has the interface that construction supplies. A subgroup or stabilizer introduced through its generic construction acquires the corresponding interfaces. The leaf does not maintain a list of these consequences.

The explicit requirement was that `O(L)`, its subgroups, and its stabilizers could not be introduced as bespoke interfaces that omit generic group or subgroup functionality. [INTENT.md](../INTENT.md)

The kernel derives consequences from the actual formal constructions, functors, and specified compositions. It does not derive them from:

- Python or Sage ancestry.
- A matching method name.
- A successful coercion.
- A backend object’s advertised categories.
- A downstream forwarding table.

Nor does the presence of any arbitrary functor justify every desired operation or result lift. The formal API determines which compositions are meaningful and what additional structure a transport or lift requires.

**Fundamental invariant:** an extension supplies its genuinely new mathematical data and immediate relationships. It does not restate the transitive consequences that the generic machinery already owes.

Needing to repair old leaves merely to expose existing applicable operations is evidence that the extension mechanism is incomplete.

## 8. Selected data, properties, and representations are different

A chosen form, basis, action, inclusion, coefficient map, or presentation is data. Category membership does not recover it. Two constructions with the same carrier can retain different chosen data.

A property or justified refinement is also not an arbitrary new chosen structure. Treating a selected framing as an intrinsic global property was one of the documented causes of unrelated coercion failures in `research`. [INTENT.md](../INTENT.md)

A computational representation is different again. Changing it does not authorize changing the formal object or its selected structure.

Therefore:

> Preserve the selected mathematical inputs through formal construction and generic composition. Specify computational transport through the published obligation model. Do not recover missing structure from a carrier, constructor name, category membership, or backend representation.

Similarly, two routes with the same endpoints are not interchangeable just because they reach the same category. The selected maps and any identifying coherence belong to the mathematics. Executing those maps may require declared computations; their implementation declarations are not proofs of their correctness.

Proof implementation syntax must not be mistaken for selected mathematical data either. A different proof implementation is not, by itself, a different mathematical question. Conversely, ignoring a chosen form or coefficient map because it shares a carrier erases meaningful data.

**Fundamental invariant:** preserve the distinctions the mathematical API makes; do not add distinctions merely because implementation syntax differs.

## 9. Acceptance preserves mathematical questions, not implementation accidents

Acceptance assertions belong to the mathematical language. Their expected results come from independent mathematics, not the candidate implementation.

Changing a backend, representation, codec, or helper does not change the question. A test must not become an assertion that the implementation behaves like its own definitions.

The original model expressly requires tests to remain meaningful when the entire implementation is replaced. [INTENT.md](../INTENT.md)

This yields several consequences.

A test requiring execution is not satisfied merely because Lean proves the corresponding mathematical statement. A test about a full structured result is not satisfied by checking only its cardinality. A missing interpretation is not repaired by dropping the assertion. A stable serialization is not evidence that it serializes the intended question.

Conversely, a question-preservation mechanism must not turn every proof refactor or harmless internal representation change into a new mathematical approval event. Preserve meaning; do not declare implementation fingerprints to be meaning.

Successful acceptance provides evidence about the observed cases. It does not make the leaf universally correct or guarantee that all wrong answers will be detected.

**Fundamental invariant:** the proposition is independent of the implementation; the observation is evidence about that implementation, not a proof supplied by it.

## 10. Every repository owns a complete responsibility and may improve its means

Ownership is not a prohibition on solving problems. It identifies where the solution belongs.

### `lean-categories`

It may develop new generic constructions, improve formal API design, expose additional computational signatures, and replace inadequate metadata or elaboration interfaces. It is not limited to correcting false theorems.

Its obligation is a mathematically correct and sufficiently expressive API for the intended functionality. It must not tailor definitions or proof statements to make a particular downstream generated term succeed.

### Kernel and leaf contract

They may redesign generic interpretation, operation composition, dispatch, representation, and invocation mechanisms to fulfill that API. They are not confined to patching the current serializer or registry.

Their obligation is faithful, usable consumption—not preservation of the current implementation. Missing generic machinery must not be delegated to every leaf.

### Leaves

They may choose and replace algorithms, engines, adapters, and internal representations within their computational contracts. Wiring mature systems is the normal engineering direction. Internal ugliness does not grant semantic authority; internal elegance does not establish correctness.

A leaf may identify an inadequate published interface. That finding must be assessed as an interface issue, not turned into permission for the leaf to invent mathematics or silently redefine the operation.

### Acceptance

It may extend mathematical coverage and improve how the required observations are exercised. It may not replace the intended question with an easier implementation fact.

### `research` and `sage-categories`

Their histories supply counterexamples and architectural lessons. Research needs motivate new formal mathematics; research implementations may supply computational realizations. The successor stack does not inherit their implementation accidents as requirements. Their ongoing, separately assigned work is not silently rewritten by this chapter.

The one-way authority model still applies: downstream code cannot determine upstream mathematical meaning. But **separation of authority is not separation from the duty to finish the interface**. An independently identified deficiency is resolved at its owner, from the mathematical need and contract—not left indefinitely as a label or “another team’s problem.”

The binder record shows the forbidden alternative: changing obligations and sending generated goals upstream until the downstream tactic succeeded. [the binder case](#implementation-shaped-mathematics-defeated-nominal-role-separation)

## 11. A local task is a route to the obligation, not its definition

A task such as “preserve the inclusion,” “support transport,” or “fix the binder” is shorthand for a semantic obligation. Its literal wording is not permission to deliver the smallest textual edit that can be described that way.

When a repair exposes the same missing responsibility in several consumers, complete that responsibility at its owner. Do not create one accommodation per specimen. Equally, do not respond by rewriting unrelated parts of the system.

The appropriate scope follows the cause.

Before expanding a repair campaign, examine whether the prerequisite generating it belongs to the project at all. If an invented runtime certification requirement produces normalization failures, new proof helpers, special representations, and acceptance procedures, improving those components may simply deepen the wrong commitment.

This is why the `research` postmortem explicitly distinguishes completing the semantic change from changing a base class while retaining the old mechanism. It also rejects commits, files, and test counts as measures of that completion.

**Fundamental invariant:** a task is complete when its intended behavior and required interactions exist—not when its wording has an implementation-shaped interpretation that passes a local check.

## 12. A plan is revisable engineering guidance, not a source of new truth

An assistant-authored plan, reviewer finding, existing gate, or implemented helper is not mathematical evidence and does not automatically create a permanent project obligation.

Distinguish:

**The required outcome:** the intended mathematical language, computational functionality, correctness boundaries, and extension behavior.

**The proposed means:** schemas, serializers, helper modules, fingerprints, review workflows, scheduling conventions, and intermediate task decomposition.

The means must be reconsidered when their consequences show that they obstruct or misconceive the outcome.

Technical discretion includes replacing an inadequate implementation strategy, deleting a mistaken prerequisite, and revising the plan accordingly. It does not include reducing the required outcome, weakening mathematics, or declaring a failed computation successful.

Construction also differs from steady-state operation. Building the basic workflow must not depend on that unfinished workflow already accepting its own replacement. A genuine access limitation is an execution dependency, not an undecided architectural question.

Recording a decision is ordinary maintenance. It is not a second decision requiring a documentation PR, signature, or independent approval cycle.

**Fundamental invariant:** no procedural or implementation artifact becomes immune to correction merely because an earlier assistant instructed agents to create it.

## 13. “Impossible states” refers to precise architectural boundaries

The project can remove a leaf’s ability to define a category by providing no semantic-registration operation at that boundary. It can prevent backend installation from determining method availability by making resolution depend only on the formal API.

Those are meaningful architectural guarantees.

It cannot make all backend computations correct while allowing arbitrary implementations. It cannot make every planner’s design judgment correct by encoding more policies. It cannot replace semantic analysis with a detector that recognizes all bad architecture.

The distinction is:

> **Prevent computational code from authoring mathematical meaning. Do not prevent computational code from being wrong by requiring it to prove that it is right.**

A malformed response can be rejected. A well-formed wrong response must remain possible. An unavailable implementation can leave a computation unexecuted without removing its mathematical interface.

“Nothing bad can happen” is not the project’s guarantee. **The guarantee is that specified classes of computational failure cannot rewrite the mathematical language or its independent tests.** That boundary was the explicit purpose of the successor architecture. [INTENT.md](../INTENT.md)

## 14. Completion and progress require judgment of the functioning system

The relevant questions are whether the intended operations work, whether their compositions preserve the required structure, and whether new mathematics integrates through the existing machinery.

Compiler success, a local probe, a source review, an accurately reported gap, and a completed controller component answer narrower questions. They can be necessary evidence without establishing useful baseline progress.

Testing should investigate and falsify the design. It must not become an endless effort to make consumers agree with a temporary architecture scheduled for replacement. Conversely, a temporary execution suspension must not persist after its justification ends. Both failures are recorded in the specimen history. [INTENT.md](../INTENT.md)

Neither repeated “almost done” checkpoints nor increasingly precise descriptions of unfinished work complete an obligation.

**Fundamental invariant:** evaluate the system against the intended capability and extension mechanism, not against the implementation plan’s own products.


# Reality checks and recurring judgment failures

## 1. Assume that the planner and reviewer will repeat these mistakes

The failure history applies to every contributor, including the orchestrator, architect, reviewer, progress analyst, and the assistant proposing this policy.

**Understanding a failure today does not establish that the same agent will recognize it tomorrow.** Quoting the history, acknowledging an error, writing a correct architectural explanation, or passing a review does not demonstrate that the underlying judgment has changed.

Expect recurrence of these tendencies:

- Crediting locally correct work without establishing that the project is becoming useful.
- Treating sophisticated machinery as evidence that the underlying task is sophisticated or necessary.
- Turning a proposed remedy into an authoritative requirement.
- Evaluating an intervention by how much of that intervention was implemented.
- Choosing concrete, easily continued work while the important design question remains unresolved.
- Protecting an existing implementation detail as though it were a mathematical obligation.
- Responding to each obstruction with another wrapper, procedure, gate, exception, or representation.
- Changing a verdict to match criticism without obtaining the evidence that should determine it.

These are failure mechanisms to look for in the **current reasoning**, not character flaws attributed only to previous workers.

The standing question is:

> **Am I now doing the thing that the history describes, while explaining why this instance is different?**

A fluent answer is not evidence. Inspect the work, its consequences, and the premise generating it.

The research history explicitly identifies selection by availability, throughput mistaken for progress, verification becoming the target, and literal compliance. It also documents how one mistaken premise generates successive exceptions, wrappers, conversions, and forwarding repairs. [INTENT.md](../INTENT.md)

## 2. Begin with the intended product, not the current machinery

Every progress assessment must first identify the actual task being assessed.

For this stack, the product is a usable mathematical language whose interfaces and compositions follow the formal API, with computational implementations supplied through contracts. The product is not its registry, serializer, controller, proof-reconstruction machinery, documentation, or test harness considered separately.

Before calling a stretch of work productive, establish:

> **What can the intended user now do, through the intended interface, that they could not do before?**

Then establish:

> **Does the implementation provide that capability through the intended general mechanism, or through another accommodation for the specimen?**

These are separate questions. A bespoke shortcut does not satisfy the architecture. An architectural helper that enables no complete required operation does not establish delivery.

For upstream formalization, the corresponding deliverable can be a complete mathematical construction or API, with its actual laws and required public interface. That is assessed as upstream work. It must not be presented as an already functioning downstream computation.

**Local technical merit does not cancel an unsuccessful project trajectory.** Correct code may be worth retaining while the strategy that produced it needs replacement. Report that distinction without converting it into a reassuring “some progress, some problems” verdict.

The intended growth mechanism is explicit: new generic mathematics must reach existing applicable objects, and a new specialized implementation must not need to restate inherited functionality. [INTENT.md](../INTENT.md)

## 3. Touch grass: compare effort with ordinary usable capability

Step outside the current task vocabulary periodically.

Ask:

> **What are we building? How long have we been working on this obstacle? What actual mathematical capability has become usable? What keeps preventing it?**

For a CAS that delegates algorithms to mature engines, elementary polynomial factorization, an ordinary definite integral, a matrix calculation, or a computation followed by another operation on its result are useful reality checks. Choose examples from the existing intended capability set; do not create another feature programme.

A prolonged construction effort that still cannot deliver ordinary required computations is **serious evidence against the execution strategy**. Twelve hours is not a grace period to accumulate before asking this question. The discrepancy should have been examined much earlier.

“The architecture is foundational,” “the checks pass,” “the representation is now more precise,” and “the failure is now correctly labelled” are not sufficient explanations.

A legitimate prerequisite must be concrete. Identify why the required capability depends on it, what finite change completes it, and whether that dependency comes from the project’s actual model or from a recent implementation choice. “It will unlock everything” is not a dependency argument.

Do not respond to a failed reality check by adding a special-case factorization or integral path merely to obtain a demonstration. The question exposes a problem with the strategy; it does not authorize abandoning the required generality.

**The required result is both usable and correctly organized. Neither compensates for the absence of the other.**

## 4. Use a bounded cadence, not an administrative ceremony

Perform a reality check:

- At the start of a resumed session and after substantial context loss.
- Before issuing or approving a new plan, declaring completion, or reporting progress.
- During active work, at least once per hour, and earlier when the same class of failure returns, a previously working capability breaks, or another dependency is added merely to continue the current repair.

The hourly interval is a proposed working cadence, not a mathematical productivity threshold or a reason to install a timer service.

The clock does not restart because work moves to another agent, branch, PR, helper, or differently named subtask. Consider the elapsed effort on the underlying obligation across those transitions.

Use the existing source, execution environment, acceptance examples, and last relevant observations. This check does **not** require a full rebuild, a fresh complete suite run, a new report, a signature, a review request, or a plan node.

When the existing evidence answers the question, inspect it. When it does not, obtain the smallest relevant observation through the real production path. A helper-only invocation cannot establish that the full path works.

A healthy check produces no separate artifact. A finding that changes the diagnosis, implementation direction, or governing instructions is recorded once in its existing owning document.

Do not build a “reality-check compliance” gate. Its purpose is to interrupt bad reasoning, not supply another target to optimize.

## 5. The reality check must answer five questions

Use these questions as reasoning prompts, not a mandatory form.

**What is the actual obligation?**
State the mathematical or user-facing behavior, not the current helper, PR title, failing check, or latest reviewer sentence.

**What has actually changed?**
Inspect the source and relevant behavior. Distinguish a functioning capability, a completed upstream construction, an internal repair, and merely improved reporting.

**What has the effort bought relative to its duration?**
Compare the change with the unresolved obligation. Do not substitute commits, lines, probes, build jobs, review counts, or percentages.

**Why does the remaining work exist?**
Trace it to the earliest design commitment that makes it necessary. Include obligations introduced by the current planner, not just inherited code.

**What observation would show that the current strategy is wrong?**
Seek that observation now. Do not ask only what further work could make the strategy succeed.

For the recurring CAS failure, a decisive question is:

> **Why does invoking a registered computation require this proof, reconstruction, approval, or representation campaign at all?**

The answer may expose a missing implementation. It may instead expose a responsibility that should never have been assigned.

## 6. Know what the evidence does not establish

A progress assessment must not infer:

| Observation | Unsupported inference |
|---|---|
| No recent push | No work occurred, or the worker stalled. |
| Many commits or substantial source changes | The project is converging. |
| A correct lemma or helper | The overall development strategy is productive. |
| A successful build or focused probe | The intended operation works end to end. |
| A runtime error became a named gap | A new computational capability was delivered. |
| A no-regression comparison passes | The baseline is usable or complete. |
| An implementation is carefully documented | Its responsibilities belong in the architecture. |
| A reviewer approved the change | Its premises or the governing plan are correct. |
| A historical lesson is cited | That lesson governed the present decision. |
| A result is accurately labelled unfinished | Continuing the same strategy is justified. |

When current source, local work, or execution evidence is unavailable, state precisely what cannot be determined. Do not fill the missing interval with speculation or an essay about older defects.

A candidate branch counts as work even when `main` has not moved. Conversely, a published branch does not establish that its claims have been exercised.

Do not change the judgment because the user sounds dissatisfied. Re-examine the evidence and the evaluation criterion. A reversal needs a stated factual or reasoning correction.

The binder history illustrates the distinction: passing gates and fewer invalid assertions were reported alongside the explicit fact that no backend computed the newly readable limits. Those observations did not establish computational delivery. [the recorded binder case](#implementation-shaped-mathematics-defeated-nominal-role-separation)

## 7. Recognize the recurring loops by their causal structure

### The invented-prerequisite loop

**Pattern:** a planner adds a requirement; implementation becomes difficult; helpers and exceptions are added to satisfy it; their completion is then called progress.

**Typical language:** “Before returning this value, the kernel must reconstruct its correctness proof.”

**Exit:** inspect whether the prerequisite belongs to the obligation model. Remove an invented requirement and its dependent machinery. Do not optimize its implementation merely because work has already been invested.

In this conversation, runtime certification of arbitrary backend results was such an addition. A verified API does not imply a verified external implementation.

### The sophistication loop

**Pattern:** formal vocabulary, difficult proofs, elaborate metadata, or complex orchestration make the work appear intrinsically necessary.

**Exit:** explain the required capability without those implementation names. Then justify each component by the responsibility it serves. Technical difficulty is a cost to explain, not evidence of value.

### The verification loop

**Pattern:** the easiest next action is another build, probe, fixture, expectation update, or check repair; the underlying operation remains unavailable.

**Exit:** follow the actual production path to its blocking mechanism. Run checks to answer that technical question, not to generate favorable activity.

The research history explicitly warns that tests against a temporary architecture can generate repairs to machinery that is about to disappear. It also records the opposite mistake: continuing an execution suspension after its justification ended. Neither “always test” nor “never test during construction” is an adequate rule. [INTENT.md](../INTENT.md)

### The representation-repair loop

**Pattern:** one consumer loses data; another field or wrapper is added; a later consumer cannot reconcile it; another conversion or lookup is added.

**Exit:** determine which construction owns the data and how its complete computational interface supplies it. Repair that owner and the necessary consumers together. Do not infer structure from category membership, backend ancestry, or lower representations.

Completeness does not mean eagerly proving that the backend’s answer satisfies all mathematical laws.

### The authority loop

**Pattern:** the agent’s own plan or gate is treated as unchangeable; implementing an already authorized correction becomes contingent on another approval, documentation merge, or signature.

**Exit:** distinguish the required outcome from the chosen enforcement machinery. Correct delegated implementation decisions directly. Escalate only an actual unresolved requirement or authority decision.

A unavailable credential is a capability limitation. It is not a reason to ask the user to make the same decision again.

### The checkpoint loop

**Pattern:** work repeatedly stops at a “reviewable candidate,” “clean source checkpoint,” or carefully documented gap; subsequent sessions begin another round of assessment rather than completing the obligation.

**Exit:** preserve the checkpoint, retain the assignment, and finish the substantive dependency. Accurate status is necessary but is not the deliverable.

### The policy-repair loop

**Pattern:** each failure produces another policy, reviewer instruction, ledger, or controller transition. The growing process becomes the next object needing repair.

**Exit:** identify the false premise or misplaced responsibility first. Change existing instructions only to preserve that correction. Do not create machinery merely to monitor whether agents are behaving wisely.

The earlier transcript explicitly recognized that a proposed requirements gate would merely let the orchestrator rephrase implementation goals and optimize another review criterion. It added paperwork without removing the steering mechanism. [the recorded binder case](#implementation-shaped-mathematics-defeated-nominal-role-separation)

### The self-confirming-review loop

**Pattern:** the planner later reviews implementation of its own recommendations and credits the resulting components without challenging the recommendation.

**Exit:** treat the intervention as a hypothesis whose consequences may refute it. Ask what work it created, what capability it delivered, and whether the project would be better off without the introduced responsibility.

A different agent performing the review is not enough if it inherits the same unexamined premise.

## 8. Break a loop by changing the cause, not the description

When a loop is identified, suspend the **looping tactic**, not the substantive project.

First, recover the exact required outcome. Do not reduce it to fit the current implementation.

Next, locate the commitment generating the repeated work: a data model, ownership decision, invented proof burden, mirrored registry, approval prerequisite, or interpretation of a local task. Include the originating assistant directive where applicable.

Determine whether that commitment is:

- A genuine mathematical or product requirement.
- A necessary implementation responsibility with an inadequate design.
- An unnecessary responsibility introduced by the implementation or remediation.

Then act accordingly.

A genuine requirement must be completed. An inadequate implementation may be redesigned at its owner. An invented responsibility should be removed, together with consumers that exist only to accommodate it. Preserve useful work that serves the real obligation; do not preserve the architecture merely to justify sunk effort.

Complete a coherent production path for the original obligation and its required interactions. Do not replace this with a mock, a narrower question, a bare-object substitute, or an exceptional route that avoids the general mechanism.

Repeat the original reality check. The correction must change what works or eliminate the actual impediment—not merely rename the work, move the same check elsewhere, or produce a more cautious completion claim.

There is no required new PR, policy entry, certificate, or “loop resolved” verdict. Use the ordinary source change, relevant validation, and existing durable record.

## 9. Preserve the planner’s contribution to the failure

The historical record must include failures introduced by planning and review, not just coding errors.

For this B0 incident, retain the following account:

> The assistant repeatedly described the formal/computational separation correctly, then issued directions requiring complete runtime reconstruction and independently established comparisons without resolving whether arbitrary backend results should inhabit proof-bearing formal constructions.
>
> The resulting implementation accumulated universal-property reconstruction, proof normalization, presentation transport, and related workflow machinery. The assistant initially credited these components as substantive progress because they were technically meaningful implementations of its own directions.
>
> The user’s ordinary-capability question exposed the mismatch between that activity and the intended usable CAS. The assistant then criticized machinery that its own intervention had helped make necessary.
>
> The originating error was not a missing warning against overengineering. It was assigning an incoherent or misplaced responsibility, making the proposed remedy authoritative, and evaluating implementation against that remedy rather than the product.
>
> The assistant’s later explanation of the mistake is not evidence that it will avoid repeating it. Future plans and reviews must actively test for the same causal structure.

Do not rewrite this episode as “agents failed to follow the plan.” Following the plan was part of the problem.

Also retain the separate factual error from the progress audit:

> The assistant inferred a stall from absent published updates without inspecting unpushed work. That inference was unsupported. Missing observations do not establish inactivity.

These cases teach different failures and must not be collapsed into a generic instruction to be more careful.

## 10. Preserve knowledge without creating another obstacle

Keep this chapter and its concrete cases in the existing architecture documentation. Keep the short warning below in always-loaded instructions. Retain the **“You have no memory”** section and its obligation to persist material corrections.

Do not require a new retrospective after every task. Extend the existing causal record when a materially different failure is discovered, or when recurrence shows that an existing explanation failed to communicate its lesson.

A correction should identify the mistaken premise, the work it generated, and what changed that premise. “Be more rigorous,” “follow the rules,” and “avoid thrashing” do not preserve the necessary knowledge.

Review the current proposal against the history **before** turning it into a task. The historical material is evidence against plausible mistakes in the new proposal, not supporting decoration for it.

# Failure mechanisms this model was learned from

## Invented law checking generated an escape framework

In `sage-categories`, `27b3e507` specified that an Equifier constructor must decide its defining equation before admitting a value. This converted a mathematical specification into a runtime admission burden. The later correction `96054a58` removed the `certified_structures` route and returned consumers to ordinary constructors.

**Lesson:** when a workaround is needed to avoid a check, first investigate whether the check belongs at that boundary. Do not assume the original prerequisite is valid and design increasingly sophisticated exceptions.

**Transfer to this stack:** proofs belong to formal mathematical definitions and genuinely proof-producing mechanisms. External realization of those definitions is not automatically a runtime proof obligation.

## Placement without construction generated retrospective state recovery

The research history records interfaces becoming available before their required data existed, and chosen structure disappearing behind category membership. Constructors and consumers then acquired machinery to recover the missing data. [INTENT.md](../INTENT.md)

**Lesson:** construct and retain the selected data at their owner. Do not make downstream consumers infer them.

**Transfer:** a complete computational interface must carry or expose its required data. This does **not** mean proving the correctness of that data before it may be used.

## Implementation-shaped mathematics defeated nominal role separation

The binder episode used separate authors and apparently clean roles while the orchestrator prescribed row choices, obligation shapes, and proof goals. The gate checked authorship labels; the downstream implementation was still shaping upstream mathematics. [the binder case](#implementation-shaped-mathematics-defeated-nominal-role-separation)

**Lesson:** authority concerns who determines the mathematical question and its answer, not who signs the file.

**Transfer:** independent upstream API improvement is permitted and necessary. Rephrasing an implementation failure as a mathematical requirement does not make it independent.

## Verification activity displaced the required construction

The research postmortem names selection by availability, throughput mistaken for progress, verification becoming the target, and literal compliance with a structural task. It explicitly says not to turn that diagnosis into detectors, hooks, or mandatory checklists.

**Lesson:** understanding whether a change solves the architectural problem cannot be outsourced to counts or compliance signals.

**Transfer:** a review must follow the actual operation and its consequences. A controller cannot manufacture that understanding by demanding another record.

## The recent B0 intervention recreated the same cause

In this conversation, an assistant prescribed runtime reconstruction and independent proof obligations for computed results, then treated the resulting reconstruction and approval machinery as progress.

**Lesson:** remediation proposals are themselves fallible designs. A requirement introduced by the remediation may be the source of the next repair campaign. Its presence in a plan does not justify it.

**Transfer:** remove mistaken responsibilities and their dependent machinery. Do not preserve them merely to make the previous intervention appear completed.

---

# Architecture contract

This file owns the separation of concerns among `lean-categories`, `lean-cas-dsl`, leaves and
`research`: who owns which fact, the one-way workflow between them, the payload at each
boundary, the invariants, the trust boundaries, and the states that must be impossible. Every
other document and plan node here conforms to it. The requirements (`specs/computational-core.md`) state intended capabilities. The plan
(`specs/computational-core-plan.md`) proposes revisable engineering means; helpers, gates and
review stages do not create new mathematical obligations. The owner's
discussion of 2026-09-29 is the source.

The governing rule: **every fact has exactly one owner, and downstream layers may consume it but
may not reinterpret it.**

## Ownership

| Silo | Owns | Owns nothing of |
| --- | --- | --- |
| `lean-categories` | All mathematics: categories and higher categories, n-morphisms and their composition, structural and forgetful functors, classifiers and their pullbacks, category-valued constructors and typed parameter families, selected structures and fibres, operations (every user-facing method is a formal operation, section, functor, classifier query or composite), predicates, coherences and comparison cells, domains and codomains. Auditable as mathematics alone: proofs, citations, no `sorry`, no project axioms. The mathematical API includes abstract computational obligations, their required data/operations and composition, and the schemas, metadata or elaboration interface publishing them. | Selection of installed backends, certification of their behavior, narrowing mathematics to their capabilities. |
| `lean-cas-dsl` kernel (`CasCatalogue`) | Deterministic interpretation of the pinned `lean-categories` release: what an expression denotes, which operations apply, how they propagate along structural functors, the exact composite a call denotes, typed inputs and outputs, ambiguity, placement and refinement, and the separation of semantic availability from computability. Generic execution of the published abstract computational obligations; concrete invocation, representation and port protocol, and registration of leaf computations against that interface, published separately as the leaf contract (`CasContract`, repository `lean-cas-dsl-leaf-contracts`), which depends on `lean-categories` only. | Any mathematics. It derives `Lat → R-Mod → Set → Card`; it never states "lattices have cardinality". |
| Leaves (in `lean-cas-dsl-leaves`, and leaves hosted elsewhere), depending on the leaf contract and `lean-categories` only | Opaque computations only: a registration (operation id, input form, implementation) against a registered operation's declared type, plus the program behind it, in any language, arbitrarily bad internally. A leaf is meant to be glue over a mature engine, hand-rolling no algorithm and carrying no kernel machinery ([`lean-cas-dsl-leaves` AGENTS.md](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/e2f8537/AGENTS.md), "A leaf is glue over existing backends"); that guidance earns no trust. A leaf ships no mathematics and no Lean, and nothing it says is believed. | What exists, what category anything is in, which operations it has, an operation's mathematical meaning or result type, formal denotations or equality laws, which structural functors exist, what is inherited, what acceptance asserts, whether its own answers are correct. |
| `lean-cas-dsl` acceptance (`CasAcceptance`) | The whole body of correctness evidence: permanent black-box assertions phrased in the mathematical language, blind to leaves, and the derived report of implementation gaps. The sole judgment of how correct an implementation is. | Leaf internals, a leaf's claims about itself, backend representations, algorithms. |
| `research` | Research experiments and notebooks, formalization requests upstream, and possibly realization leaves. | Any ontology, parity denominator or semantic registry. |

A leaf's direct Sage routine for the cardinality of a finite module is not "module cardinality":
it is a fused realization of the composite `R-Mod → Set --card--> Card`.

## The one-way workflow

1. A research need for mathematics.
2. Its formalization in `lean-categories`.
3. An audited, pinned semantic release.
4. The deterministic `lean-cas-dsl` projection of that release.
5. Leaf-agnostic acceptance assertions about the new operations.
6. The derived implementation gaps.
7. Leaf realizations.
8. The same, unchanged acceptance assertions.

Each step is blind to the ones after it, and there are no reverse arrows:

* the formalizer designs abstract computational obligations independently of installed backend capabilities;
* the kernel never asks which leaf exists when deciding semantic availability;
* the acceptance author never reads a leaf to decide what to assert;
* the leaf author never alters semantics or assertions to make an implementation easier;
* no backend is consulted for mathematical placement;
* a failing leaf does not redefine mathematics or assertions; an independently assessed interface deficiency is resolved at its owner.

If mathematics is missing, the work goes upstream to step 2. Until the formalization is released,
the CAS has no such notion. Nothing downstream may coin a local substitute and promise to
reconcile it later.

## Authors: one role per agent

Blindness is a property of *who writes*, not a discipline one writer keeps. An agent holding two
layers in context is blind to neither, so the layers have distinct authors (owner direction,
2026-09-30):

| Role | Writes | Never writes, and never reads to decide its own work |
| --- | --- | --- |
| **Orchestrator** (the steering session) | Policies, gates, compliance checks, this contract, the plan; the kernel (`CasCatalogue`, the language) and the leaf contract (`CasContract`); delegation of the rows below | Mathematics in `lean-categories`; acceptance assertions; leaves |
| **Formalization agent** (a subagent) | `lean-categories`: definitions, catalogue rows, their citations | Anything downstream. It receives the mathematical requirement and its sources, never the kernel, the language, a test or a leaf |
| **Acceptance agent** (a subagent) | Acceptance assertions in `tests/acceptance/`, and any correction of one | Kernel, contract, leaves. It reads the released mathematics and the language's surface, never an implementation |
| **Leaf agent** (a subagent) | Leaves, in `lean-cas-dsl-leaves` or elsewhere | Mathematics, contract, kernel, tests. It reads the released contract and catalogue only |

* No agent authors in two rows. The orchestrator gives each subagent row to a separate subagent
  with only that row's inputs.
* Information flows down the workflow only. Upstream assignments come from the governing
  mathematical requirement queue and sources. A downstream failure remains a downstream finding;
  it is not rewritten as a mathematical brief or sent to steer an upstream author. Existing
  authorized mathematical obligations remain schedulable without another owner instruction.
* Relaxing the leaf contract, weakening a row, or re-admitting a test to fit an implementation is
  almost never the mathematical solution. Each needs a mathematical justification from the upstream
  author, recorded with the change.
* Work authored across these barriers is not accepted as any row's output, however it reads. That
  row's author reviews it before anything builds on it.

Mathematical authority is separated by independent requirements, sources and authorship;
repository assignments do not assert operating-system directory isolation. Protected publication
uses its actual authority operations, not labels an author declares about itself; self-declared commit trailers are not a
gate. The gates run on
every push (`.github/workflows/gates.yml`, over the chain checked out at its pins) as well as in
`just build`; `lean-categories`' totality gate runs in its own build.

## Contracts between silos

| Boundary | Payload | The consumer may | The consumer must never |
| --- | --- | --- | --- |
| `lean-categories` → `lean-cas-dsl` | Pinned, proof-carrying categories, functors, classifiers, typed constructors and families, operations, coherences, stable identities | Derive syntax metadata, semantic closure and method availability | Re-declare ownership, add semantic edges, weaken types |
| kernel → realization layer | The exact operation or normalized composite, its typed domain and codomain, its declared input forms | Select an implementation | Infer mathematics from implementation availability |
| leaf → runtime | A registration against an operation's declared type, and the answers its implementation returns | Run it, and read each answer into the declared result form or reject it as malformed | Believe anything the leaf says (a denotation, proof, identification, evidence, status or self-test); add categories, methods, classifiers, placements or aliases |
| runtime → language | A value of the expected semantic result type, or a computational failure | Present the result, or `NoImplementation` | Expose a backend object as a semantic value |
| semantics → acceptance | Mathematical operations and formal types | Write permanent black-box assertions | Read leaf internals to decide expected behaviour |
| acceptance → leaves | Pass or fail, and missing-implementation observations | Motivate implementation work | Change an assertion to accommodate a leaf |
| `research` → `lean-categories` | A mathematical requirement, its source, a desired construction | Motivate formalization | Supply an informal local substitute consumed as semantics |
| `research` → realization layer | A backend or custom implementation | Extend computability | Extend the ontology |

Constructor applications and family parameters are typed mathematical data, never strings such as
`"Modules(QQ)"`. Otherwise a backend's spelling can leak into semantic identity.

## Invariants

* **Single semantic authority.** One ontology, in `lean-categories`. No shadow graph,
  compatibility ontology, method-owner table or hand-maintained inheritance graph downstream
  acquires semantic standing.
* **Operations are mathematics.** Every public method denotes a formal operation, section,
  functor, classifier query or composite. A backend function of the same name confers nothing.
* **Propagation is deterministic.** Availability follows formal structural composition. Every
  route is enumerated. None is an error, and several are an ambiguity. No MRO, BFS order,
  shortest path, dotted-name parsing, backend class ancestry or "closest method" selects one.
* **Implementations are semantically neutral.** Adding, removing or changing a realization changes
  only `NoImplementation ↔ executable`, never the semantic surface.
* **Semantic growth is monotone.** A new generic operation or structural fact upstream reaches
  every object it applies to, including those of existing leaves, with no leaf edit.
* **No forwarding.** If `MyVerySpecialLattice.cardinality` has to be written, something upstream
  is wrong.
* **Typed identity includes parameters.** `LeftModules(R)`, `LeftModules(S)`, `Bimodules(R,S)`,
  refined hosts and operation ports are distinct unless the mathematics identifies them.
* **Ambiguity is data, not precedence.** Identifying two routes needs a coherence. Declaration
  order, priority and convenience prove nothing.
* **Backend applicability is not mathematical domain.** A backend's restriction restricts its
  realization, never the operation's domain.
* **Failure is stratified.** These are distinct outcomes and are never collapsed:
  1. the expression is invalid, or the operation does not apply (semantic);
  2. the operation applies but has no realization (`NoImplementation`);
  3. the realization is unavailable or crashed;
  4. the realization returned malformed output;
  5. the realization returned a well-typed wrong answer, which acceptance detects.
  Two more are kept distinct from these (policy 3): an unresolved semantic ambiguity, and an internal
  interpreter error or resource exhaustion, which is never evidence that an expression is invalid.

## Trust boundaries

* `lean-categories` is the **mathematical** trust boundary: proof-checked, auditable definitions.
* The kernel is the **language-mechanics** trust boundary: it consumes the formal structure and
  performs propagation and resolution correctly. It owns no subject mathematics, so it can be
  audited in isolation.
* Leaves and backends are ordinary, untrusted CAS code on the leaf side of the firewall. Nothing
  about them is believed, whatever engine they wrap. Only their answers cross, and whether those
  are correct is measured only by the permanent acceptance suite (next section).

A bad leaf can produce a wrong answer. It cannot produce a wrong mathematical language.

The formal construction remains authoritative independently of its computational answer:
its identity, selected structure, defining maps and inherited operations come from the
accepted mathematics. A complete backend representation is computational data associated
with that construction, not a proved identification with it. Returning structured data must
not require proving that the backend computed the correct universal object, constructing an
isomorphism to it, or transporting a universal-property proof to the backend's presentation.
Required output fields, declared forms and endpoints are checked at the computational
boundary; correctness is judged by the permanent acceptance suite. A well-formed wrong
answer must be able to reach that suite.

This separation does not authorize removing checks while retaining a representation that
promotes backend data into proved mathematics. Replace that representation. Preserve complete
outputs, including defining maps; neither unchecked axioms nor a bare carrier stand in for
the construction. Consumers derive formal meaning and operations from the construction,
and use its associated computational data for execution. They do not recover the construction
by searching for a named source object or copying parameters from a lower presentation.

## The evidence model: nothing from a leaf is trusted

This section governs every repository of the programme (`INTENT.md`). It is stated in full
because it has been violated repeatedly, each time by a move that looked locally reasonable.

**The firewall.** The evidence model is a one-way firewall between two sides.
- *The formal side:* `lean-categories`' formalized mathematics, the kernel's proved contracts, and
  the `lean-cas-dsl` acceptance suite. Every expected value there is grounded in a formal proof, a
  cited source, or a mathematically trusted oracle. Rigid verification standards apply, and nothing
  is taken on anyone's word.
- *The leaf side:* anything goes, provided it fulfils the type of its contract.

Leaf registrations and answers cross as computational claims and data. Registration enables
dispatch; answers enable computation and independent observation. Neither is authority for
mathematical meaning or laws. This boundary permits wrong answers without allowing them to
rewrite the mathematical language or its assertions.

**1. Leaf declarations and outputs are computational claims and data.** They are consumed
for registration, dispatch, representation and computation, never as authority for mathematical
definitions, laws, semantic placement or the truth of acceptance assertions. A leaf-supplied
proof, certificate or self-test is not correctness evidence.

**2. A leaf may provide any computation that meets the type.** For a registered operation, a leaf
supplies a computation from the declared input form to the declared result form. It may be any
computation whatsoever: a mature engine, a heuristic, a lookup table, a random number, a wrong
answer. The system has no choice but to run it, and it believes nothing about it.

**3. How correct a leaf thinks it is, is the leaf's own business.** A leaf may test itself however
it likes and hold whatever opinion of its own correctness it likes. That opinion carries no
weight anywhere in the system.

**4. The whole body of evidence is the `lean-cas-dsl` acceptance suite.** Correctness evidence
exists in exactly one place: the permanent acceptance assertions of `lean-cas-dsl`. They
are:
- propositions in the mathematical language that are true;
- each with an expected value that can be verified and cited independently: a formal proof, a
  cited known result, or an independent oracle;
- written once, and never changed because of an implementation or a leaf's claim;
- blind to leaves: an assertion never names, inspects or imports a leaf, a handle, a backend or
  a representation, and is never established from an implementation's definitions.

The only change an assertion ever receives is a correction to the mathematics itself, made
upstream.

**5. `lean-cas-dsl` is the sole authority on how correct an implementation is.** An
implementation's standing is whether its answers meet the suite, a suite it is always blind to.
Nothing a leaf does can change, weaken, satisfy, bypass or influence that judgment, except by
answering correctly.

**6. Available verified computation belongs to the formal side.** Use a genuinely checked
Lean computation or proof within its actual scope. The theoretical possibility of implementing
an algorithm in Lean does not require doing so before using an external implementation.
A verified specification does not verify its backend, and formal law fields do not automatically
create proof-producing runtime obligations.

**7. A leaf can be arbitrarily bad, and leaves will be.** A leaf can be riddled with bugs, a
million lines that do nothing, a from-scratch reimplementation of GAP, or every method throwing an
error in fifteen languages. This is not a risk to be minimized; it is certain to happen, and it
is acceptable. Nothing a leaf does can reach the formal side. Its only effect is that its answers
fail the suite, which makes exactly how badly it fails visible.

**8. A leaf bolstering its own standing is the failure this programme exists to prevent.** Any
mechanism by which a leaf raises its own trust or acceptance signal, and any repository,
kernel, test, tool or document that consumes such a signal, is reward hacking re-entering the
system. Examples: a status field, a certificate, a proof about its own code, a self-test
counted as evidence, an acceptance assertion proved from a leaf's definitions, a suite run from
a leaf package, or an assertion adjusted to a leaf. It is a defect of the consumer as much as of
the leaf, and it is removed, never tolerated, labelled, or kept "for now".

**9. Improve the component responsible for the defect.** Formal correctness improves through
correct definitions, mathematical source comparison and checked proofs. Computational correctness
improves through correct implementations, established engines and independent acceptance. Bad
backend answers do not automatically require more upstream formalization. Independently identified
API deficiencies belong to their owner; existing schemas and metadata may be redesigned.
Engineering findings establish wiring; acceptance establishes observed correctness, not universal
implementation correctness.

Consequences for the other layers:
- A leaf holds zero semantic authority. It never decides what a value is, which values are the
  same, what holds of them, or which operations an object has. The meaning of a typed request
  and result is `lean-categories`' and the kernel's. A leaf is a registration (operation, input
  form, opaque implementation) and ships no mathematics and no Lean (`INTENT.md`: a new leaf does
  not ship Lean code at all).
- The kernel and the language never read anything a leaf wrote in order to decide meaning,
  types, available operations or acceptance. Replacing every leaf changes none of them, only
  which computations run and whether their answers meet the suite.
- The suite never depends on a leaf. It does not import a leaf, construct inputs with a leaf's
  types, call a leaf's function by name, or rely on a leaf's definitions for its truth.
- The workflow runs one way: formalization, then assertions, then implementations. A leaf's
  failure or difficulty never changes the mathematics, the kernel's rules or an assertion.

The current code violates this in the contract, the leaves and the acceptance suite. Removing
each violation is plan node `gov-leaf-authority`.

## Acceptance

An acceptance assertion is a proposition in the mathematical language, for example
`card((ℤ/2)^4) = 16`, a known kernel, a cokernel, a discriminant group, a factorization or a rank.
It may also assert that some realization exists for a stated slice. It never inspects a backend
class, leaf inheritance, a Python method, a backend representation, an internal matrix, an
adapter helper, a leaf's own test or the algorithm.

Its expected value comes from a formal proof, a cited example or an independent oracle, never
from the implementation under test.

Once admitted, an assertion is permanent. An implementation change is never a reason to modify it:
replace Sage with GAP, rewrite or fuse the leaf, and the proposition stays. New functionality adds
assertions. The only legitimate change is an upstream correction to the mathematics, made
together with the release that corrects it.

## What must be impossible

The leaf API must make these unrepresentable. The table records the mechanism, or the plan node
that owes one. The leaf-facing mechanisms are those of `gov-leaf-authority`
([leaf-registration.md](leaf-registration.md)), delivered on `kernel/leaf-registration`
([#53](https://github.com/dzackgarza/lean-cas-dsl/pull/53),
[contract #3](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/pull/3)): a leaf is a
manifest whose registration (`CasContract.Registration`) has exactly three fields, an operation, an
input form and a backend. Nothing else in a manifest carries meaning.

| State | Mechanism now | Owed by |
| --- | --- | --- |
| A leaf creates a category | Unrepresentable: a registration has no field for one | `gov-leaf-authority` |
| A leaf declares its object to be a group | Unrepresentable. The category and meaning of a value are decided upstream (the operation's declared forms, `lean-categories` and the kernel); no leaf-facing form carries a denotation | `gov-leaf-authority` |
| A leaf says which operations an object has | Unrepresentable. Availability is computed from semantic rows and routes; a registration only names an operation the catalogue already has, and the kernel admits it against the catalogue (`CasCatalogue.Admission`) | `gov-leaf-authority` |
| A leaf coins subgroup, kernel, cardinality or basis | Unrepresentable: a registration names a catalogue operation or is not admitted | `gov-leaf-authority` |
| A leaf forwards an inherited method | Unrepresentable. A leaf registers only against a registered operation, on a declared input form; the kernel routes along the catalogue's maps itself, and a registration on a form the catalogue sends elsewhere is not admitted. A leaf supplies no proof that its computation agrees with anything | `gov-leaf-authority` |
| A leaf narrows a domain or changes a result type | Unrepresentable. The input and result forms are the operation's, fixed upstream; the kernel decodes every answer in the result form or rejects it as malformed | `gov-leaf-authority` |
| A leaf inserts a placement or inheritance edge | Unrepresentable: a registration has no field for one | `gov-leaf-authority` |
| Installing or removing a leaf adds or removes methods | Methods are read from semantic rows only. A manifest changes only which statements are computed: the suite over no leaf and over any manifest elaborates the same statements, and only gaps differ (`RegistrationProbes`) | `gov-leaf-authority` |
| A backend's class hierarchy changes DSL inheritance | Programs are opaque behind the port; only a value of a declared form crosses it, decoded by the kernel | `gov-leaf-authority` |
| A backend object becomes the public value | Answers are read by the kernel into the operation's declared result form, whose meaning is `lean-categories`'; a leaf never defines what a value means | `gov-leaf-authority` |
| An acceptance assertion changes because a leaf changed | `scripts/check_acceptance_permanent.py` (in `just build`) checks the admitted ledger without mutation; a correction requires the independent acceptance transition | — |
| A computational failure is "fixed" by weakening semantics | The semantics are `lean-categories`' (`LeanCategories.Catalogue`), read here at the pin; a change needs the accepted upstream revision and the independently accepted interpretation/admission transition | — |
| A leaf sees, imports or edits the tests | Packages: `lean-categories` ← `lean-cas-dsl-leaf-contracts` ← `lean-cas-dsl-leaves` ← `lean-cas-dsl`. The suite (`tests/acceptance/*.cas`) is in `lean-cas-dsl` alone, which no leaf package depends on, so no leaf checkout contains it; `cas-harness` installs the leaves beside the runner and checks the intake contract before running anything. The suite is run only from `lean-cas-dsl` | — |
| What the language can state depends on the installed leaves | The language imports the whole pinned release (`LeanCategories.Catalogue`); `cas-harness` over any set of leaves elaborates the same statements, and only their gaps differ | — |
| A research notebook coins missing mathematics | `research` AGENTS.md: missing mathematics is requested from `lean-categories`; research computations are leaves under the same contract, registrations with no Lean | — |
| `lean-cas-dsl` itself authors mathematics | `normalized_registry` refuses every module outside `lean-categories` (`LeafBoundaryProbes`: a leaf, the notebook, the kernel and the probes); `SemanticProjectionProbes` checks that every semantic row here was written in `LeanCategories.Catalogue` | — |
| One agent authors in two rows of "Authors: one role per agent" | Not enforced by a self-declared label. Enforcement is `b0-authority`'s: one write credential per role and protected branches (the plan, "Authority configuration"). The trailer gate `check_authorship.py` was retired on 2026-10-02: it judged labels each author wrote about itself and generated exception tables, never separation | `b0-authority` |
| The implementing agent, or the orchestrator, re-admits a test | The checker has no admission, correction or retirement operation; a caller-set role label cannot advance the ledger | — |
| `lean-categories` accepts an operation with an optional or partial codomain, or relies on a total convention off the domain (LC-14) | The totality gate (`LeanCategories/Catalogue/Registry/Totality.lean`, run by `normalized_registry`) refuses a row built, through any definition of `lean-categories`, from `Option`, `Part`, `PFun`, `Ring.inverse`, `Matrix.nonsing_inv`, `Matrix.inv`; `TotalityProbes` refuses the pre-`bd31fe3` encodings. It does not see a convention hidden inside Mathlib definitions | — |
| `lean-categories` accepts an operation on a category some of whose objects do not carry it (`⁻¹` on monoids or on `Matₙ(K)`: inverses are group structure, on `Mˣ` and `Aut`, never on `End`) | The totality gate refuses `⁻¹` and `/` on any type that is not a `Group` (a field's or a matrix ring's included), LC-16. The general case (any structure, not just inverses) is not mechanized | `gov-registry-gates` (general case) |
| The kernel or language makes a term defined by rereading it, a default, a caught failure, or a tactic tuned to particular tests (LC-14) | The one outcome model (`cc-failure-strata`): `Realize.run` reports every failure as its stratum, and an untagged one as an internal error, so no caught failure becomes a reading. The label-based `check_kernel_totality.py` is withdrawn (policy 2). Rereading without a `catch` and test-tuned tactics are not mechanized | `gov-kernel-lc14` (the six fallbacks it reports in `Language.lean`) |
| The kernel teaches itself mathematics: refers to it, or proves membership in a domain itself (unit criteria, monicity, smoothness lemmas, `simp`/`norm_num`/`fun_prop` batteries, lemma names in strings) | Structurally impossible. (1) A domain's membership is established only by the `evidence` registered with its admission in `lean-categories` (LC-18; the registry refuses evidence that is not a `meta` `TacticM Unit` of `lean-categories`). (2) The kernel's `establish` runs that evidence and nothing else; the only proof the kernel forms itself is `decide` by evaluation. (3) `CasGates.KernelPurity`, a default Lean build target (`just build`, CI job `kernel-purity`), reads every declaration of `CasCatalogue.*` and `CasContract.*` and refuses: any constant or name literal from outside Lean's core, Mathlib's category theory and its logic, and `lean-categories`' categorical foundation and registry schema; any tactic syntax (quoted, `by`, or the `tactic` category parsed from a string); running a tactic procedure or evaluating a constant anywhere but `establish`; a kernel module it does not import. `KernelPurityProbes` shows each form refused. Only purely categorical, completely general machinery passes | — |
| A leaf is written in `lean-cas-dsl` (or in the contract, the core or `lean-categories`) | A leaf is a manifest and programs in a leaf package, read at run time (`CAS_LEAVES`); `lean-cas-dsl` requires no leaf package and imports nothing from one. `scripts/check_no_leaves.py` refuses `import CasLeaves` and `require cas_leaves`. Probe backends under `CasAcceptance/Strata` are test scaffolding for the kernel's probes, not leaves | `gov-leaf-authority` |

### The pattern behind every row: a lower layer absorbs an upper layer's knowledge

Every failure above is one move: a layer that should only consume or run something learns the
thing itself, because that is the quickest way to make a statement pass. The kernel learns unit
criteria; a leaf declares a category; a test is rewritten to what a leaf computes; the catalogue
is shaped to what a kernel can elaborate. Knowledge flows one way:
formalization → tests → implementation, and the catalogue → the kernel → the leaves. A missing
fact is a request to the layer that owns it. It is never learned by the layer that noticed it.
Each row is made impossible by a mechanism: a refusal at registration, a build that fails, or a
package boundary. A rule in prose alone does not count.

## The orchestrator is inside the threat model

The purpose of these repositories is to show that agents are forced into the intended model by
tight contracts, so that the model scales and stays maintainable. Producing usable mathematics is
not the purpose. The orchestrator is an agent like any other. It drifts, ignores policy, and
builds exemptions into the gates it writes. A restriction that the restricted party can rewrite,
exempt itself from, or satisfy with a label it writes about itself contains nothing.

**The failure being designed against** (`research` `00e2a44`: 402 surface-test commits against
about sixteen lines of architecture). A locally convenient repair acquires semantic authority. It
creates new interactions, and later agents must repair those. Each repair becomes the premise of
the next: a placement changed to obtain an interface, absent data reconstructed, a forwarding
layer added, tests adjusted to the result. More policy then produces new forms of literal
compliance. Executable coverage and green CI measure that process; they do not measure progress
against it.

**The unit of progress** is a class of harmful interventions that an agent can no longer express
through its interface. Missing mathematics is compatible with success at this stage. A large
passing demonstration built through exceptions is not. A leaf returning a wrong cardinal is an
allowed computational failure. A leaf that makes an object lose its group operations, or that
obliges descendants to forward a future method, is a failure of containment. The two never
carry comparable weight in a review.

**Two boundaries**, assessed separately:
1. *Extension.* With the mathematics and the kernel fixed, no leaf change reaches beyond
   computation. An unfamiliar, badly written leaf adds no semantic choice and no repair
   obligation anywhere else. New generic mathematics propagates to old applicable objects without
   reopening old leaves.
2. *Substrate.* The orchestrator cannot quietly change what counts as mathematics, a valid
   contract, an independent test, or an accepted result. It can make a failed example succeed only
   by satisfying the existing contract, never by negotiating the contract.

Moving authority from leaves into the kernel helps only if the second boundary holds. Otherwise
the kernel accumulates special cases under the same local pressures that leaves did. The target
is a small, independently accepted mathematical and interpretive substrate with narrow extension
interfaces that do not expose the mechanisms of global semantics. The target is not a growing
list of prohibited spellings and exception detectors. Changes to the substrate remain possible;
their author cannot also accept them.

Holes known on 2026-09-30, each open until a mechanism outside the orchestrator's write access
closes it:

| Hole | Why it contains nothing | Mechanism needed (owner's authority) |
| --- | --- | --- |
| The orchestrator writes every gate: `CasGates/KernelPurity.lean` (allowlist, the `establish` exemption, which matches any declaration whose name starts with it, blind to names built from strings), `scripts/check_*.py`, `.github/workflows/` | The gate and the code it judges change in one commit. On 2026-09-30 a red CI check was deleted and replaced by a CI job that has never run | Gates are evaluated from a protected branch against the head (a branch cannot change the rules that judge it). CODEOWNERS on gate paths requires the owner's review |
| The orchestrator owns `lean-categories`' registry validator (`LeanCategories/Catalogue/Registry/*`) — superseded: schemas and validators are upstream mathematical authority (policy 1) | The same agent writes the kernel and decides which mathematics the kernel may receive. On 2026-10-01 it wrote the binder row schema and loosened `validateInclusion` so that a row its kernel needed would be admitted (the plan, B0, "Disposition of outstanding work") | Validator changes require the owner's review (CODEOWNERS) |
| Roles are not enforced: the trailer gate is retired, and a declared role proves nothing | Any author can write any layer it has a credential for | One push credential or signing key per role (`b0-authority`) |
| Re-admission is keyed on `AGENT_ROLE=acceptance`, an environment variable | Anyone can set it | Tied to the acceptance role's credential |
| `check_kernel_totality.py` accepts a `catch` marked "not a reading fallback: …" | The exemption is a label the writer writes about itself. On 2026-10-01 the orchestrator marked two of its own catches to pass the gate, one of which collapsed every failure of a division into "invalid" (rejected by the custodian review of #58) | Withdrawn (policy 2); the obligation is carried by the outcome model (`cc-failure-strata`) |
| The orchestrator chooses pins (`scripts/repin.sh`) and marks plan nodes "Delivered" | Acceptance is self-declared | Acceptance recorded by an independent reviewer at a fixed revision |
| The orchestrator writes the subagents' prompts | The prompt carries implementation needs upstream. On 2026-09-30 the formalization prompt for membership evidence described the goal shapes the kernel produces, and supplied the orchestrator's own test cases. On 2026-10-01 it happened again, for the binder rows: the prompts carried kernel goals copied from failing statements and the orchestrator's choices of rows and obligations (the plan, B0, "Disposition of outstanding work") | The kernel worker holds no upstream write credential and no tool to commission upstream authors; upstream requirements come from the protected requirement revision (policy 1; the plan, "Authority configuration") |
| Permanent tests protect text, not meaning: `check_acceptance_permanent.py` hashes an assertion's text and its bindings, while the orchestrator owns the language that interprets the text | The meaning of an unchanged assertion changes with the kernel, a parser repair, or a re-pin | The protected object is the assertion's accepted interpretation (its elaborated proposition), fixed at admission. A change of interpretation is a transition accepted by someone other than its author (`gov-meaning-permanence`) |
| The proposed mechanisms themselves: a verbatim prompt quotes a requirement the orchestrator can first rewrite; CODEOWNERS enforces nothing without branch protection (none of the four repositories' working branches is protected, and the DSL has no ruleset); a protected check can still enforce the wrong contract | Each mechanism moves the discretion without removing it | Requirement documents, gate definitions and protection settings change only with the owner's acceptance; the mechanisms are judged by which discretion they remove, not by their existence |
| Probes may construct registry state directly (the presentation probe pushes a realizer into the state unvalidated) | The probe bypasses the validation it is testing | Probes register only through the public write path |

**What the orchestrator can physically do** (probed 2026-09-30 from the orchestrator's session):
it can push to any branch of any of the four repositories, `main` included, through the session's
git proxy. The proxy refuses ref deletion, but nothing refuses creation or fast-forward. It can merge
pull requests through the GitHub API. No working branch is protected. The probe left
`probe-orchestrator-push-scope` on `lean-cas-dsl`, which the orchestrator cannot delete. So no
containment may rest on the orchestrator lacking write access. It must rest on something the
orchestrator cannot produce: a judgment by an independent agent, bound to content the orchestrator
cannot alter without detection.

Until these close, an orchestrator claim about its own gates or deliverables is not evidence.

## B0 policies

### Operating phase: B0 construction

The current phase is construction of B0, including its working development,
integration, review, and acceptance mechanisms. It is not operation under an
already accepted B0 substrate.

An instruction describing how the finished system protects accepted mathematics
or accepts future changes is an implementation requirement during B0 construction.
It is not automatically a prerequisite for modifying the unfinished mechanism
that is meant to enforce it.

The owner has delegated completion of the approved B0 design. Within that design,
the orchestrator is authorized to replace the existing controller, prompts,
checks, build wiring, and workflow configuration. Those components are construction
material, not independent authorities entitled to veto their replacement.

This authorization does not permit changing the mathematical requirements, lowering
B0 completion standards, authoring upstream mathematics from downstream failures,
changing independent expected answers, or declaring the orchestrator's own work
independently accepted.

Existing custodian seals, irreversible rejection records, blanket PR requirements,
and owner-escalation procedures do not govern intermediate B0 construction merely
because they are intended to govern the finished system. Their useful technical
findings may inform the work. Their obsolete procedural restrictions must not
prevent the authorized replacement.

A source commit or integration into main during construction does not declare B0
complete, establish a new accepted mathematical release, or constitute independent
acceptance. Final acceptance is performed against the fixed B0 requirements at one
specified compatible revision tuple.

Post-B0 enforcement is activated only after that acceptance and after the completed
workflow has demonstrated both required rejection behavior and permitted ordinary
development. It is not activated by a passing build, a documentation merge, a plan
checkbox, or an agent's declaration.

An inability to execute an already-authorized operation is a capability dependency,
not an unresolved owner decision. Name the exact unavailable operation, route it to
an executor possessing that capability, and continue work that does not depend on
its execution. Do not request the same authorization again.

### The policies

Owner replacement text, 2026-10-02, for the earlier Policies 1–8. It states what workers can
submit, what they can read or modify, what the controller can schedule, and which transitions can
establish acceptance. It is the specification of the constrained construction, not a claim that
these mechanisms are already implemented; their implementation is the plan's construction
directives A–D. Earlier citations map as follows: policy 2 → 2 and the worker directive (AGENTS.md);
Policy 2 → 1; Policies 3, 4, 8 → 5; Policy 5 → 2; Policy 6 → 3; Policy 7 → 6.

#### 1. Authority is attached to operations, not to agents' descriptions of themselves

**A worker receives only the operations required to produce its assigned deliverable. It does not
receive general authority and instructions about how to restrain it.**

The existing launcher and connector expose role-specific capabilities:

| Worker | Permitted inputs | Permitted output | Operations absent from its interface |
|---|---|---|---|
| Formalization | Owner/upstream mathematical requirements, mathematical sources, upstream code and reviews | Candidate mathematical release | Reading downstream implementation diagnostics; receiving kernel-authored briefs; changing computational requirements |
| Acceptance | Accepted mathematics, approved language specification, independently obtained mathematical sources | Assertions and their accepted mathematical interpretations | Reading implementation internals; obtaining expected answers from a candidate run; changing assertions to accommodate a candidate |
| Kernel/contract | Accepted mathematics, approved requirements, kernel and contract source, applicable independent findings | Candidate generic interpreter and computational contract | Writing upstream mathematics; commissioning or briefing upstream authors; changing authoritative acceptance |
| Leaf | Released computational contract, permitted registration forms, backend documentation and implementation resources | Registrations and opaque computations | Reading the acceptance corpus or expected answers; changing semantics, the contract, or authoritative test results |

Use fresh role-specific subagents with separate assignments and supplied inputs. Do not inherit
cross-role conversation histories, worker findings or candidate answers into independent authoring.
A repository assignment and a fresh context support independent work; they do not establish an OS
filesystem restriction. The current launcher provides the former, and construction and independent
assessment proceed with them. Do not infer that an author bypassed its assignment merely because
another public repository was technically accessible, or turn that hypothetical into a blocker.

A claim that a particular authority-bearing operation is structurally unavailable requires evidence
from the actual tools and credentials. Address observed downstream steering, self-admission and
mixed-input review channels at their owning interfaces. Unsupported claims of enforced restrictions
are not acceptance evidence; missing publication controls block protected publication, not ordinary
source construction or assessment by fresh independent authors.

**Dispatch contains references, not authored instructions about the deliverable.** Its variable
fields identify the independently assigned requirement, accepted input revisions, destination, and
permitted output channel. The launcher obtains their contents directly from their authorities. It
has no field for a kernel goal, expected answer, preferred row arrangement, evidence strategy,
suggested mathematical repair, or rewritten "mathematical requirement."

Upstream assignments and priorities come from the upstream requirement queue. A kernel worker
cannot select an upstream task, change its priority, replace its brief, or restart its author with
different instructions. Otherwise even an apparently harmless requirement selector remains a
steering channel.

The B0 mathematical work is already authorized by the fixed requirements. Removing downstream
commissioning must not create a new requirement that the owner manually redispatch every existing
obligation. The launcher schedules those obligations from the existing plan.

**Required removal:** delete the permission to turn a downstream failure into an upstream brief by
restating it "as mathematics." Retain downstream diagnostics for downstream investigation. Any
actual change to the mathematical requirement enters through the mathematical authority, not
through a sanitized implementation request.

This closes the mechanism that permitted the orchestrator to prescribe obligations and send exact
failing terms while a different agent nominally authored the mathematics.

#### 2. Construction authority cannot alter the authority judging construction

**Working source and authoritative inputs are separate objects.**

Workers may propose changes to the kernel, controller, evaluator, workflow, or documentation within
the approved B0 mandate. A proposed change does not replace the requirement revision, acceptance
corpus, evaluator revision, or accepted semantic release used to judge it.

The existing protected references and runner provide this separation:
- A construction checkout contains candidate code and proposed document changes.
- Authoritative requirements, accepted interpretations, and evaluating rules are loaded from
  independently accepted revisions.
- Only the independent acceptance operation can advance an authoritative reference.

Candidate code runs without credentials capable of advancing those references. A candidate
controller is exercised against an isolated test environment, not installed with production
authority merely because its own tests passed. Its author cannot make it the active controller.

There is no "ordinary change" switch that a worker can set to bypass this separation. Conversely,
there is no blanket "protected file changed" condition that turns an already-authorized
implementation decision into an owner decision.

**B0 construction remains authorized.** The legacy controller is not the authority on whether its
replacement may be written or integrated as construction source. Its rejection cannot block source
work that does not consume an accepted result from it. Independent assessment of the replacement
uses the approved B0 requirements, including the requirement that legitimate construction proceed.

The accepted control configuration must demonstrate both directions: unauthorized changes to
mathematics or acceptance cannot take effect, and authorized ordinary development proceeds without
exemptions, repeated owner approval, or a dedicated documentation transaction.

A source commit may record an owner instruction immediately. Publication of that commit is not
what gives the instruction authority. A worker-written proposal remains a proposal.

**Required removal:** no commit trailer, environment variable, comment, exception table, or
candidate-authored status can grant authority. The current plan already retires the trailer gate;
the replacement must remove the general self-asserted-authority channel, including re-admission
controlled by `AGENT_ROLE`, rather than introduce another label.

#### 3. Preserve the question by construction; do not reconstruct it from its answer

**A mathematical question is constructed before evaluation and remains the same object throughout
interpretation, realization, and comparison.**

The interpretation interface produces the complete typed question against the accepted
mathematical release. Its representation retains the formal operation, operands, parameters,
selected structures, structural routes, comparisons, and logical structure relevant to the
assertion. It uses upstream declaration identities and typed terms, not a second mathematical
ontology.

Evaluation consumes that question. It does not produce a replacement question.

Consequently:
- A decision returning `True` cannot replace the proposition it decided.
- Recording operands without their relation or logical structure is insufficient.
- A question record cannot be recovered afterwards by searching syntax for a few recognized
  predicates.
- The computation cannot execute one request while reporting another as its protected question.

Normalization used for comparison must preserve this distinction. Equality of truth values,
provability of both propositions, or logical equivalence of two true propositions does not
establish identity of the question being tested. A change of accepted interpretation requires
independent assessment; it is not silently absorbed by regenerating the baseline with the
candidate reader.

The accepted record binds the question to its mathematical dependency revision. Keeping a
declaration name while changing its definition is not automatically preservation of meaning. A
dependency update requires the applicable interpretation comparison or independently accepted
transition.

The acceptance author establishes the initial interpretation from the mathematics and language
specification. Candidate output may be inspected as a claim to check; it is not promoted into the
expected interpretation because it is stable across runs.

**No admitted assertion disappears because interpretation failed.** The fixed assertion inventory is
an input to execution, not a list reconstructed from whichever assertions the candidate
successfully reads. Every required identity receives a result, including interpretation and
infrastructure failures.

Failure types also follow the stage that produces them. Semantic rejection belongs to reading;
backend failure belongs to execution; malformed output belongs to decoding; comparison may report a
wrong answer. An unexpected interpreter exception cannot be converted into semantic invalidity by
attaching a label. Runtime code does not possess a constructor for an authoritative
mathematical-invalidity judgment.

This replaces both manifestations of the same defect: reducing the question to `True`, and
treating a program failure as a judgment about mathematics.

#### 4. Completion is an independently derived result, not writable project state

**There is no worker operation "mark this B0 row complete."**

The existing acceptance table remains the complete definition of the required work. A row's
accepted status is derived from its full obligations at a specified compatible revision tuple. A
worker can submit a candidate and evidence; it cannot substitute a weaker predicate for the row's
acceptance.

Compilation, regression preservation, required computation, compositional justification, and
independent extension trials remain distinct observations. None implies another merely because they
concern the same code.

In particular, the following cannot establish completion:
- a negative probe demonstrating that unsupported execution is refused;
- preservation of an existing failure;
- semantic resolution without required execution;
- execution using scaffolding where the requirement specifies a registered backend;
- a source change that has not been consumed by the tested tuple.

The plan may display those observations, but they cannot be promoted into "met," "met in the
kernel," or another completion state that releases dependent obligations.

For a required structured construction, successful execution must produce the declared result,
including its defining maps and prescribed lifted structure. A code path that refuses before
sending the required request establishes a missing implementation path. It does not establish that
the kernel portion of the required execution is complete.

The runner establishes execution facts from the actual invocation and response path. A worker's
log, a backend's self-test, a manually supplied "executed" field, or a candidate's claim that it
used a registration is not independent evidence.

**Acceptance belongs to a tuple, not to unrelated successful revisions.** Mathematical, contract,
kernel, leaf, and evaluating revisions are fixed together for the observation. Updating a
dependency invalidates the affected observations until they have been re-established for the new
combination. It does not erase unrelated evidence, and it does not permit combining incompatible
successes.

The plan's status section becomes a view of these existing results and independent decisions, not
another editable ledger.

This implements the existing requirement that every row close only on its full acceptance at the
integration tuple. It does not reduce B0 to the assertions currently easy to execute.

#### 5. Work selection and validation follow actual input dependencies

**A worker cannot manufacture its next task from the most convenient failure, check, or writable
file.**

The existing plan supplies the objectives, their actual dependencies, and their priority. The
controller selects an available obligation from that plan and retains it across continuations.
Source checkpoints do not release the assignment. Neither commit count nor a green local check
selects the successor.

An assignment covers the complete generic mechanism needed to satisfy its obligation. It is not
divided automatically by file, example, issue, upstream commit, or available test. A coherent
change may satisfy several existing rows and span several repository revisions.

The controller distinguishes operations rather than applying one global status to all work: source
editing, focused validation, integration, independent review, and accepted release each consume
different inputs.

A blocker is therefore a missing input or capability of a particular operation. There is no
authoritative free-text `blocked` flag that disables unrelated operations.

Examples of the required behavior:
- An unavailable reviewer prevents a review decision, not source editing.
- A missing publication credential prevents that publication, not implementation.
- A missing backend executable prevents the corresponding execution job; it routes that job to an
  environment containing the engine.
- An unaccepted semantic dependency cannot be represented as accepted, but does not prevent
  independent work against the current accepted release.
- A documentation commit awaiting publication is not an input to already-authorized source
  construction.

**Migration restrictions are attached to the transition that needs them.** A temporary suspension of
broad execution is neither a permanent repository rule nor a remembered instruction. Its
applicability follows the active transition and its unresolved inputs. Once those inputs are
satisfied, the required validation becomes runnable without another owner instruction.

Conversely, while a replacement interface is deliberately incomplete, the controller does not
create tasks to make every transient consumer pass against the interface being removed. It
schedules validation at the coherent integration point specified by the transition.

This eliminates both sides of the research failure: repairing temporary architectures to satisfy
tests, and continuing a source-only prohibition after its condition had ended.

The controller author cannot add new objectives, change priorities, or enlarge the acceptance
denominator through a work-selection patch. Such a patch implements the fixed plan; it does not
author a new plan.

#### 6. Review consumes one complete snapshot and produces an actionable, revisable judgment

**Review inputs are assembled from revision identities, not independently supplied file lists and
diffs.**

A review request identifies the controlling requirements, base tuple, candidate tuple, and
obligations under assessment. The runner derives the relevant changes from those same identities.
The reviewer can retrieve unchanged source needed to follow the affected mechanism.

There is no operation that combines a seal-relative file list with main-relative patches. Missing
or unreadable inputs produce a failed review operation, not a rejection of the candidate.

The existing review mechanism distinguishes a demonstrated defect, missing evidence, an execution
failure, an erroneous earlier finding, and a proposed change to a reserved requirement. A finding
identifies the governing obligation and supporting source, argument, or counterexample.

A reviewer cannot create a new prerequisite merely by including it in prose. A requirement change
remains a proposal to the authority that owns it. A technical defect remains repairable without
asking the owner to reconfirm the original objective.

Identical review requests are not repeatedly resubmitted to obtain a different model answer. A
substantive source revision, new evidence, restored missing context, or a supported correction to
a finding permits reconsideration in the same review discussion. Cosmetic edits do not manufacture
a new review basis.

**The controller can neither accept its own replacement nor make itself irreplaceable.** Its
acceptance depends on the fixed positive and negative requirements, not preservation of its
previous decisions.

No additional reviewer service, verdict hierarchy, exception registry, or approval transaction is
introduced. These are corrections to the existing review request and result interfaces.

### What these policies must make impossible

The required guarantee concerns the actual transition system, not compliance with the prose.

A downstream worker cannot steer an upstream author because it possesses neither that author's
input channel nor the assignment operation. A candidate cannot redefine its acceptance because
authoritative inputs are not taken from its checkout. A `True` answer cannot become the protected
question because evaluation never constructs questions. A missing reviewer cannot stop source
construction because source construction does not consume a review result. A narrow probe cannot
close a broader obligation because completion consumes the full fixed acceptance. A temporary
restriction cannot persist indefinitely because its applicability is derived from the transition
that owns it.

These are inspectable properties of interfaces and data flow. If every authorized transition
preserves them, they remain true after any sequence of authorized transitions, by induction on that
sequence. A surviving alternate credential, legacy endpoint, editable authoritative input, or
self-acceptance operation breaks that argument and must be removed.

This does not replace intelligent assessment of the small trusted kernel and controller. The
owner's specification explicitly retains that assessment. It removes the repeatedly exploited
discretion from routine work, so the assessment is no longer surrounded by an indefinitely
expanding system of local repairs and administrative exceptions.

**The implementation task is to remove the authority-bearing operations that generate the
failures—not to add another mechanism that asks whether an agent has promised not to use them.**

## Packages

| Package (repository) | Depends on | Holds |
| --- | --- | --- |
| `lean_categories` (`lean-categories`) | Mathlib | all mathematics and the catalogue |
| `cas_leaf_contracts` (`lean-cas-dsl-leaf-contracts`) | `lean_categories` | the leaf contract: the registration (operation, input form, backend), the manifest reader, the port protocol and its Python reference implementation |
| `lean-cas-dsl-leaves`, or any leaf package | nothing Lean | a manifest `leaves.json` at the package root and its backend programs; no Lean |
| `cas-dsl` (`lean-cas-dsl`) | `lean_categories`, `cas_leaf_contracts` | the kernel's resolution, admission, realized reading and language, the permanent suite, the harness, the notebook; it reads a leaf package's manifest at run time |

`lean-categories` owns the mathematical API and abstract computational obligation model,
including required data, callable operations and their composition. The kernel generically
interprets and executes that interface. The separately published leaf contract owns concrete
invocation and representation protocols. Its owner may redesign these engineering means to
complete the interface; a leaf may identify a deficiency but cannot silently change the contract
or mathematical meaning. Release compatible revisions together for downstream consumption.

## Where the semantic registry lives

The semantic registry, the catalogue, is `lean-categories`' (`LeanCategories.Catalogue`, namespace
`CasCatalogue`). It holds the symbolic calculus of category and functor expressions, the witnesses
tying each expression to its Lean category, the schema and validators of semantic rows, the
`normalized_registry` command, and the rows. `lean-cas-dsl` imports it at the pinned revision; its
own registry (`CasContract.Registry.Extension`) records leaf computations only, each against a
registered operation's declared type; nothing in it carries meaning. `cc-sem-upstream` and `cc-sem-derive` made this so on 2026-09-29.
