# Kernel evaluator and mathematical data: explicit-state assessment

Recorded 2026-10-28 at the owner's request to integrate the preceding response verbatim into the repository and GitHub work.

**Placement:** the evaluator comparison belongs to the existing #69 first-complete-chain trial under #10; #23 carries the mathematical-data requirements into the existing consumer forecast, #66 preserves the complete mathematical reading, and #24 applies the unchanged delivery conditions. This is an implementation trial, not a new framework milestone or an accepted runtime result.

The response below is reproduced verbatim. The integration clarification after it preserves existing lazy and fused execution and the current evidence model.

<!-- BEGIN VERBATIM RESPONSE -->

You’re right. I misread your question. You meant **how to structure the kernel and mathematical implementation so agents can work on it reliably**.

**Yes: explicit state, reducers, and separation of effects could help substantially here. The strongest application is an evaluator in which a computation has one immutable definition, one result location, and explicit dependencies—and mathematical values retain the defining data and witnesses needed by later operations.** That could replace several mechanisms currently responsible for recurring failures. It would be a change to the implementation itself.

There are two related opportunities: **how the kernel evaluates computations**, and **how mathematical transformations represent and preserve their data**.

## 1. The kernel opportunity: make execution an explicit machine

The architectural change worth considering is:

> A consumer refers to a particular computation and its declared outputs. It does not reconstruct that computation from a mathematical expression or carry its own partially updated copy of the producer’s state.

This is more consequential than putting `Pending`, `Running`, and `Completed` labels around existing functions.

### The historical mechanism it addresses

The repository records three particularly relevant failures:

| Observed failure | Mechanism | What an explicit evaluator could eliminate |
|---|---|---|
| After preparation, replacing an expression-cache entry could substitute a different computational input or endpoint presentation. | Preparation selected an occurrence, but execution later recovered it using mathematical expression identity. | Post-preparation recovery of operands by expression. Consumers instead retain references to the selected occurrences. |
| A target operation received an unexecuted forgetful action; pullback reuse similarly passed composite recipes that a target leaf happened to understand. | Dependencies were described inside values without a uniform rule requiring their execution before consumption. | Consumer-specific interpretation of foreign executable recipes. The evaluator demands the declared dependencies before invoking the target. |
| A pending map converted into a point could be mistaken for completed computation. | Interface role, payload shape, and completion status were distributed across optional fields and flags. | Independent guesses about whether a value has executed. A point view of a pending computation remains pending. |

These are recorded in the [handoff’s execution-boundary diagnosis](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/HANDOFF.md#L421-L477) and its [subsequent lifecycle checkpoint](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/HANDOFF.md#L527-L566). Some individual cases have since been repaired; their significance is the repeated underlying mechanism, not a claim that every historical reproducer still fails.

These failures are a good fit for an explicit evaluation machine because they concern **which computation is being evaluated, what it depends on, and whether its result actually exists**.

### What that machine would contain

A schematic representation would separate three things:

```text
Selected computation:
    complete formal application
    selected category contexts and parameters
    exact operand references
    declared result interface
    execution/completion plan

Execution cell:
    Pending selectedComputation
    Evaluating selectedComputation continuation
    Completed checkedResult

Checked result:
    actual computational data
    complete result interface
    positioned ownership
    references to retained fields and defining maps
```

Here, the result interface must contain the complete selected information—not merely a form name or carrier type. An object, a morphism with particular endpoints, and a scalar have different interfaces. Those roles are independent of whether execution is pending or complete.

A reducer-style transition can then be small:

```text
step(machineState, observation)
    → nextMachineState + requiredEffects
```

The effects are operations such as demanding an operand, invoking an already selected computation, or checking a returned packet. Lean elaboration and validation remain effectful operations; backend interaction remains IO. The reducer determines which transitions are permitted and where their results belong.

**The substantial simplification comes from making that result store authoritative.** A downstream projection holds a reference to the parent occurrence and a declared field. It does not copy the parent’s execution flags, infer its owner again, or search for an equal-looking expression.

### Much of the necessary representation already exists

The current source already has:

- `CapturedInvocationInterface`, with six invocation kinds.
- `SelectedStructuredInvocation`, retaining contexts, diagrams, creation information, operand occurrences, and a `StructuredResult.DataPlan`.
- `SelectedStructuredProjection`, retaining a parent and its declared projection.
- `RoutedResultPlan`, representing retained inputs, returned fields, intermediate stages, and projection actions.
- `InvocationExecution`, containing an original input, captured invocation, and optional result.

See [the selected invocation types](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/CasCatalogue/Realize.lean#L409-L608), [the invocation result record](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/CasCatalogue/Realize.lean#L660-L688), and [RoutedResultPlan](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/CasCatalogue/RoutedResultPlan.lean).

But these coexist with mutable `Wire` flags, optional framing and invocation information, expression-keyed results, separate result tables, field caches, and recursive observation callbacks. The [current harness](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/CasCatalogue/Realize.lean#L2189-L2227) makes that coexistence visible.

**My recommendation is to complete the change from recursive reconstruction to evaluation of explicit selected plans.** Creating another graph beside those plans would worsen the situation.

## 2. A concrete mathematical computation to drive the replacement

The existing pullback/creation obligation is a suitable first case because it exercises the difficult parts together.

Suppose we have

\[
f:A\to C,\qquad g:B\to C,
\]

and a registered functor \(U\) with the required creation structure for computing the chosen pullback through another category.

The computation must preserve:

- The independently selected structures on \(A,B,C\).
- The actual occurrences of \(f\) and \(g\).
- The selected object and morphism actions of \(U\).
- The accepted comparison or creation data.
- The computed apex and defining maps.
- The relationship between that particular result and subsequent projections or universal operations.

The executable plan would express the necessary dependencies explicitly:

```text
demand the original map and endpoint occurrences
evaluate the selected object/morphism actions
invoke the registered construction on their completed outputs
validate and retain the complete construction result
project its declared defining map
use that retained map in a subsequent computation
```

These are generic instructions over registered plans. The kernel does not need a new collection of mathematical opcodes named after every construction.

The crucial operation is the projection:

```text
Project(parentOccurrence, declaredPort)
```

Its meaning is “obtain this field of this computed construction.” It cannot quietly become “reconstruct a mathematically equivalent construction and obtain its corresponding field.”

That distinction matters when the two constructions have different presentations, chosen comparisons, backend objects, or ownership.

It also handles laziness naturally. A projection of a pending parent demands that parent. A projection of a completed parent reuses its retained result. A later universal factor operation can take a new cone while still referring to the original chosen construction; the initial result need not precompute every possible factorization.

### What would actually be removed

For this first complete path, the replacement should remove responsibilities currently spread across:

- Recursive `observeObject` and `observeMap` scheduling inside `observeStructuredInvocationWith`.
- Recursive recovery of parent and endpoint computations during projection.
- Separate completion updates and caches for the same intermediate result.
- Expression-based recovery of already selected inputs.
- Captured callback environments that can instead be represented by the existing explicit completion plans.

The current [structured invocation observer](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/CasCatalogue/Realize.lean#L9901-L9975) shows the callback-based orchestration that this would replace.

The mathematical plan builders and validators remain necessary. An instruction that simply calls the existing large observer unchanged would provide almost none of the proposed benefit.

This is where the expected payoff is grounded: **the change removes operations that enabled the recorded errors**, rather than asking every future caller to remember more invariants.

## 3. The mathematical opportunity: transformations should carry their defining data

There is a second application that goes beyond the evaluator.

Several historical mathematical bugs arose because code kept the transformed object but lost, misinterpreted, or reconstructed the transformation that defined it. Here, the useful pattern is **explicit mathematical state with transitions that preserve a stated relation**.

### A concrete example: the basis-change convention bug

The research repository’s October 7 repair records two consumers interpreting Sage’s `LLL_gram` transformation incorrectly.

For the returned matrix \(U\), the convention was

\[
G_{\mathrm{new}}=U^{\mathsf T}GU.
\]

Its columns were the new basis vectors in the original coordinates. One consumer transposed \(U\) before using it in Babai rounding. Another used \(UGU^{\mathsf T}\) to obtain an enumeration bound, which could cause vectors to be missed. The [actual repair](https://github.com/dzackgarza/research/commit/fa2318454826c2b128d640ab77dfeb3b544f8afa) corrects both uses.

That is an excellent example of where this design discipline can help the **mathematics implementation**.

Instead of returning a matrix whose direction every consumer must reinterpret, return a basis change with its source and target frames and the agreed direction of its coordinate map. For a sequence of elementary changes \(E\), the state transition is

\[
U' = UE,\qquad
G'_{\mathrm{new}}=E^{\mathsf T}G_{\mathrm{new}}E.
\]

The invariant

\[
G_{\mathrm{new}}=U^{\mathsf T}GU
\]

is preserved by construction.

The benefit is that the transformation, its composition rule, and its coordinate convention have one implementation. Consumers use its declared operations instead of choosing whether to transpose a bare matrix.

This does **not** justify rewriting LLL to try out reducers. The immediate transfer is a better representation of the returned basis change and a shared implementation of its actions. Where a cheap checker is appropriate, the retained witness also makes that checker possible. Whether such certificates become primary acceptance evidence remains the separate evidence-model decision already identified in #71.

The same principle applies to:

- A quotient together with its quotient map.
- A kernel together with its inclusion.
- A normal form together with its change-of-basis transformations.
- A finitely presented module together with its selected presentation.
- A universal construction together with its defining maps and the operations that use them.

Those mathematical representations belong with the mathematical declarations and forms. The kernel should execute their registered interfaces, without acquiring lattice- or matrix-specific semantics.

### Another concrete example: derive a property from the retained construction

The research merge repair [e8866fb1](https://github.com/dzackgarza/research/commit/e8866fb1f232deed6c105e80cbbfc580732c90ed) documents `is_framed_module()` returning `False` after the `Framed` category was retired, despite a selected resolution being present. The repair made the answer derive from `has_selected_module_resolution()`.

That is the simplest useful “reducer architecture” lesson here: **do not independently store a status that is already determined by the actual mathematical data.**

Likewise, the same repair restored use of the codomain’s chosen framing lift. Replacing that retained lift with a general solver had caused recursion.

A richer lifecycle enum would not have fixed either problem. Retaining the construction and deriving its observable properties did.

## 4. Refinement and resolution need immutable mathematical identity

The Sage history gives another relevant distinction: refining what is known about an object must not inadvertently replace which object or structure was selected.

In [sage-categories #31](https://github.com/dzackgarza/sage-categories/issues/31), asking whether `AbelianGroups()` was concrete caused a previously constructed module to lose its working `action()` method.

In [#33’s corrected causal analysis](https://github.com/dzackgarza/sage-categories/issues/33#issuecomment-5563959264), intersection discarded an independently declared subcategory. An inverse retained under one base could no longer be found through the later lookup.

A better mathematical state model separates:

1. **The selected structured value:** its category context, parameters, source/target where applicable, and defining data.
2. **Additional facts and available implementations:** what refinement establishes about that same value.

A refinement transition can add a fact or derive an implementation view while preserving the selected value. Transport to another presentation is a separate operation carrying the required comparison.

That is a useful constraint on the implementation. It reduces the possibility that a local refinement repair changes the meaning of another consumer.

However, the representation must distinguish the right mathematical entities in the first place. In [sage-categories #26](https://github.com/dzackgarza/sage-categories/issues/26), additive and multiplicative monoid structures were collapsed into one implementation occurrence. A perfectly deterministic reducer over that one slot would still produce the wrong structure. The state needs separate selected owners.

**Reducers help preserve a correct mathematical model; they cannot supply a missing distinction or theorem.**

The Lean kernel already has useful pure machinery here. [`Resolve.lean`](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/CasCatalogue/Resolve.lean) computes routes and coherence classes with explicit ambiguity outcomes. [`ComputationDerivation.grounded`](https://github.com/dzackgarza/lean-cas-dsl/blob/65a09dbef4309576afb83b9e6c74904ad77ee0cd/CasCatalogue/ComputationDerivation.lean#L29-L48) computes a finite closure of declared prerequisite support.

I would extend and consistently consume those mechanisms. There is no reason to introduce a second mathematical reduction engine.

## 5. Why this could make agent implementation more reliable

The benefit for agents comes from changing the amount of distributed knowledge required to implement a feature.

With the current overlapping representations, adding a consumer can require knowing:

- Which flags imply actual execution in this particular path.
- Which cache contains the authoritative value.
- Whether an endpoint was retained or must be reconstructed.
- Whether a callback will execute while supposedly preparing a candidate.
- Whether a returned descriptor is data or another executable request.

The historical failures above show that these distinctions have repeatedly been mishandled.

With an authoritative selected plan and result cell, a new consumer has a smaller responsibility:

> Declare its typed dependencies, obtain their completed values through the evaluator, and consume the registered result interface.

Similarly, a mathematical operation returning a basis change or universal construction supplies the defining data once. Later operations use that data through its declared interface.

This can make edits more local and compositional. Exhaustive case analysis can expose a missing execution case; typed field references can prevent accidental substitution of an unrelated result; a single completion boundary can prevent several partially synchronized representations.

But wrapping existing structures in a `State` type would achieve none of that. **The alternative paths must disappear for the migrated computation.**

## 6. What I would do within the existing roadmap

I would use the already planned first complete #69 computation as a bounded comparison of this architecture with the current recursive execution path.

The experiment should establish, together:

1. A nonidentity action and the selected universal construction execute through the same occurrence store.
2. The defining map is retained and used by a later real computation.
3. Changing an equal-expression cache entry after preparation cannot change the selected input.
4. Repeated demand reuses the actual result.
5. Distinct producers with equal formal expressions remain distinct.
6. The migrated path’s old recursive orchestration and alternate completion writes are removed.

That uses existing historical counterexamples and the existing required mathematical chain. It does not require a preparatory framework project.

The expected payoff is specific: fewer places implement dependency ordering, result adoption, field retention, and context preservation. The historical record supports trying to remove those duplicated responsibilities. It does not yet establish how many days the replacement will save.

I would keep this inside the roadmap’s existing first one-to-two-day architectural trial. If the result is only a new instruction such as `ExecuteOldObserver`, or another graph whose values still need expression-cache recovery, the experiment has failed. If it produces the complete chain while removing those recovery and synchronization paths, that is evidence to extend the design.

**My corrected recommendation is therefore to use these techniques in the evaluator and mathematical data representations: an explicit computation machine over retained occurrences, plus mathematical transformations that preserve their defining data and invariants. That is a plausible way to remove a class of implementation problems, and it deserves a bounded implementation trial within #69.**

<!-- END VERBATIM RESPONSE -->

## Integration clarification

Dependencies required before invocation are those required by the **selected realization**. Preserve lazy demand and adequate fused realizations of a fixed composite, including when individual primitive realizations are absent. A fused computation must not fabricate execution receipts for intermediates it did not execute. This clarification preserves the existing #69 implementation-irrelevance and runtime-topology rulings; it does not change the verbatim response.

Use the existing mathematical plans, occurrence identity, validators and registered comparisons. The comparison succeeds by completing the existing required mathematical chain and removing its competing orchestration/result-state path. It does not require a new graph beside the existing plans, a global event bus, or a mathematical opcode per construction.

Returned defining maps, basis changes and other witnesses are computational data with declared meaning. They do not automatically become a new correctness-evidence channel. The certificate-primary-evidence proposal in #71 remains unadopted; INTENT.md, the independent mathematical expectations, frozen-extension obligations and final V1 exit conditions are unchanged. The basis-change example identifies a representation defect to avoid; it does not require an LLL rewrite or add a new V1 mathematical inventory item.

No implementation, compilation, performance improvement or final acceptance is asserted by this record.
