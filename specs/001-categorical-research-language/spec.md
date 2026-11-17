# Feature Specification: Categorical Mathematical Research Language

**Work priority:** required functionality has absolute priority over performance. Performance work is the last phase of this project and begins only when every required capability works through the public interface. A slow run, timeout, resource budget or red CI job does not select work and does not block functional work. [Full rule](https://github.com/dzackgarza/lean-cas-dsl/issues/10#work-priority).

Feature context: `001-categorical-research-language`.

Read both current issue-owned specification parts:

1. [Scope, workflows, scenarios, edge cases and the November 7 clarifications](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6660528117).
2. [Functional requirements, success criteria, entities, evidence quantifiers and traceability](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6660532064).

The [clarification integration and current built-in quality recheck](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6708367076) records the already answered questions and their requirement-level integration. The [original specification review](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6660536569) and its digest apply to the historical version, not the subsequently revised text.

Read the current [constitution](../../.specify/memory/constitution.md) and the full issue bodies. The local scenarios below are a maintained supplement to those texts, not an implementation or independent-acceptance claim.

## Mathematical-model acceptance

These maintained scenarios apply C23 and the [execution model](../architecture.md). They extend
both linked specification parts without changing the original workloads or author separation.
They state required behavior; their presence is not a pass or an implementation-status claim.

| Requirement | User scenario and observable acceptance |
| --- | --- |
| MM001 | Construct an object in a declared category and call an applicable inherited operation. The accepted formal composite supplies its meaning and complete result interface. Removing its provider leaves that meaning intact and yields the prescribed missing-implementation result when demanded. |
| MM002 | Construct an image under a functor implemented independently of its target consumer. The unchanged target method consumes the image through its public interface. Apply the functor to identities and composable morphisms and verify the independently specified functor laws and exact endpoints. |
| MM003 | Request a method whose domain is an owner's core groupoid or a dependent, slice, arrow or higher construction. Interpretation uses that actual domain and does not invent an action on unsupported morphisms. |
| MM004 | Request an inherited operation along competing routes. Use definitional equality of the complete dependent families, an accepted comparison with its prescribed transport, or the explicit C6 binding preference. In its absence, report ambiguity. Route order, provider speed and equal endpoints do not resolve it; a natural isomorphism does not silently become judgmental equality. |
| MM005 | Use a formally finite integer subset in a finite-set operation. The declared refinement and evidence produce its finite-set object with the specified underlying-set comparison. A backend list alone cannot provide this evidence. Two applicable refinements can coexist. |
| MM006 | Perform a calculation requiring a chosen basis, orientation or enumeration. An existence proof alone does not supply that choice. Subsequent calculations consume the actual selected data and their relation to the original object. |
| MM007 | Construct a limit or colimit and use a defining leg and universal factor in a later public operation. The maps come from its selected cone or cocone. Distinct selected constructions sharing an apex keep their own maps. |
| MM008 | Execute the original lift and factor workflow, then use the returned object, defining map and comparison in subsequent functor actions. Verify the original equations with the required computational implementations and inputs. Equal formal expressions from distinct occurrences cannot substitute for the selected returned values. |
| MM009 | Execute a dependent construction with later fields consuming earlier results. Supply the actual values prescribed by its formal dependent interface. Another admitted record requires no construction-specific runtime case. |
| MM010 | Make the same selected public computation directly and through a deferred or provider request. Both paths preserve the same operation, parameters, comparisons and dependent inputs through common mathematical preparation. |
| MM011 | Add an independently authored category with immediate functors, then apply an unchanged target consumer. Add a generic operation and apply it to existing eligible objects. These extensions require no accommodation edits to old categories or leaves, respectively, under the C12 frozen-baseline procedure. |
| MM012 | Replace a computational provider while keeping the mathematical context fixed. Formal denotation remains fixed; different coverage or an incorrect answer remains an execution or correctness issue. The kernel does not compute an unpublished value by Lean reduction. |

Each scenario includes subsequent mathematical use where specified. The complete original
acceptance workload and independent assertions remain required. These scenarios do not authorize
candidate authors to author independent expected answers or reduce acceptance to finite examples.
