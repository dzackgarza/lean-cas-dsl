# Reuse record: `cc-dsl-language`

## Engineering notes for the work issues

The current architectural direction is recorded in
[#85](https://github.com/dzackgarza/lean-cas-dsl/issues/85). Interpretation work is in
[#66](https://github.com/dzackgarza/lean-cas-dsl/issues/66), execution work in
[#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69), and the delivery sequence and
acceptance obligations in [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10).
This file records source evidence, reuse candidates and technical implications for those
issues. It does not set a separate work order or change their instructions.

The boundary described in #85 runs from catalogue selection through Lean's ordinary term
formation to a complete typed dependent computation. Its application, dependencies, result
interface and later use remain associated. Existing reader mechanisms are examined below
as implementation evidence, without assuming they are the architecture to retain.

## Owner

- `lean-categories` owns categories, structures, dependent declarations, admission hypotheses,
  literal and binder meanings, functors, selected routes, comparisons and their laws. The
  catalogue supplies canonical declarations and their public surface names; the kernel
  introduces no translation ontology or mathematical replacement.
- Lean owns ordinary term elaboration, application, local contexts, substitution, typeclass
  synthesis within the selected context, and kernel type checking. These facilities do not
  decide between mathematically distinct structures, routes or comparisons.
- The kernel owns selection under the catalogue's rules, lowering a complete selected
  application into computation, and preserving it through the public execution boundary.
  Mathematical acceptance remains independently authored in the permanent suite.

## Queries

The original corpus searches and their results remain available in the
[immutable pre-replacement record](https://github.com/dzackgarza/lean-cas-dsl/blob/0cee529c343fbe1c5f7a5f1326d4b805cc8fed44/specs/reuse/cc-dsl-language.md).
They included `custom syntax category DSL elaborator declare_syntax_cat`,
`parse external file runParserCategory`, `surface notation registry name lookup`,
`structured parameter provenance`, `selected object parameter transport`,
`forallMetaTelescopeReducing`, `Polynomial.C`, `deltaExpand`, and
`registered callable dependent parameter provenance`. The recorded matches did not provide
this application's selection and lowering boundary. That result does not establish that the
existing reader is the right implementation or exclude a suitable computation representation.

The replacement assessment follows the actual selected application through
[`Value`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/Language.lean#L335),
[`applyFamilyWithOwners`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/Language.lean#L5581),
[`recognizedEndpoint?`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/Language.lean#L8257),
and [`ComputationDerivation.compileAt`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/ComputationDerivation.lean#L307).
These are evidence for responsibilities to replace, not accepted foundations.
The [#85 analysis](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6570584402)
and [prior-art assessment](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6570686947)
connect these reader mechanisms to later result recovery. The remaining reuse questions
concern concrete representation and API fit across that complete boundary.

## New code: complete selected application and typed lowering

The following engineering analysis develops the boundary in #85 and the mathematical
application and execution obligations in #66/#69.

Selection resolves the mathematical declaration, complete structures and parameters,
admission data, source and target, and any route or comparison required by the written
question. It preserves unresolved ambiguity. It cannot use implementation availability,
registration order, carrier equality or a timeout to choose a meaning. Lean's ordinary
overload or instance search does not substitute for this selection; already selected
declarations and dictionaries remain the inputs to elaboration.

Lean's elaborator can form ordinary applications and local terms from the selected
declaration and context, with arguments elaborated at their dependent types and the complete
result checked at the original expected type. Ordinary elaborator unification serves this
purpose. A second application engine that opens a fresh telescope and guesses mathematical
witnesses would reconstruct the already selected application. A generalized point, categorical
map or admitted binder retains its declared mathematical interpretation even when Lean
represents part of it with a lambda or a local declaration.

Lowering the complete application into a typed dependent computation retains
the formal request and selected input occurrences, executable dependencies, result field
roles and interfaces, explicit comparison actions, and the continuation's use of the actual
returned fields. A dependent result interface can bind an apex and then a map from that
apex; it need not know the returned data before execution. What is fixed before execution is
the dependency and mathematical interface, not the backend's eventual answer. Actual data
and its lifetime information fill those prescribed positions.

The concrete computation representation has not been validated by this record. Its fit
includes the continuation's use of actual results. Existing `Value`/trace structures and
external packages need assessment against that responsibility. A datatype containing legacy
recognition callbacks would retain the reconstruction boundary.

### Existing sources and limits of reuse

| Responsibility | Primary source | Technical fit and limit |
| --- | --- | --- |
| Ordinary dependent application | [`Lean.Elab.App`, `Term.elabAppArgs`, Lean v4.33.0](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Elab/App.lean#L1338-L1353) | Use Lean's application elaboration for the already selected declaration. `expectedType?` propagates information but does not itself check the completed result type; retain the final check. This API does not justify keeping a mathematical witness-search engine around it. |
| Ordinary binders and local terms | [`Lean.Elab.Binders`, `Term.elabBinders`](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Elab/Binders.lean#L242-L263), `elabTermEnsuringType`, `withLocalDeclD`, `mkLambdaFVars` | Reuse scoped term formation. The catalogue still supplies a binder's actual domain, admission and generalized stage. A Lean lambda alone does not supply those choices. |
| Local definitions and closure | [`Lean.LocalContext`](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/LocalContext.lean), [`withLetDecl`](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Meta/Basic.lean#L1905-L1927), `mkLetFVars` | Preserve or close the local context. A transient `FVarId` or normalized right-hand side is not an execution occurrence. Definitions retain their actual evaluation-at-use semantics. |
| Existing selected declaration elaboration | [`DirectConstruction.elaborate`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/DirectConstruction.lean#L19-L84) | Existing use of Lean elaboration is useful evidence. Calling it does not complete the replacement if callers subsequently rebuild arguments, endpoints or result interfaces through `Language`. |
| Catalogue selection and complete contexts | [`Semantic`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/Semantic.lean), [`CategoryContext`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/CategoryContext.lean) | Reuse operations that consume exact accepted declarations and structures. Preserve their mathematical responsibility; current wrappers, copies and reconstruction paths may be replaced. |
| Question identity and explicit export | [`QuestionIdentity`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/QuestionIdentity.lean), [`Trace`](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/CasCatalogue/Trace.lean) | Preserve complete question meaning, operand positions and contextual identity. Existing comparison and interning code is reusable where it represents those facts without making old producer wrappers authoritative. Ordinary execution need not serialize unused audit output, but preparation validation and complete requested exports remain required. |

These versions identify inspected APIs and mechanisms. They are not delivery pins or evidence
of compatibility for an unimplemented combination. Actual imports, dependency/toolchain fit
and any adaptation remain implementation evidence to establish. Computation representation
candidates and their limits are in [`cc-realize-2cat`](cc-realize-2cat.md); the old searches
do not establish a package choice or a blanket local-rewrite decision.

### Mathematical distinctions relevant to reuse

The interpretation and execution requirements in #66/#69 distinguish the following data.
These notes identify what a candidate representation needs to express; they do not retain
the older record's implementation prescriptions.

| Mathematical distinction | Preservation property |
| --- | --- |
| Selected objects versus their carriers | Keep `Maps`/`Vec` and distinct bilinear forms on the same module distinct. An anonymous carrier supplies no missing named structure or coercion. A declared forward forgetful action remains usable with its actual source and map. |
| Complete dependent parameters and maps | Retain coefficient objects, scalar constructors and maps, selected class dictionaries and closed admission hypotheses. Distinct compatible choices stay ambiguous; a chosen map is not replaced by an identity because its endpoints coincide. |
| Declared notation and overloads | Preserve the approved quotient-ring interpretation of `ℤ/n`, explicit functor actions and complete signature-based name resolution. A later requested operation must not choose another structure on the same carrier. |
| Generalized points, binders and definitions | Preserve the actual domain `S` of `S → X`, destructuring and stage projections, local generator binding, declared admission and evaluation at a definition's use. |
| Selected views and comparisons | Retain complete action arguments, orientation, endpoints, actual comparison components and required compatibility. Inverse action requires a supplied inverse; carrier equality cannot supply one. |
| Complete structured constructions | Preserve the chosen diagram, apex, legs, mediator or factorization, and creation/lift data. A public `K.leg(n)` keeps the accepted diagram-index interpretation and the actual selected construction. |
| Explicit result contexts | Preserve an admitted explicit target such as a subset or callable object through the complete application. An absent context does not authorize choosing a named object from an anonymous result carrier. |
| Formal admission and evidence presentation | Check accepted evidence at its original complete target, including Type-valued witnesses. Definitional conversion may establish a presentation change; it cannot change the selected predicate, dictionary, domain or mathematical value. Backend data supplies no admission proof. |

The [historical main reader record](https://github.com/dzackgarza/lean-cas-dsl/blob/0cee529c343fbe1c5f7a5f1326d4b805cc8fed44/specs/reuse/cc-dsl-language.md#L36-L377)
and [PR #67 reader record](https://github.com/dzackgarza/lean-cas-dsl/blob/b35ab54e1d87b99b5d91d5cc7efda8748b3377f1/specs/reuse/cc-dsl-language.md)
preserve the source investigations, controls and recorded evidence behind these distinctions.
Current acceptance work is tracked in [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10).
Historical claims that a probe passed are evidence only for their recorded source and scope;
they do not establish that the new lowering or current combined product works.

### Shared preparation boundary

Notebook/DSL preparation, public service preparation and derived-computation compilation
are entrances to the same mathematical operations. A notebook reader replacement would
leave the reconstruction mechanism in place if `ComputationDerivation.compileAt` or a
service callback still invoked the old application or endpoint recognition. A deliberately
staged new request can receive its own complete interface at preparation; that differs from
recovering missing information for an already prepared request.

Fresh telescope reconstruction of a selected application, endpoint-witness search/retry,
carrier-based producer recovery and callbacks into these mechanisms are concrete examples
of the boundary diagnosed in #85. Keeping them behind a new facade or as a fallback would
retain that mechanism. Independent mathematical observations and engineering controls of
substitution, ambiguity and ownership concern behavior, not the lifetime of those helpers.

### Evidence linked from the work issues

Implementation evidence for [#66](https://github.com/dzackgarza/lean-cas-dsl/issues/66) and
[#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69) can identify the representation,
actual imports and compatibility results, transferred responsibilities, removed recovery
paths, and preservation through actual subsequent use. Execution and acceptance results
belong with those work issues and [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10),
with their original scope stated. This source record establishes no replacement execution
or acceptance verdict.
