# Independent kernel MVP compositional source review

## Status and inspected inputs

This is a source-only review checkpoint, not an executed acceptance result. The reviewer is not an implementation author. No build, runtime artifact, acceptance output, leaf implementation, unrelated worktree, or unrelated review report has been inspected or used. Generic engineering probe source may be inspected as source; its presence is not evidence that it ran or passed. One unsolicited implementation-worker message asserted that its focused controls passed. That assertion was not requested, verified, or used, and the worker was asked to send only source information. All conclusions here remain source-derived; the report does not claim to have received literally no outcome statement.

The first inspected kernel is `61550fc15da227856a62276f40c60db4d2411ed8`, checked out detached for this review. The permitted mathematical declarations are from `lean-categories` at `2dbf2f576ef5a4a406294d083fc52666c0010282` in the supplied independent-interface checkout; the supplied public-contract snapshot is `aa8477de4aebc83823b88ac4885225e8fc13d9c5`. These exact revisions identify inspected sources, not an accepted release tuple. `INTENT.md`, `AGENTS.md`, and the kernel-MVP mechanism requirements in `specs/computational-core-plan.md` govern the assessment.

The whole-operation agreement consumer and destructured-product delta announced by the assigning session are outside the first inspected kernel. Their subsequent source reinspection is recorded separately below. No B0 acceptance, V1 acceptance, frozen-kernel readiness, or computational correctness is asserted here.

**Current bounded source verdict:** the earlier focused follow-up inspects kernel `7a407fc55687a2c253c0725f2b7141ac5e5f0a7d` and the supplied long-expression repairs through `9b09050b67100179024fccc79d9ae31eea1777d1`, followed by rigid-owner and stage changes at `a56008f2b4398d59e6a94d05b8a2d9d1e89913a9` and `64d9e22c7e08a602001336b3c7ac88b76f7e267c`. No remaining concrete source blocker was established in those named mechanisms after their recorded repairs. The three component-presentation findings identified at `1b441552e1b11e5364f3beca53f4cf435bd56519` are source-repaired by `737b45353d14a278f4f00928541e0704fb5a934f` and `e8075dfad3e52c1654fcfee4be74f59aacc2818b`; the bounded closure read found no remaining concrete counterexample to those three findings in the integrated source. The latest bounded review at `5d176cef3b1e2dfe51e03b97dd1a8122b73195ba` found no concrete blocker for the five assigned parameter-recovery risks, with the conditional argument below. The report's cross-revision permanence and explicit scope assumptions remain open qualifications. This is not an acceptance or whole-kernel readiness result.

## Concrete findings from the first pass

### Creation-limit resolution loses target-presentation multiplicity

`RegistryState.resolveLimit` in `CasCatalogue/Resolve.lean` rejects multiple direct presentations, but its creation-lift branch uses `state.limits.find?` to choose one target presentation for each lift. Distinct accepted rows sharing the same category and shape can therefore silently become a first-row choice behind a creation lift. Upstream `validateLimit` and `persistSemanticEntry` validate the declaration and distinct stable IDs; they do not impose uniqueness of category/shape. The direct and lifted branches consequently implement different ambiguity policies for the same generic source of multiplicity.

The required compositional invariant is that adding another applicable presentation cannot change a previously selected semantic construction through array order. Every full candidate must remain visible until an independently specified comparison or explicit selection resolves it. This is an extensibility defect, independent of any installed leaf.

The neighboring failure boundary also needs correction: `Semantic.limit` maps every string error from `resolveLimit`, including multiple direct presentations and multiple lifts, to `.invalid`. Unresolved semantic choice must remain ambiguity. No invalid mathematical input has been established by a multiplicity error.

### Defining-leg projection discards creation context

The `.limitProjection` branch of `Realize.realizeFresh` always calls `StructuredResult.projectData row result.diagram result.answer index`. For a created limit, `row` is the downstairs presentation, `result.diagram` is the original source-category diagram, and `result.answer` is the downstairs returned packet. The field projection thereby interprets those downstairs data as source-side ports without retaining the creation action. The independently published finite-set pullback lift supplies a category-changing source instance: its source is `FintypeCat`, while the registered downstairs pullback presentation is in `Type`.

The public contract explicitly provides `constructionLeg` carrying the complete `createdCone` packet and the exact typed index. The production projection path should preserve that source-side interface and its actual lower data rather than treating a source leg as the same downstairs field. A previous review formulation attributed this to necessary constructor/category unification failure; that formulation is withdrawn. The registered `PullbackCone.mk` and `BinaryFan.mk` data constructors are polymorphic, and `StructuredResult.dataPlan`/`dataProjection` instantiate them against the supplied diagram without forcing `row.category`. Loss of creation provenance is the established defect.

The invariant is that projection composes a fixed source-side formal leg with the corresponding actual computation descriptor, including every intervening creation action. The hostile case is a nonidentity creation lift whose lower representation cannot itself stand for the source-side defining map.

### Structured-callable validation falls back to grammar without its typed receiver

`ComputationalData.validateCallableAt` delegates `constructionLeg`, `constructionField`, `limitLeg`, `arrowHom`, and `subobjectInclusion` to `validateCallableData`. The latter ultimately accepts their general public grammar without checking the demanded hom endpoints or reconstructing their complete receiver interface. For example, the source path admits the grammar of `{"ctor":"arrowHom","args":[0]}`: `arrowHom` has arity one, and `0` is public scalar data. It has no complete Arrow record.

This fallback is reachable through `validateElementAt` for an `element` envelope whose selected descriptor matches, then `validateElementExpressionAt` for `point`, and then `validateCallableAt`. A complete `element(..., point(arrowHom(0)))` can therefore cross a boundary that is meant to reject malformed callable data. An analogous `constructionLeg` packet can contain a recursively grammatical but incomplete cone, because the grammar-only cone check requires only a nonempty apex field.

This finding concerns framing, not mathematical correctness. A well-framed wrong map must remain data for independent acceptance; a receiver with no defining map or wrong declared endpoints is malformed before correctness is considered. The missing invariant is that every callable-data constructor preserves the same expected full hom interface through recursive validation, regardless of whether an enclosing result happened to be validated elsewhere.

## Positive compositional structure inspected so far

The following are conditional source arguments, not execution evidence.

- `completeRoutes` is retained. It first computes a closed reachable category enclosure and only then invokes the upstream simple-route enumerator with a sufficient finite bound. Failure to close is an interpreter obstruction, not evidence that no route exists. The completeness statement is specifically about the upstream simple-route notion; unrestricted nontrivial cycles are not proved covered by this argument.
- Route comparison witnesses retain the exact cell, constructor context, prefix, and suffix. `Semantic.routeComparison` consumes accepted natural isomorphisms, applies the declared constructor action and its identity/composition comparisons, then checks complete functor endpoints. Endpoint equality alone is not used as a comparison.
- `ProofRefinement.construct` is retained. It fixes the complete forgetful image before solving remaining proposition fields, rejects missing nonpropositional chosen data, and kernel-checks the resulting proof-only object. The runtime stores and restores the complete computational source snapshot through the corresponding checked forgetful prefix.
- `CategoryContext` and `ReindexAction` carry actual category bundles and the original base map. Source and target checks include category dictionaries and complete fibre parameters. The accepted family realization determines reindexing and cartesian maps before computational data are consulted.
- `WirePayload`, `forwardPayload`, and `combinedPayload` distinguish formal interfaces from actual computational JSON. Transport wraps actual data in `map`, `compose`, or `functorAction` descriptors and preserves live dependencies; the formal expression is used for typing and provenance rather than as a recovered answer.
- `StructuredResult.dataPlan` fixes constructor-binder roles before the answer is supplied. `validatePlannedData` validates the ordered returned fields against that plan. Distinct roles are not collapsed because their formal objects happen to coincide. `StructuredResult.complete` pairs the independently supplied universal presentation with the actual opaque packet; its validation callback does not prove universality.
- `executePrescribedLift` is retained. It dispatches all four public fields in sequence for each prescribed component, in reverse structural-route order, validates each prefix at the actual endpoints, and advances with the returned object/inclusion. The completed packet is replay-checked against the independently fixed ordered lift plan. A formal lift plan alone does not count as an executed lift.

## Further first-pass findings

### An admission descriptor is not tied to its declaration's actual endpoints

The `admittedPoint` case of `ComputationalData.validateCallableAt` decodes the six public fields (object, parameters, domain, original source, selected target, argument), checks their public grammar, checks the supplied domain and target against the requested Hom, and validates the argument at the supplied original endpoint. It does not instantiate the named object's actual admission to derive that admission's input and selected output. The neighboring `constrainedPoint` case does perform the corresponding constructor/data-field check.

Consequently a registered object with some admission and grammatically suitable parameters can be named while the packet's endpoint fields describe a different admission. Endpoint agreement between fields supplied together is insufficient. The signature must come from the independently selected declaration; only then can the fields be checked against it. This is a malformed-interface finding, not a demand to prove membership, build an inverse, or accept an admission obligation from returned data.

### Judged execution propositions are absent from the initial serialized identity

The initial `Realize.claimQuestion` case `.judged question _ expected _` serializes the interpreted `Question` and expected orientation but ignores the proposition actually used by execution. `QuestionIdentity.equivalentClaim` separately compares that proposition. Holding the question, expectation, and trace fixed while changing the claim proposition from `True` to `False` therefore leaves the initial serialized identity unchanged, although the independent direct comparison rejects equality and execution has a different proposition.

This is a concrete disagreement between two public descriptions of full question identity. The invariant is stronger than preserving displayed syntax or truth: the exact typed proposition that execution evaluates must be retained before deciding it. Two different true propositions must also remain different when their full mathematical questions differ.

### Operation provenance is recovered by the first declaration match

`Language.applyFamily` records all three operation paths (direct nullary point, nullary point through a terminal comparison, and applied operands) using `state.operations.find? (·.declaration == declaration)`. `applyOperation` has already selected an `OperationEntry`, but does not pass its ID into those recording paths. Upstream `validateOperation` requires a unique `(category, name)` binding; it does not require a declaration to have one registration. Two different surface names on the same owner can legitimately refer to the same declaration.

Such a selected binding can consequently acquire the first other binding's trace and primitive dispatch address. This is independent of any leaf implementation or the equality of their mathematical maps. Selection must retain its exact accepted row, or explicitly resolve an applicable equivalence class before choosing a representation. It cannot recover that row from declaration equality and storage order. The new operation-equivalence consumer also needs its candidate operation IDs to agree with the retained child records when candidate results share an expression.

The same defect exists for named morphisms: `applyNamed` selects a specific `MorphismEntry` but passes only its declaration to `applyFamily`, which records the first matching morphism declaration. Upstream `validateMorphism` also allows distinct names to share a declaration. The selected-operation repair recorded below addresses operation rows, but the shared helper still needs the exact named-morphism/callable address. Its new unconditional operation-row lookup can also make an already supplied `callableAddress` ambiguous because unrelated operation aliases share the declaration. A fixed callable kind and address must not be reselected through another registry class.

### Short symbolic result tags bypass their selected declared interfaces

`ComputationalData.validateElementExpressionAt` checks `point` and `operationExpression` against their full interfaces, but `add`, `mul`, and `neg` only recurse. `numeral` and `generator` fall through to grammar-only `validateElementExpression`. In particular, `element(obj.sets.naturals, generator())` reaches a successful grammar check even though the independently published `obj.sets.naturals` row in `Foundation/Objects.lean` has no generator. The exact outer selected descriptor does not supply the missing inner operation.

The executable public-contract documentation says these short tags invoke the existing registered language operations. Their applicability and full selected types must therefore be checked, just as for the long operation-expression spelling. This finding does not require reconstructing a returned mathematical value, declaring every wrong answer malformed, or establishing an arbitrary membership obligation from leaf data. The narrower countercase is the complete absence of the requested public generator interface.

## Source reinspection of committed repairs and additions

These are source-only conclusions. No result from compiling or executing a probe is relied on.

| Inspected delta | Source conclusion |
| --- | --- |
| `be822ca6fa66df73e7a7abffc9a11b7de1a0bb0e` and `2bfd4121bee7319a28fb65b640d00739f8a3f6a3` | Close the specific creation-limit multiplicity and failure-stratum finding. `resolveLimitDetailed` enumerates every applicable lift–target-presentation pair and retains both IDs; `Semantic.limit`, `StructuredProjection.construction?`, and all three `Language` consumers propagate semantic ambiguity. The existing declared direct-presentation-else-creation policy is preserved. |
| `5ba653252a2ceff07c809de49bf8a886fa4c6685` | Closes the specific judged-proposition omission in source: `claimQuestion` checks the proposition, encodes it and its type alongside the complete question, and retains expected orientation. The new engineering probe source separately holds display text fixed, changes `True` to `False`, and distinguishes different true equality propositions. Its source is inspected; no execution is asserted. |
| `d735e134118b61bbad912d8b9989615a5eacdfc8` | Closes the production created-limit defining-leg defect in source. The created branch checks its exact lift, original source diagram, and shape-typed index, then emits `constructionLeg` with the entire retained `createdCone`. Only direct packets call the downstairs data projection. The independently checked formal leg is not reconstructed from lower returned maps. Recursive framing of this descriptor remains part of the pending validator repair. |
| `9391de985d00ae34d6781d8d538e4abce3e2d882` | Partially repairs admission framing: derives the actual declaration's input and result, retains the ordered prefix, and distinguishes a scalar admission from admission of an entire original function. A same-carrier foreign selected target still passes because the result check uses conversion without binding the expected target's named identity to the admission owner; the `Maps` versus `Vec` case in the permitted upstream `AdmissionOwnerProbes.lean` supplies the precise boundary. The target-head check should also follow the upstream `headBeta` owner normalization. |
| `15505319be8e53e76071e42c160e0e2a65e65930` | Closes the specific operation-row first-match path and raw canonical-key concern. All three operation-result paths receive the selected ID; `Trace.recordOperation` retains a binding-specific typed transparent child, separating aliases in trace and result-cache keys. Complete source/candidate records are ordered by finished `QuestionIdentity` encodings, and source deduplication uses the independent typed comparator. The neighboring named-morphism and explicitly addressed callable paths described above remain open. |
| `237ad2070a8fcf281c6c20e45a81dd7bc3ddd4ce` | Closes those neighboring exact-binding paths in source. An explicit callable kind/address ends unrelated lookup after checking its declaration and owner. Named morphism, action, binder, component, and registered-arrow consumers preserve the accepted address and use a binding-specific typed child. Declaration-only uses require a unique applicable binding; multiple aliases are not selected by array order. |
| `f9feda3b3f10bea2be924641933f145c9d0bef63` | Closes the reported admission-owner hole and the obvious structured-callable grammar escape. `admissionInterface` retains the expected named declaration after administrative wrappers and the packet's target descriptor must name that owner. Complete Arrow receivers and their actual defining-map endpoints are checked. Construction descriptors now derive a registered complete interface and validate every returned data port. Nested presentation selection and the exact creation-to-data-diagram standardization still need the additional checks discussed below. |
| `42c584b263ca8aead62c8c179420307475050f99` | Repairs the named-map transport path to reuse `carrierMorphism` and its complete accepted route applications; `ReindexAction.map` retains the original Hom endpoints and carries an explicit expected-type hint before and after reindexing. The limit multiplicity probe source retains immutable accepted aliases, reversed order, Cartesian lift/presentation multiplicity, and distinct missing/ambiguity strata. No outcome is inferred. The neighboring `ReindexAction.cartesian` endpoint-normalization issue remains below. |
| `a6337f5d0a3ea93d141ae2239d529d3aa3bf76af` | Closes the two reported remaining construction-validator composition defects in source. It checks and retains the exact accepted `Iso` from the actual mapped diagram to the data schema's diagram. It considers all full-arity retained presentations, including those in an independently supplied formal field, and tests each in isolated elaboration state against the requested port type. It no longer selects by traversal order. |
| `909856c86c907b7bce52ab74dc5920d617f31ad4` | Closes the arbitrary-inner-category fallback for constructed operation sources. `sourceTemplateWith` recursively realizes the fixed accepted `CategoryExpr`, shares repeated symbolic arguments, checks the constructor's accepted dependent interface, and rigidifies source parameters before routes can constrain them. `bindTemplate` and `selectedParameters` match the actual complete source recursively. Independent residual route/declaration parameters remain pending. This delta is reported integrated by the assigning session as `cc76ae67a868d77d881173eff6779e00acdf8e64`; the inspected implementation delta is `909856c`. |
| `b730efb2b719a4071e21e985df6a790b719228f3` | Adds class-wide computational selection after the complete operation class is validated. Each candidate retains its exact declared address, full parameters, staged/nullary original argument, and actual endpoint data. Applicable registrations are counted before one dispatch; there is no reply-dependent retry. The chosen actual packet is reframed only after its full formal result agrees with the canonical result. Also closes the specific `ReindexAction.cartesian` raw-Hom endpoint issue. |
| `d62ea8efbf7eb89701e9d546b291fba4a6bd5f25` | Adds kernel-owned `callableObserved` metadata on received whole-callable results, retained through proof snapshots and operation-class forwarding. The observation consumer checks it before interpreting recipe syntax, so a returned symbolic expression does not become a fresh operation request merely because its JSON tag resembles a pending recipe. |
| `52a723026f28dd824136798d926bc6a0c52ba20b` | The destructured-product fallback reconstructs an already declared product presentation at the fully selected carrier, checks equality with that whole carrier, obtains its projections, then retains the original selected object as context. It does not let unrelated retained parameters choose structures on the component carriers. The whole point and its original generalized domain remain the projected input. |
| `f368730a882141ca570a6504846ccfae26bbdcb1`, `78b546745001150ccc4d49e67da87909beb676fe`, `8f3d4d5c0c89d833ea6fe3a3689f1fc24c45c9e9`, and `24ad473c9f48697cd3d78c6bae0c21b87b12813d` | Introduce the complete operation class and its consumers. Initially inspected at coherent source `2bfd412`, with later exact-ID and ordering repair inspected separately at `1550531`. |

The independently supplied agreement specification is additionally inspected at `e2d5e3083956a213cd7573c206a42603ddbe5e36` (reported published commit `4acd7aff0350c5a84ce695e42eaadfd583ac343d`, tree `eecb528949d9cff60dfe54c06c19fdf12c17806a`). It explicitly requires universal whole-map agreement over the entire dependent source, route/declaration parameters, and numeral parameters before selected objects or operands are substituted. It allows checked definitional equality as agreement evidence and preserves both routes and all required endpoint transports. The related public-contract documentation checkpoint is `a3a44aad7bd5eda1659314d88243a4bf4bc8dbb6`; the executable `Port` contract is unchanged from the initially allowed snapshot.

### What the whole-operation addition establishes conditionally

`OperationAgreement.universalFamilies` opens the declared source category telescope, a rigid object, and rigid numeral parameters. It constructs complete routed operation applications before comparing their whole dependent functions. `compareSources` checks both full types and families, constructs `Eq.refl` only at that exact universal equation, and kernel-checks it. Only afterward does it instantiate the shared context at the actual selected bundle, receiver, and numerals, checking ordered arguments against the original applications. This rules out accepting equality merely at a convenient operand or numeral.

`validateSource` checks full route application arguments, category dictionaries, the first-binding rule, and the exact retained route-comparison witnesses. `validateComparison` reconstructs the independent universal comparison and checks the retained closed terms. `validate` requires one connected class and identical full results after the accepted comparison. The runtime wrapper checks its strict original-result child and forwards that child's actual JSON and metadata; it does not produce a computational answer from the universal proof. The snapshot and direct comparator retain the operation IDs, complete source records, universal functions, their types, the proof's proposition, and the ordered instantiation parameters.

The first addition used raw `reprStr`/`Expr.lt` source and candidate ordering. Those values include proof implementations and binder spelling which the established question-identity quotient intentionally ignores. Such an irrelevant change can reorder sources with different routes and hence change their index-based comparisons. Commit `1550531` replaces this with quotient-aware complete-record keys before indices are assigned; its source closes that reported invariance concern. The corresponding engineering controls were read as source only.

The new typed `Trace.operationResult` wrappers also create a separate permanence obligation. They contain a nonpropositional binding string around an otherwise existing expression. The current typed question quotient does not generally erase arbitrary transparent data wrappers. Correct alias distinction within the new source therefore does not itself establish that every old successful question retains its old cross-revision identity. That needs an independently justified representation migration or a narrowly specified quotient that still retains the selected binding. This review has not compared runtime snapshots across revisions.

The published universal context additionally includes independent route or declaration parameters `q`. The initially inspected implementation rigidifies the source schema telescope, object, and numerals, then rejects any other unresolved parameter in `applicationAt` or `routedApplication`. Its unnamed-constructor fallback also used an arbitrary base category instead of the fixed inner expression. Commit `909856c` repairs the latter by reconstructing and abstracting the full fixed source template before routes are considered. The independent residual-parameter case remains pending: a declaration or route parameter not determined by that source must become a rigid universal binder before selected values are used. Such slots may be shared only through an accepted common context or exact shared route prefix, not because their selected values happen to coincide. The current lack is a conservative non-merge, not an established unsound equality. Generic readiness needs the full supported context or an explicit coverage restriction; successful ring, field, or algebra examples cannot discharge it. No installed-row execution failure is asserted.

### Remaining projection-validator composition checks

At `f9feda3`, `ComputationalData.constructionInterface` obtains the formal lower presentation at the actual composite diagram using `Semantic.limitPresentation`; that helper does consult the row's accepted standardization. The validator separately rebuilds a data diagram by applying the registered diagram constructor to mapped inputs. It does not check that the accepted standardization has exactly this rebuilt diagram as its other endpoint. The production construction path in `Realize` does check that complete `Iso` type. The validator needs the same relation before attributing the complete lower data packet to the original created construction. A merely well-typed alternative standard diagram is insufficient.

`retainedConstruction` also selects the first same-row presentation occurring anywhere in the demanded field type. That traversal position does not identify the requested projection. For a coproduct leg whose source is an earlier coproduct built by the same row, the earlier source-side presentation can occur before the new target presentation. The complete requested Hom type and port must select the compatible occurrence; nested uses of the same accepted construction are not an ambiguity to resolve by traversal order. Commit `a6337f5` closes both this traversal-order defect and the exact standardization relation described above. Its validator checks every full-arity candidate in isolated state; success establishes framing against the fixed expected port and does not select a mathematical witness from returned data.

An additional claimed defect concerning `constructionField` was withdrawn after rereading `StructuredResult.dataPlan`. That plan uses a polymorphic registered constructor against the source diagram and created presentation. Its explicit requirement that the formal presentation expose the declared field schema remains a conditional completeness assumption, but the review has not established a concrete failure of that requirement.

### Operation-class execution and terminal-point composition

At `b730efb`, `realizeArrowObservation` first revalidates the entire semantic class. It prepares a complete actual `PointInvocation` for each retained candidate and checks its exact live owner, then obtains all applicable exact and category-wide registrations without starting an operation process. Zero choices are a realization gap; multiple choices are realization ambiguity. One choice is dispatched exactly once, and malformed or unavailable output does not trigger another candidate. `forwardOperationEquivalent` checks the chosen result's complete formal value and type against the canonical result while forwarding the chosen actual JSON and owner. The original class and canonical interpretation are retained. These are source invariants, not evidence of successful execution.

The counted choices are pairs of candidate invocation and admitted registration. If two distinct same-ID application contexts remain in a class, one registration applicable to both appears twice. This implements conservative ambiguity between complete invocations; it must not be described as deduplication/counting of distinct registration records alone. No assumption that such distinct contexts cannot occur was established by the review.

`d62ea8e` separately records whether a whole callable has already been observed. This addresses the hostile boundary where a valid symbolic reply happens to have the same tag as its original recipe: actual output remains output, rather than a request inferred from leaf-controlled syntax. Proof-refinement snapshots and class forwarding preserve that marker.

The closed-point branch of `realizeClaim`'s `.homs` case still sends an uncomputed complete `operationExpression` to equality instead of demanding that operation's separately registered computation. This is a valid public representation: `CasContract/Port.lean` at `aa8477de` explicitly permits these portable expressions and assigns their native lowering to the consuming leaf. It is not itself malformed framing. However, it does not establish the stronger extension argument in which a new operation's own implementation produces data for an unchanged old equality implementation. Nothing in the public sources guarantees that every old equality implementation understands every future operation address. The direct point-invocation form and subsequent consumption of actual returned data are also published. The assigning session plans a pre-dispatch demand path that recursively materializes installed operation dependencies while retaining portable recipes where no dedicated registration exists, without catching or retrying a failed dispatch. That plan is not an inspected implementation at this checkpoint.

## More detailed compositional boundaries

### Selected dependent elaboration and admission

`parameterTrial` and `optionalReading` isolate candidate metavariables and trace state; only invalid candidate formation is discarded. Ambiguity and internal failures propagate. `typedParamTerms` supplies a dependent telescope in order. `typedParameter`, `bindSelectedReceiver`, and `applyFamily` check the actual whole selected objects and dictionaries rather than filling a structure from its carrier. `applyFamily` retains the complete declaration application, including implicit parameters, synthesized instances, supplied maps, and the original generalized domain. A product-valued single operand stays one operand; two supplied operands request the declared binary factors.

Named admission fixes the actual selected object, extracts the declaration's input binder, and discharges its obligations from independent formal evidence. `ConstrainedPoint.construct` permits its specific one-data-field record only after checking the supplied proofs and preserving the original domain. Binder candidate trials choose a unique declared complete source before admission; `selectedBinder` checks the entire already admitted family and retains the declared range and original point. Independent variables become projections from registered products of their exact selected domains.

The hostile boundaries are same-carrier objects with different structure, a family with an ignored parameter, a non-global generalized point, missing proof obligations, and several applicable readings. The code must preserve their distinctions before execution; leaf availability is absent from this selection process. The initial operation/callable provenance defects are repaired in the inspected exact-binding deltas above; cross-revision permanence remains a distinct obligation.

### Computational transport and ownership

`contextualAction` verifies each accepted complete edge application against the current full bundle, constructs `map` or `functorAction` on the current actual JSON, and carries all parameter dependencies. `contextualComposition` checks the fixed categorical composition and preserves its original domain. `frameMorphismData` supplies exact typed endpoints for a graph, or transports an existing endpoint presentation with the independently accepted directed comparisons. A comparison is never inferred merely because two data endpoints are equal or two carriers reduce alike.

Computational ownership is an exact backend/live-session pair. Nested opaque tokens acquire that pair at receipt, and combining or forwarding data preserves compatible dependencies. Dispatch rejects a missing or different original session; reopening a process under the same backend name is insufficient. This argument assumes the current sequential harness exchange discipline: the request/reply exchange and connection-owner lookup are not shown to be one synchronized transaction for concurrent use of a shared harness.

An additional portability limitation should not be misreported as a safety defect. Several result paths conservatively merge request ownership into wholly inline new replies, while some point/presentation paths retain only reply ownership. The public contract does not explicitly promise that every materialized inline reply must shed its request's dependency. The inconsistent restriction can prevent reuse, but the inspection does not establish an unauthorized opaque-session escape.

The `42c584b` map repair preserves a raw `Quiver.Hom` interface before reducing a concrete bundled morphism's type. The same issue was identified in `ReindexAction.cartesian`, which reduced both the base-map type and returned cartesian-map type before checking the categorical Hom head. Commit `b730efb` now preserves both original Hom types before any fallback reduction. This closes that specific endpoint-retention obstruction in source; no executed counterexample or pass is asserted.

### Complete results and prescribed lifts

`StructuredResult.dataPlan` keeps each constructor binder's role before formal unification, so coincident formal objects do not merge distinct data ports. Ordered fields are checked against their dependent interfaces, including prior actual fields. The independently accepted cone fixes mathematics; the retained complete packet fixes computational projections. An incorrect but well-framed returned apex is data for independent correctness assessment, not a reason to replace it by the formal apex.

Creation lifts validate their actual lower packet before using the independent formal presentation and the accepted `CreatesLimitsOfShape` structure. `executePrescribedLift`, `selectedLiftExecution`, `cacheLiftFields`, and `executeLiftFactor` retain the complete ordered component outputs. Each subsequent stage receives the previous actual object, inclusion, or factor; suffix caching retains the corresponding exact selected lift plan and owner. Neither the four-field framing nor the formal factorization proves the returned maps satisfy the universal laws. The production created-limit leg repair preserves the complete source-side packet; the remaining independent recursive-validator checks above still matter for reuse.

### Full questions and failure separation

The typed expression quotient removes metadata, binder names, and proof implementation while retaining the full proposition type of a proof. It does not reduce arbitrary data expressions merely because their current values agree. Complete parameter dictionaries, maps, base morphisms, admission/binder choices, and route comparisons remain visible. The independent direct comparator traverses typed claims and trace nodes rather than trusting serialized DAG bytes or revision labels. Its guarantee is in the current mathematical environment; cross-revision changes to constant meaning still require independent assessment.

Interpretation fixes the claim, trace, and identity before evaluation. Invalid formation, semantic ambiguity, realization gaps, backend unavailability, malformed data, and internal failure have distinct paths. `executionFailure` does not turn an execution error into mathematical invalidity or semantic ambiguity. The initial limit-stratum and judged-proposition defects were concrete exceptions; their source repairs are recorded above. No whole-inventory permanence or acceptance conclusion follows from inspection of these mechanisms.

### Public encode/decode boundary

The public encoders retain complete operation, input, parameter, endpoint, and orientation fields. Dispatch checks registered operation/input addresses; competing implementations are not ranked by incidental availability. Typed map and ordinary callable validation carries expected interfaces recursively; plain-data codecs do not manufacture mathematical proof fields. The reported admission-owner, Arrow-receiver, and construction composition bypasses are source-repaired. Short element-expression tags still need closure. An enclosing descriptor's correct name is not enough when a nested callable can avoid its complete receiver signature.

The authority argument is limited to the active computational reply paths inspected. Legacy public helpers remain: `StructuredResult.reconstruct` and `Realize.fixedConstructionComparison` can decode maps and prove inverse/cone equations; `preserveResultComparison` can replace answer JSON with fixed JSON in one branch. No callers of `preserveResultComparison` or production invocation of `StructuredResult.reconstruct` were found. The ordinary scalar/finite observation decoders and independent input-graph transport checks are a different boundary. The review does not infer a live reply-to-proof leak from these definitions alone, but neither does it certify every exported legacy entry point as a data-only API. An absolute claim about all consumers requires that additional boundary to be made explicit.

## Remaining work and evidence limits

The first pass ended at the assigning session's request. Its focused follow-up is recorded below. The cross-revision wrapper permanence obligation, conservative candidate-invocation multiplicity policy, and explicitly scoped legacy authority/concurrency assumptions remain separate. Fresh independent frozen-source trials, compilation, runtime ownership trials, hostile framing executions, permanent mathematical acceptance, and cross-revision question permanence are outside this review's evidence. None is inferred from examples or from the presence of engineering probe sources. This report makes no B0, V1, or frozen-ready claim.

## Focused follow-up at `7a407fc`

The review worktree was moved, while clean, to the assigning session's committed kernel `7a407fc55687a2c253c0725f2b7141ac5e5f0a7d`. Its `INTENT.md` and `AGENTS.md` are unchanged from the initial inspected kernel. The prior review text is already present unchanged. This follow-up inspects only the previously identified composition boundaries and supplied committed repairs; it introduces no implementation changes and uses no runtime results.

| Exact inspected delta | Source assessment |
| --- | --- |
| `b82350028fd58783ac9219ac613a6b346b18fdfa` and `32c5b9f41122a45fdeaedf19711c16fb57329c62` | Close the reported residual-context omission in the operation-agreement comparison mechanism. Source parameters are rigid before route templates; remaining independent parameters, receiver, numerals, and universes become part of a closed universal family before comparison. Exact actual instantiation is checked afterward. |
| `0343a5a6da6c8d8729e90743b0a761cee9e54fac` | Extends `StructuredResult.dataPlan` to opaque formal cones through the registered constructor's own direct projection identities. It does not reconstruct a universal witness from data. |
| `02be3b880ab00f95082c9b1490d3aa6db0ab0ca8` | Closes the original grammar-only short-tag bypass by checking the selected registered primitive or complete operation class first. Its interaction with long-form operand selection exposes the concrete composition defect below. |
| `1114e311ae6adf9764fa1e813fb86b1fdb310f73` | Retains complete Arrow/full-subcategory receiver context from the independently fixed Hom type, tests all compatible complete receivers, and validates the actual packet without extracting a predicate proof from it. |
| `d839cc76c0f2fce723ee62991a96ec9c223d9c30` | Adds the previously missing installed-operation demand to ordinary realization, including closed points. Dependencies are demanded before downstream recipes are assembled; absent applicable registrations preserve the portable expression, while ambiguity and actual dispatch failures do not trigger recipe fallback. |
| `b658d7b5a08890b2a58cf5ec4f2cfa7173d9a8a2` | Repairs the long endo-operation's exact owner-slot check in both `ComputationalData` and `ElementData`, and threads a retained operand selection through short-tag recursion. Its first operand-selection implementation still needs the complete declaration parameters converted into available typed witnesses, as explained below. |
| `9b09050b67100179024fccc79d9ae31eea1777d1` | Closes that remaining operand-selection issue through `Language.operationParameterObjects` and `declaredEndpointObject`. It derives typed retained witnesses from the complete application, fixes the owner category from the accepted row, retains all compatible category schemas for other parameters, and resolves each operand at its original declared source expression. Invalid or ambiguous operand interfaces in reply data become framing errors; internal failures propagate. |

### Universal residual contexts

`withSourceTemplate` fixes the accepted source expression and abstracts its dependent parameters before any route can constrain them. `routedTemplate` shares a template only for an identical ordered route prefix from that same source. Separate declaration and route parameters otherwise remain independent. `universalPlan` includes the complete route applications and declaration prefixes in the abstraction input, even when a returned operation ignores one of those parameters. It checks that the receiver and numeral placeholders have not been specialized, closes the complete term context, and then abstracts the remaining universes.

`compareSources` compares the full closed family types and functions and kernel-checks `Eq.refl` at their exact equality before calling `instantiatePlan`. The latter matches both complete source bundles and receivers, every numeral, both ordered route-application arrays, and both full declaration applications. `bindTemplate` descends through the declaration and its arguments before conversion can erase an ignored parameter. The retained parameter vector includes the selected universe levels as `Sort` terms. `validateComparison` independently reconstructs the same plan and checks the retained terms and proposition.

This closes the specific concern that a selected value, coincident numeral, or ignored parameter could substitute for universal agreement in these paths. An unspecified actual route parameter is still not invented: a concrete request must supply its full accepted context. The source controls exercise arbitrary precomposition, independent parameters, ignored arguments, and universe changes; their execution is not part of this assessment.

### Formal port recovery and stored subobject maps

`projectFormalDataPorts` reads only the independently accepted diagram, constructor schema, and formal cone. It identifies a port when a constructor projection reduces directly to that port: the cone point, whole transformation, whole component family, or a separately indexed component at an index supplied by the fixed diagram type's existing finite metadata. Multiple projections of one port must agree at their complete types. The resolved fields come from projections of the independent formal presentation. No backend field, cone law supplied by data, or equality with an actual returned apex enters this calculation. Data ports lacking those direct identities still fail explicitly; this is a stated schema condition, not evidence of coverage for an arbitrary unrelated constructor.

`retainedRecordReceivers` examines full projection applications in the independently expected Hom type. The stored-map validator checks all compatible retained records in isolated state and then validates the whole actual receiver packet at the selected Arrow or full-subcategory context. A raw subobject packet therefore need not reconstruct its mathematical predicate. An ordinary Arrow packet does not by itself introduce that full-subcategory context. No new source defect was established in these two focused repairs.

### Installed-operation demand preserves actual dependencies

`realize` now invokes `realizeArrowObservation` in its registration-only mode for operation results and operation classes. `realizeFresh` demands an operation's operands before assembling its expression; `elementExpression` then consults the actual-result cache and retains each returned packet and owner as a computational operand. `realizeUnobserved` prevents preparation of one class candidate from selecting that candidate's implementation before the complete class is considered. The `callableObserved` marker remains authoritative for received output, regardless of its JSON tag.

The fallback is pre-dispatch and explicit: no applicable admitted registration leaves a portable expression. Several applicable invocations remain realization ambiguity, and an actual malformed/unavailable/wrong computation does not cause another implementation or recipe to be tried. Thus the earlier unconditional terminal-point bypass is removed in source. This is the required compositional mechanism for a separately installed new operation to feed actual data to an old consumer. It does not establish that any particular execution, result framing, or unchanged leaf succeeds.

### Long expressions must retain each operand's selection

The `7a407fc` long `operationExpression` branch obtains complete operand types from its explicit registered declaration, but recursively validates each operand with the unchanged outer `selected` object. The new short-tag checks make that a concrete composition failure. The permitted public declaration `PowerSets.le` has a complete linear-order owner, two operands in that owner's underlying set, and a separately registered truth-values result. With owner `orderIntegers`, the long expression's integer `numeral` operands reach `validateShortTag` with the truth-values selection and the integer carrier. A point selected at the result cannot inhabit the operand's `1 ⟶ Int` interface. The same issue affects heterogeneous operand products. This is an interface countercase, independent of the comparison's truth or any leaf implementation.

The explicit linear-order owner is legitimate. An operation whose registered result is a separate set must not be required to use that result as its owner. Conversely, where the validator does require a structured selected owner for an endo-operation, its original `explicit.anyM` check is insufficient: an earlier same-typed parameter could match the selection while the declaration's actual owner slot holds another structure. The accepted schema places that owner immediately before the trailing numeral parameters. Commit `b658d7b` now checks that exact slot, including in `ElementData.read`; this closes the reported owner-slot hole in source.

The same commit threads a retained `Language.Value` through nested short tags, but initially obtains it by calling `Language.recognize` with only the outer result selection as a known value and the raw declaration arguments as `fixedParameters`. In the inspected `Language.recognize`, that raw array only disambiguates multiple already matched known selections; it does not create available object witnesses. For the separate-result example, the truth-values selection does not supply the integer-order owner, and the source expression `orderCarrier orderIntegers` is a carrier projection rather than the head of a registered set declaration. The complete accepted owner and relevant declaration parameters must first become typed retained values used by the existing endpoint machinery. Normalizing to a coincident named carrier would violate the selected-structure boundary.

Commit `9b09050` supplies that missing step in both the response validator and `ElementData`. `operationParameterObjects` examines the complete typed declaration application. The accepted row fixes the actual owner's category; other complete parameters retain every compatible registered category schema rather than receiving one by position or carrier equality. Each source is then passed unchanged to `declaredEndpointObject` with these witnesses and the full declaration arguments. That machinery follows actual field occurrences and declared endpoints, retaining complete selections and ambiguity rather than recovering a named object from a coincident carrier. The resulting operand selection is threaded through its nested short and long expressions. The validator also converts invalid/ambiguous operand selection into a data-framing error while preserving internal failures. This closes the reported residual source issue without equating the legitimate explicit order owner with its separate truth-values result.

### Follow-up verdict and remaining limits

At the inspected `7a407fc` plus `b658d7b` and `9b09050` deltas, the concrete long-form operand and owner-slot defects found in this bounded pass are source-repaired. The earlier residual-context, short-interface, opaque-projection, stored-subobject, and installed-operation demand findings have the conditional compositional arguments stated above. No remaining concrete source correctness blocker was established in those named mechanisms after the final supplied correction. This verdict covers the inspected repairs and their relevant source dependencies, not every intervening change or an arbitrary future extension.

The existing cross-revision wrapper-permanence obligation, candidate-invocation ambiguity policy, direct-projection schema condition, sequential shared-harness assumption, and explicitly limited legacy authority argument remain. These conditions must accompany any use of the review. No compilation, runtime success, computational correctness, B0, V1, or frozen-readiness conclusion is inferred.

## Final narrow follow-up: rigid owners and dependent stages

This additional read covers only the assigned committed changes and the source dependencies needed to assess them. It does not expand the review to other intervening changes. The governing `INTENT.md` and `AGENTS.md` are unchanged from the previously inspected base. No implementation or probe was executed, and no leaf source or runtime artifact was inspected.

| Exact inspected delta | Scope and source verdict |
| --- | --- |
| `a56008f2b4398d59e6a94d05b8a2d9d1e89913a9` | `CasCatalogue/OperationAgreement.lean`: the new `bindOperationTemplate` accepts a transparent presentation only at the exact complete owner slot, after that owner is closed. The independent source, route, declaration-parameter, numeral, and universal-proof boundaries remain intact in the inspected callers. |
| `64d9e22c7e08a602001336b3c7ac88b76f7e267c` | `CasCatalogue/Language.lean`: `restage` preserves the unreduced categorical Hom interface, and scope/binder results now enter that existing restaging path. The generalized-map preflight reads its argument against the function's retained source carrier; the existing full composition checks still determine validity. No new concrete type/domain-preservation defect was established. |

### The exact owner slot admits conversion without assigning an owner

The permitted upstream `OperationEntry` interface places the owner immediately before its trailing numeral parameters. `bindOperationTemplate` checks the registered declaration head, full application arity, actual application closure and typing, and then locates exactly that slot. It requires both expected and supplied owners to be closed before comparing their complete types and values under Lean conversion. Carrier equality alone does not satisfy these checks. Every other argument, including independent declaration parameters and numeral arguments, still passes through the unchanged recursive `bindTemplate`; the helper does not normalize the whole operation before checking its arguments.

The order at the two callers is decisive. `instantiatePlan` first binds both complete source bundles and receivers, all numeral slots, and both ordered arrays of complete route applications. Its owner expression therefore comes from the fixed source and those independently matched routes. `validateSource` separately reconstructs the owner from the retained source receiver and the checked route composite before forming its operation template. A remaining unresolved owner is rejected rather than determined from the supplied operation. This per-candidate check establishes a valid source description; it does not itself establish agreement with another candidate.

`compareSources` is unchanged: it closes the full universal families, checks their complete types and equality, and kernel-checks the exact equality witness before calling `instantiatePlan`. Independent declaration and route parameters have already been abstracted at that earlier stage. Allowing conversion of a closed owner during the later instantiation therefore cannot make two independent universal owners equal, specialize a numeral to make an equation true, or select an operand to establish agreement. This remains consistent with the supplied upstream whole-operation agreement specification at `e2d5e3083956a213cd7573c206a42603ddbe5e36`.

The hostile boundary is a different structured owner with a coincident carrier, or an ignored independent argument hidden by the returned operation's reduction. The former still needs equality of the complete already-fixed owner value and type; the latter remains subject to recursive argument matching and the prior universal proof. The narrow conversion allowance does permit a named owner and a transparent expression for that same full owner. It does not replace the original candidate application or its source records: `encodeCandidate` retains the actual full application, and `encodeSource` retains the complete bundle, receiver, route applications, and comparisons. This is an instantiation check, not a new question-identity normalization or permission to erase selected syntax. The earlier cross-revision question-permanence qualification remains unchanged.

### Restaging preserves the original point and generalized domain

`restage` now examines `inferType h` for its `Quiver.Hom` endpoints before attempting reduction. This prevents reduction to a concrete function representation from hiding a categorical point's domain. For an element at current stage `S`, it leaves an existing domain `S` unchanged and also leaves an unrelated nonterminal domain unchanged. Only a point whose source is the registered global terminal object is passed to `staged` and `throughTerminal`. Those existing helpers compose the registered terminal map `S ⟶ 1` with the original point `1 ⟶ X`; the retained target value stays `X`, and the composition trace keeps the original point as a child. Scope expansion and element-valued selected binders now use this same path. The binder's prior admission, exact domain, operation, and trace are not replaced by a fresh point.

The `apply` preflight now obtains its ambient argument context from `carrierObject originalSource`, where `originalSource` comes from the complete selected function's `morphismContext`. If the argument is itself a complete map, the subsequent branch still checks both full category bundles and the common intermediate endpoint, constructs their categorical composition, checks its full source and target, and returns the original argument's source value. A typed ambient does not authorize treating an arbitrary generalized map as a global point. Ambiguity and internal errors are not swallowed as an invalid speculative reading. The added engineering probe sources were read only as descriptions of these boundaries, not as executed evidence.

### Narrow follow-up verdict

No new concrete source correctness blocker was established in these two deltas. The full-owner allowance remains confined to a closed independently obtained owner, while all other selected arguments and original descriptions remain retained. The stage changes preserve the original point and the independently selected generalized domain through a registered composition. This is a conditional source assessment of the stated paths. All previously recorded scope conditions and open qualifications remain; no compilation, runtime outcome, mathematical acceptance, B0, V1, or frozen-kernel readiness is asserted.

## Bounded component-presentation review at `1b44155`

This source-only follow-up inspects `1b441552e1b11e5364f3beca53f4cf435bd56519`, specifically `Language.refinedComponentPresentation?`, its `componentElements` caller, and the existing helpers and trace consumers needed to assess the new path. The permitted upstream `ObjectEntry`, `ObjectRefinement`, `ObjectComponents`, and `validateObject` declarations at `2dbf2f576ef5a4a406294d083fc52666c0010282` determine the admitted generic cases. The governing instructions are unchanged. No build, executed probe, runtime artifact, or leaf implementation is evidence for this follow-up.

### What the full-object check preserves

The new helper requires an already selected structured source inside the carrier value and does not begin from a bare set. It instantiates a candidate refined declaration in isolated elaboration state, matches the complete object type and value against that source, and closes all declaration arguments before using its base's components. Later checks compare the actual carrier, complete explicit parameter arrays, arity, and the whole typed projection family. Different complete parameters or component families produce semantic ambiguity before candidate IDs are sorted. Thus no carrier-only inference or traversal-order selection was found in those full-object and whole-family checks themselves.

For an admitted candidate set that reaches those checks, the return value keeps the actual carrier and original point. The fresh `id actual` wrapper separates its new identity-class trace key from the original source expression, and its evidence includes the selected source and named views. The original registered projection is then applied to the original generalized point. These local invariants do not discharge the candidate-admission and computational-consumer issues below.

### An unrelated non-set refinement can abort candidate discovery

`refinedComponentPresentation?` calls `setOf state row` for every same-category row with `refines.isSome`, before checking that row against the selected object and outside the optional candidate reading. `setOf` throws `.invalid` when the refinement reaches an unrefined object outside Sets.

The permitted upstream `validateObject` requires a refinement's base to be unrefined and checks its complete structural route and isomorphism. It does not require that base to belong to Sets. A valid same-category refinement into another structured category can therefore abort this scan even when it is unrelated to the independently selected object. Adding that ordinary row can invalidate an otherwise unchanged component reading before eligibility is established. This is a concrete generic admission defect, not evidence that the selected object itself is invalid. Non-component candidates must be excluded without suppressing ambiguity or internal failures of genuinely applicable candidates.

### Generic recognition loses the exact admitted row when aliases share a declaration

After matching a particular row, the helper calls `recognize state application.value category #[] application.explicit`. That recognizer searches all registered objects with the same category and declaration head, then requires exactly one matching row. The accepted object validator prohibits duplicate stable IDs and duplicate names in a category; it does not prohibit distinct names/IDs sharing a declaration.

Two valid refined aliases may therefore share the same declaration, complete parameters, base object, arity, and component family. Each is an eligible full presentation under the new helper's stated rule. Nevertheless, the generic recognition call finds both and throws `.invalid` before either can be collected and compared. The exact row already selected by the outer iteration has been lost. The required invariant is to construct each retained presentation from that exact checked row and then compare all eligible presentations; an unrelated unique-declaration lookup cannot substitute for that step.

### The new wrapper's consumers do not yet preserve its original computational child

The helper records `wrapper := id actual` as `.parameterEquivalence expected actual alternatives`. This keeps the original expression available as a distinct child. However, `Realize.realizeFresh`'s existing `parameterEquivalence` branch uses `representative` only for definitional-equality and proof checks. It then realizes `sources[0].object` and transports that chosen named source. It does not realize the new wrapper's distinct `actual` child. `Realize.parameterData` likewise encodes the first named source and route directly; its comment explains that this avoided the older node's self-recursion.

For a complete anonymous or computed selected object, `coalesceSelectedParameterViews` can retain that original value in its contextual views while contributing no original named `ParameterPresentation`. The alternatives can then consist solely of the newly recovered named presentations. If the wrapper is demanded computationally, the inspected consumer follows one of those presentations rather than the original computation and its exact packet/session owner. Keeping the original expression in identity data does not establish forwarding of its computational data. A formal full-object equality cannot certify or replace the data returned by that original computation.

This is an unresolved compositional boundary established from the actual consumer paths. The review has not executed a surface program that demands the wrapper, and does not claim an observed packet substitution. The new distinct-child design needs a consumer argument that preserves the original data when demanded, with the checked presentations remaining formal context. The existing first-source fallback for older self-referential nodes cannot by itself provide that argument.

### Component follow-up verdict

The full-object and whole-family checks support a conditional ownership argument. The two concrete candidate-admission defects prevent an unconditional generic source-correctness verdict for this new mechanism at `1b44155`, and the original computational child must be accounted for in its consumers. These findings were sent to the assigning session with their function references. This bounded pass adds no implementation, mathematical registrations, acceptance changes, or broader audit. The earlier inspected repairs and all existing evidence limits remain as recorded.

### Source repair of original-child forwarding at `737b453`

Commit `737b45353d14a278f4f00928541e0704fb5a934f` changes the two identified consumers while retaining their full presentation, route, type, and identity checks. After those checks, a `parameterEquivalence` node whose representative is syntactically distinct from its key follows that original child. `parameterData` encodes the child; `realizeFresh` realizes it through the normal cache and execution path, checks its complete result type, and returns `{ actual with payload := forwardPayload actual e actual.json }`.

The record update preserves `form`, presentation isomorphisms, object and endpoint presentations, morphism framing, the callable-observed marker, proof-source snapshots, lift execution, category context, and retained construction inputs. The forwarded JSON is exactly `actual.json`, and `forwardPayload` preserves its exact backend/session owner and whether it is computational data. The formal term changes to the checked wrapper; no named presentation or formal expected answer replaces the actual JSON. `realizedParameters` sends traced or cached parameters through `realize`, then keeps both this JSON and the resulting Wire dependency, so later parameter use retains the same owner.

For the new `id actual` node, following the original child is not recursion through the wrapper's own key. Historical nodes whose representative equals their key retain the previous named-source fallback; this repair does not claim a new general acyclicity theorem for arbitrary trace graphs. The repair also preserves the previous checks of all named alternatives before forwarding, so those alternatives remain formal identity evidence rather than a source of computational authority.

`CasAcceptance/Kernel/ParameterResultReuseProbes.lean` was read as engineering assertion source only. It constructs distinct named, actual, and wrapper expressions; supplies a cached owned packet; and asserts preservation of packet, owner, category context, repeated use, and later parameter dependencies. These assertions were not executed or used as outcome evidence. The complete metadata-preservation argument above comes from the record update and payload helper, beyond the fields explicitly inspected by that probe. No remaining concrete source counterexample was established for the reported distinct-child forwarding gap at this repair. The two candidate-admission findings still require their separate committed correction.

### Source repair of candidate admission at `e8075df`

The two candidate-admission corrections were first read at worker commit `374864308c8c6a902f07bf5fc987fe3e5596eaf2`, then checked in the integrated root source `e8075dfad3e52c1654fcfee4be74f59aacc2818b`. The integrated `Realize` consumer repair remains unchanged from `737b453`. This reinspection covers only the three reported component findings and their relevant dependencies.

`componentRefinement?` now runs each candidate in isolated elaboration state. It matches the complete declared object type and value and closes the application before asking `setOf` for a component base. A nonmatching object, an undetermined complete application, or a valid refinement without a set/component base is inapplicable to this recovery step. Candidate `.invalid` failures return `none`; semantic ambiguity and internal failures propagate. An unrelated non-set refinement therefore no longer aborts the scan. Neither a candidate's base nor its components can choose the independent structured source.

`recognizeObjectApplication` receives the exact already matched `ObjectEntry`, checks its category, reconstructs its dependent parameter values, and calls `registeredObject state entry values` directly. The component loop supplies that exact row from its successful candidate check. It no longer sends the whole candidate application back through the generic unique-declaration recognizer or a second name lookup. Distinct same-declaration aliases can therefore retain their own IDs and complete applications and both enter the existing candidate array. The prior comparisons of full explicit parameters, arity, and whole typed projection families remain before deterministic ordering; distinct families still produce semantic ambiguity. The complete original source and all checked named views continue into the retained evidence.

The added engineering assertion sources build immutable registry-state fixtures using the public object validator: one refinement with a non-set structured base, and two distinct-ID/name aliases of the same component declaration. They assert inapplicability of the former, exact retention of the latter, unchanged dependent parameters, and retention of both presentations under reversed candidate orders. These sources were inspected but not executed; their intended checks are not runtime or mathematical acceptance evidence.

### Closure verdict for the three component findings

At the integrated `e8075df` source, the two reported candidate-admission defects and the distinct-child data-forwarding gap have the conditional closure arguments above. No remaining concrete source counterexample was established for those three findings. Full selected ownership precedes presentation recovery, all eligible checked presentations reach comparison before ordering, and a demanded distinct wrapper forwards its original computational child with actual JSON, owner, and retained Wire metadata. This verdict is confined to those paths; it does not certify every reader extension or arbitrary trace graph.

No implementation, mathematical registration, protected assertion, or baseline was edited by this reviewer. All earlier scope conditions remain, including cross-revision question permanence, candidate-invocation ambiguity, direct-projection schemas, the sequential shared-harness assumption, and the limited legacy authority argument. No build, runtime result, computational correctness, B0, V1, or frozen-kernel readiness conclusion follows from this source review.

## Bounded retained-parameter recovery review at `5d176cef`

This source engineering review inspects the integrated kernel at `5d176cef3b1e2dfe51e03b97dd1a8122b73195ba`. Its scope is `FunctorActionData.retainedParameterAction?` and `encodeRetainedParameterAction?`, the `Realize.parameterData` / `declarationData` / `edgeDescriptor` and `realizedParameters` / `realizedEdgeDescriptor` integration, and `Harness.parameterRecovery`. The read also follows the immediate existing helpers needed to assess data dependencies and precedence. It does not cover every intervening reader or execution change. No Lean process was run, no shared build artifact was changed, and no leaf source or mathematical acceptance outcome was consulted.

### Fixed provenance is selected before data callbacks

`retainedParameterAction?` accepts only a closed, well-typed requested parameter. A candidate receiver must be an exact literal expression occurrence inside that parameter and must differ from the whole requested expression. A merely definitionally equal receiver elsewhere in the trace is insufficient. The planner considers retained functor or object-route records, checks their complete recorded result types and values, reconstructs full functor applications where necessary, and checks each ordered accepted action. It then recomputes the complete formal image and kernel-checks its equality to the requested full object. An equality of carriers is not the check.

The planner reads the registry and trace, not `Harness.results`, admitted implementations, connections, or backend availability. It retains the exact receiver, route, and full application array. Only repeated copies of that same triple are deduplicated. Several distinct triples produce `.ambiguousRealization` before `encodeRetainedParameterAction?` invokes either callback. Consequently neither the first successful computation nor the first usable cache entry can select among those plans. Callback failures propagate; they do not cause another candidate or a named fallback to be tried.

The planner's equality checks are presentation checks on the independently fixed formal side. They do not compare returned packets, derive proof evidence from those packets, or authorize replacing one packet with data from a different equal result.

### The five assigned risks

| Risk | Inspected invariant and hostile boundary |
| --- | --- |
| Substitution of unrelated definitionally equal cached data | `realizedParameters` uses the existing exact-expression cache lookup for the requested parameter. On a miss, the new planner does not search that cache. Its source callback encodes the exact retained receiver occurrence, not the recorded action-result expression that happened to compare equal. A foreign cached action result therefore cannot supply the source merely through conversion. |
| Loss of actual source ownership | The realized source callback returns its actual JSON and Wire dependencies through `realizedParameters`. `realizedEdgeDescriptor` does the same for every explicit action parameter. The encoder wraps those actual data in ordered `functorAction` descriptors and accumulates both dependency arrays; the caller retains them. Existing owner combination subsequently checks exact backend/session compatibility. The pure encoder is a formal-input encoder and supplies no claim about a runtime packet or owner. |
| Precedence over a literal selected named object | Before scanning action records, the planner removes metadata and administrative `id` wrappers for this head check. A literal registered object declaration makes recovery inapplicable. The existing named-object path therefore retains precedence over an action recorded elsewhere that happens to have an equal full result. Exact requested cached or traced data also remain earlier than recovery. |
| Ambiguity selected by execution availability | All complete candidate triples are collected and distinguished before either data callback runs. Several triples raise realization ambiguity independently of installed implementations or cached results for those other expressions. There is no reply-dependent retry or availability-ranked alternative in the new path. |
| Recursion through source or action parameters | Both pure callbacks extend the same `recovering` array with the requested parameter. `parameterData`, `declarationData`, and `edgeDescriptor` carry it through their recursive calls. Both realized callbacks receive a scoped Harness copy with that same extension, and `realizedEdgeDescriptor` passes it through parameter realization. Re-entering recovery for an exact parameter already in the chain raises `.noImplementation` before callbacks. |

The recovery chain is scoped rather than a mutable global visited set. Harness copies share the intended result-cache and session references but do not mutate the caller's `parameterRecovery` array. A sibling parameter therefore does not inherit a completed sibling's traversal mark. An exact cached result can still terminate a dependency through the normal earlier cache path. The new mechanism guards recovery cycles; it is not a general termination theorem for arbitrary malformed trace graphs or every legacy recursive encoder.

### Engineering-source controls and verdict

`CasAcceptance/Kernel/ReducedParameterActionProbes.lean` was inspected as assertion source. It defines a reduced full-object presentation whose receiver remains a literal child, puts deliberately different owned packets at the original-source and equal-action-result keys, and asserts use of the original source packet and owner. It also asserts priority for an exact requested cached result, deduplication of identical records, ambiguity for distinct retained source occurrences, rejection of equal-carrier/different-structure substitution, and rejection of a pre-marked recovery cycle before either callback. None of these assertions was executed or counted as a passing result. The nested callback-chain and named-head arguments above come from their actual source paths, not from assumed probe coverage.

No concrete source correctness blocker was established for the five assigned risks at this checkpoint. The bounded composition argument is: fix an anchored full action plan without computational availability, reject unresolved alternatives, encode the exact source and action parameters while preserving their dependencies, and reject repeated recovery targets within that scoped chain. Actual cached data at an unrelated equal expression are not substituted into that process. All earlier qualifications remain, and this conclusion provides no mathematical acceptance, computational-correctness, B0, V1, or frozen-readiness claim.

## Bounded follow-up: selected context and staged data (2026-10-24)

This follow-up reviews the generic source delta from `d729046e9c7599c831ba0b35bf06eb2b4a0feb0f`
to local `331463ce7c1c09e4fb050b2d1169e25778b81406`; published commit
`aeb0b3900a40ffd948b2bda16a36595d977c02ff` has the same tree
`f5758e59dd125abf0ef8140f9a383cdff289c094`. It is an engineering source argument,
not mathematical acceptance, a build result, or an execution verdict. No leaf
source, question files, expected answers, runtime results or other review reports
were consulted. The focused engineering probes were read only as source.

**Concrete source finding at the reviewed revision.** `Realize.presentMorphism`, `frameMorphismData` and
`realizeCallableEndpoint` use `explicit.orElse retained` for `CategoryContext`.
The first two then check only the selected Hom interface; `presentMorphism`
replaces the retained context even on its already-framed return. A Hom type
retains the quiver's Hom field, not the category's complete identity and
composition dictionary. Two complete contexts may therefore share the object
and Hom types while their full bundles differ. The new explicit context can
silently replace the one under which the existing packet was framed. The
`contextualAction` caller provides its trace-selected source but does not compare
it to the original wire's context; reuse is keyed by the formal expression.
The minimum compatibility check is equality of both complete bundles before
selecting the framing context, in a speculative state so missing parameters
cannot be filled by that comparison. Distinct accepted expression labels need
not be rejected when their complete bundles agree: the independently supplied
expression continues to govern the requested route.

The remaining delta has the following bounded compositional justification:

- `incompatibleTypeShapes` restores speculative elaborator state and recognizes
  only rigid Sort, function, inductive and primitive quotient type heads.
  Unresolved projections, eliminators and other heads stay inconclusive; matching
  rigid heads also stay inconclusive. Its rejection cannot select a structure.
- The early refinement filter and `operationOwnerCandidates` apply the same
  `completeRoutes` result and `isFirstOperationBindingRoute` predicate to the same
  category expression. The early test asks only whether any eligible route exists;
  surviving route classes and full-parameter ambiguities still reach the existing
  checks. It introduces no route priority.
- The sole caller supplying `operationId` to `applyFamily` supplies the complete
  application selected by `selectedOperationApplicationsWithSources`. Every
  parameter is first matched to that typed application. The new call to
  `operationParameterObjects` additionally checks the exact accepted ID and arity
  with `selectedEntry`, and retains the application's full parameter values before
  endpoint reading. It does not obtain those values from carrier coincidence.
- At each of the four changed numeral paths the original global point receives
  `elementNumeral` before `staged` records the terminal-map composition. Existing
  realization then consumes the closed point and terminal map separately and
  combines their actual packets and owners. With no stage, the same point remains
  recorded; with a stage, the composition is no longer overwritten by a numeral
  record. No computational result is synthesized by this change.

`completeRoutes`, proof refinement, and lift machinery were not changed or
reaudited. The arguments above do not establish that any probe compiles or passes,
that a realization answers correctly, or that the kernel MVP is accepted.

**Bounded repair in this follow-up.** `Realize.framingContext` now compares the
two complete, resolved bundles under `withoutModifyingState` before selecting
the supplied context. Presentation and framing run that check before the
already-framed return. Presentation also checks any retained endpoint contexts;
callable-endpoint reuse checks the returned endpoint's retained context before
consuming its packet. Context mismatch propagates as declared invalidity, not as
missing computation. Existing packet composition and owner merging are unchanged.
This checks compatibility of independently selected contexts; it neither admits
an expression label nor infers a category from the Hom type. Different accepted
expression labels may denote definitionally identical full bundles, so the guard
does not impose an additional syntactic-label equality requirement.

The added source probe uses Mathlib's existing `SingleObj` category instances for
`Nat` and `Multiplicative Nat`, whose reduced object and Hom types agree but whose
complete dictionaries differ. This is a local reflection fixture, not a registry
addition. It covers conflicting retained contexts before and after framing,
direct and cached endpoint conflicts, compatible packet/owner preservation, and
refusal to fill an unresolved selected bundle. Only `git diff --check` was run
for this follow-up; no Lean compilation or execution result is claimed.

## Bounded follow-up: retained action-source interfaces (2026-10-24)

This source review covers `5b173d3ec87c22d56d209f3d22a8bd2441f87969` relative to
`331463ce7c1c09e4fb050b2d1169e25778b81406`. The carrier change delegates to
`interfaceSelectedValue` and supplies the existing `InterfaceObjects` table at
all three callable consumers. For descriptors carrying a complete named source
or selected action, this validates the entire action image and retains its full
target bundle; it no longer asks recognition to find a target object name from
a carrier. The consumers still compare their independently selected complete
endpoints. Ordinary descriptor failures remain interface errors; there is no
blanket conversion of interpreter exceptions into successful validation.

A remaining source defect affects a retained opaque structured source. The
structural-action branch first recovers that exact source through
`interfaceObject objects originalData`, but then recursively calls
`interfaceSelectedValue` on its opaque packet. That second call has no selected
source category and rejects every structured value whose descriptor carries no
selection, even though the accepted full action fixes its source bundle and the
interface table fixes the complete original object. This is a missing supported
retained-input path, not evidence about an executed result.

The separate repair uses the accepted action's complete source bundle and the
exact retained packet binding for descriptors without selection syntax. Every
binding of that packet must agree as a complete value; input order cannot select
one. Named, action and presentation descriptors continue recursive validation,
including full source-bundle agreement. The source, action parameters and target
bundle must already be complete. The public carrier helper can also receive an
unresolved selected object through the input table, so the action branch now
refuses an unresolved independently expected result before comparing the full
action image. It cannot fill that result from the returned descriptor. Declared
invalid or ambiguous source interfaces become interface errors; interpreter
failures continue to propagate.

The focused source probe covers retained opaque sources through the carrier and
nested element consumers, complete source context and route retention, missing
bindings, conflicting bindings in both orders, different full sources and
results on the same carrier, unresolved sources and expected results, explicit
named-source contradictions, and retained, missing or incorrect action
parameters. These controls were authored but not executed in this source task.
`git diff --check` is the only completed mechanical check; compilation and the
coordinated consumer verification remain pending. The unchanged registered-edge
argument reconstruction still uses definitional equality after unfolding; this
bounded review does not establish retention of declaration parameters erased by
that unfolding. No execution failure or mathematical acceptance is inferred.
