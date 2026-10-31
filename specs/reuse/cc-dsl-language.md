# Reuse record: `cc-dsl-language`

## Reconstructed partial named-object views — 2026-10-31

Local source inspection reuses `Trace.checkProducerRecord`, `recognize`,
`recognizeObjectApplication`, `Value.sameSelection` and `retainObjectContext`.
A view of the exact authenticated handle with neither origin nor selected value
may lack binding data, but still asserts its category declaration. `recognize`
checks that declaration before completing only the missing binding. Supplied
complete selections must still agree through the unchanged selection predicate;
all original context is retained. A conflicting declaration or complete origin
is not converted into a partial view.

Structured projections, binders and selected numeral carriers retain their own
`Trace.recordProduced` handles. Candidate binder readings copy the existing
trace and caches; closed-type instance visibility still checks the original full
type. These are new reconstructions, not recovered historical byte identities.
Codec and Language compile in the current recovery logs. Fresh
`reconstructed-controls-v2` passes ReaderContextContinuityProbes, including the
partial-view and conflicting-declaration controls, and DeclaredParameterEndpointProbes.
The complete unchanged consumer family and original mathematical questions still
require fresh runs.

## Selected V1 Lean reuse and import placement (2026-10-28)

**Decision:** keep the existing catalogue-controlled DSL and delegate ordinary dependent
term application to Lean's public elaboration APIs. Do not replace mathematical selection
with Lean overload/typeclass search, build another parser or copy Lean's application engine.
This is the implementation direction for #66; the fixed controls validate it rather than
initiate another reader-architecture comparison. It adds no Lake dependency or toolchain move.

| Responsibility | Selected source | Placement and required boundary |
| --- | --- | --- |
| Syntax and catalogue selection | Existing `Language` syntax, `Parser.runParserCategory`, `Scope`, `Semantic` and `CategoryContext` | Keep the admitted surface and catalogue-owned declaration/route choices in `CasCatalogue/Language.lean`. An already selected declaration is passed to Lean as an `Expr`; do not ask name/overload resolution to choose it again. |
| Dependent application | [`Lean.Elab.App`, `Term.elabAppArgs`](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Elab/App.lean#L1338-L1353), with the existing `forallMetaTelescopeReducing` parameter acquisition | Import/use `Lean.Elab.App` in the reader's generic application adapter. Supply the selected declaration and complete chosen arguments/dictionaries. Its `expectedType?` propagates information but does **not** check the result type; retain final complete type, context, parameter and closed-term checks. No permissive fallback to another mathematical candidate. |
| Ordinary local terms and binders | [`Lean.Elab.Binders`, `Term.elabBinders`](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Elab/Binders.lean#L242-L263), `elabTermEnsuringType`, and existing `withLocalDeclD`/`mkLambdaFVars` | Use these inside the reader adapter for actual local term formation. Keep `binderReading` and the catalogue's generalized-stage projections where they define the mathematical binder; an ordinary lambda is not a replacement for that semantics. Preserve the actual use context of definitions. |
| Scoped local declarations | [`Lean.LocalContext`](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/LocalContext.lean), `Lean.Meta.withLetDecl` and `mkLetFVars` | Use Lean's scoped context/closure operations during preparation. A transient `FVarId` is not a persistent computation identity, and a DSL definition is not executed when declared. Persistent outputs belong to #69's selected execution owner. |
| Complete question comparison and explicit export | Existing `QuestionIdentity.equivalent`, `encodeInContext`, `TermTable` and its closed/contextual `Std.HashMap` caches | Retain the complete typed comparison and existing contextual interning. Separate ordinary execution from unused serialization; do not replace identity by assertion text, `Expr.hash` or unrestricted definitional equality. The October 19 cache repair is the existing optimization source, not a reason to write a new exporter. |
| Preparation validation | Existing closed-term, selected-parameter and producer-reference checks | Enforce them before dispatch even when export is not requested. Reuse their implementation where retained and carry the invariants to the selected owner where the old trace helper disappears. |

Use the unchanged dependent-reader specimen and selected-structure/admission controls while
replacing duplicate application plumbing. That specimen remains separate from RX-LIFT;
their shared implementation is not permission to compose or rewrite their fixed questions.
Compile the actual adapter and affected consumers, then measure the original matrix and
RX-LIFT requirements. No successful build, speedup or mathematical acceptance is asserted
by this source decision. The implementation and its validation remain work to complete.

The dated records below retain source history. This selected route owns the current
implementation order; a historical source-level claim is not a new runtime verdict.

## Complete inclusion paths and selected power structures (2026-10-25)

Corpus searches `monomorphism composition` and `CategoryTheory CategoryStruct comp`, followed by
source inspection, locate the mathematical owners in Mathlib's categorical identity/composition
and `lean-categories/Catalogue/Registry/Semantic.lean` (`validateInclusion`). The existing
`InclusionEntry` carries its actual arrow, endpoint families, shared or dependent parameterization,
and the upstream proof that that arrow is monic. The concrete controls use the published
`NumberSystems.finIntegersMod`, `RealLimits.puncturedUnits`, finite points/reversal, identity maps,
and their existing proof data. No mathematical definition, theorem, global registration, permanent
assertion or leaf changes.

The former `inclusionChain` kept the first shortest family-level route. Membership and named subset
judgments used that graph result without instantiating the arrow; a route `Fin(n) → ZMod(n)` could
therefore decide membership at different actual values of `n`. Conditional inclusions could likewise
lose their premise. Coercion, complement and dependent-parameter inference used the same first route.

The reader now supplies a complete independently selected source, enumerates candidate paths without
an ObjectId visited rule, and constrains every adjacent and final endpoint before closing the whole
path's parameters and proof obligations. Matching declaration heads compare every ordered computational argument
before conversion can erase one. Proof arguments retain their complete proposition while their
incidental proof implementation is irrelevant. Transparent endpoint presentations use that same
binding rule before whole-map equality. Target metavariables may be determined from that fixed source;
failed trials cannot assign the caller's metavariables or write trace entries. The selected path is
replayed once to commit its actual parameters and complete inclusion/composition trace.

Repeated families may denote different concrete parameters and remain in the search. An incompatible
signature ends only that branch. A failed independent parameter or proof cannot be repaired after
both its source and intermediate endpoint are closed; a genuinely unresolved endpoint remains
expandable. A repeated prefix closes only after its complete endpoint application and whole composite
map agree. The current installed inclusion graph is finite and acyclic; cyclic extensions are not
silently truncated. An unclosed search reaches the existing host resource failure, while two distinct
applicable maps establish ambiguity immediately. Lean's kernel checks complete map types and equality
in the existing local context; a point sample or equal carrier is never agreement. Kernel exceptions
propagate instead of being interpreted as invalidity or mathematical ambiguity. A deterministic
representative is chosen only inside a class whose whole maps agree. Deterministic breadth-first
frontier ordering also keeps shared intermediate prefixes independent of registry storage order. Explicit reflexivity remains at
the membership, named-subset and coercion caller boundaries; the path selector grants identity no
priority over a different applicable same-family map.

`validatePowerObject` permits independent structures sharing an object family, truth-value family or
extent declaration. The remaining first-row reads in `powerOf?`, `asAnswer` and `Realize.extentOf?`
now use explicit unique selection, matching `powerObjectIn`. `validateSubsetLiteral` already enforces
one form per power-object ID, so that separately justified lookup is unchanged.

`InclusionSelectionProbes` checks same/different concrete parameters, membership, subset, coercion,
complement, target inference, exact trace arguments and isolated failed trials. Its immutable local
rows only specialize existing upstream maps/proofs. They cover both declaration orders, signature
and closed-premise cycles, same-family paths through different parameters, delayed earlier-parameter
binding from the final endpoint, distinct whole maps, identical-map and transparent-endpoint aliases,
proof irrelevance, committed identity inference, unrelated unfinished locals, and all three formerly
first-match power selectors. Original controls and fixed questions
remain unchanged.

## Complete member applicability before result construction (2026-10-25)

The corpus query `dependent telescope application elaboration` returned other elaborator
implementations, not a mathematical construction needed here. Direct source searches locate the
existing owners in Lean's `forallMetaTelescopeReducing`, `instantiateMVars`, and `inferType`, and
the reader's `bindSelectedReceiver`, `parameterTrial`, and `invariantOf`.

The unchanged structured-execution probe exposed a deterministic timeout while checking both
declaration orders and ambiguity. Stage measurements attribute about 48,600 of a member reading's
52,500 heartbeats to constructing its source and target endpoint values. The old applicability
trial repeated that result construction for every candidate before constructing the selected
result again.

`invariantApplication` factors the existing complete dependent binding and type checks from
`invariantOf`. Competing declarations are checked by those same full applications; the selected
family still constructs its actual endpoints, parameters, and trace through `invariantOf`.
Both declaration orders and distinct applicable declarations retain their existing meaning.
No mathematical row, assertion, conversion, cache, or heartbeat limit changes.

## Reconstructed declared endpoint context (2026-10-24)

The conversation's lost-source record identifies the earlier `14b676e` change:
every result of `declaredEndpointObject` retains its complete supplied inputs.
Inspection of `Value.viewData`, `sourceParameterValues`, `recognizedEndpoint?`
and `declaredFieldEndpoint?` locates the existing owner of this interpreter
context; no mathematical construction is required. `retainObjectContext`
extends only the original-input list. It preserves the existing source, route,
parameter comparisons, full action arguments, selected object and declaration.
An anonymous endpoint remains anonymous. This reconstructs the recorded change
against the surviving source; the unavailable original commit is not claimed
to have been recovered.

## Complete family parameters in structural applications (2026-10-20)

Corpus queries `CategoryFamilyFibreWitness` and `structure eta reduction`, followed
by direct dependency source inspection, locate the owners in
`LeanCategories/Catalogue/Realization.lean` and Lean's `Meta/Structure.lean`.
`FunctorRealization.sourceRealization` and `.targetRealization` retain the actual
category-family fibre witnesses. `CategoryFamilyFibreWitness.parameter` supplies
the complete selected parameter, including its dictionaries. Lean's existing
`etaStruct?` reduces a reconstructed record of projections to that same record.

The kernel adds no category, parameter constructor, equality or transport. It
unifies these published complete parameters before comparing adjacent carriers,
and uses the declared source category's witness when applying an action to its
actual typed receiver. Definitional equality checks retain the complete supplied
data; an equal carrier alone does not identify different selected parameters.

## b0-selected-structure: full same-carrier observations (2026-10-11)

Searches for `recognize`, `carrierObject`, `Maps`, `BilinModuleCat.ofBilinMap`, and
`LinearMap.mul` in the existing selected-structure/carrier probes and the upstream
bilinear-map module locate all required input constructors. The checks extend
`SelectedCarrierProbes`; no new mathematical row or construction is introduced.
The public `Maps` and `Vec` declarations supply the function-carrier pair. The upstream
`BilinModuleCat.ofBilinMap` applied to the existing zero and multiplication maps supplies
the form pair on the same module. The reader's existing `recognize`, `carrierObject`,
and `coercionMap` are checked in both candidate orders: full selected inputs retain
their identities, whereas the common carrier alone is ambiguous and does not confer
an identity coercion between the chosen forms.

The no-witness function-carrier case exposed an additional defect: `recognize` searched
transparent aliases when the expression named no object declaration. It selected `Vec`
while the same-carrier `Maps` declaration was opaque. Recognition now uses retained
complete values or the actual registered declaration head and its typed parameters only.
It no longer recovers an object identity from reducibility. A caller holding an anonymous
structured value must retain that value; it cannot manufacture named provenance from
its carrier.

A declaration may still pass its supplied value to an anonymous equal carrier required
by another signature. This is forward forgetting, not named-object recovery. The identity
carrier check permits only a target with no origin, selection or retained view data; the
reverse direction remains refused. `coerceTo` retains the supplied point's provenance in
that case. The new probe checks both directions and preservation of the named vector input.

Binder domains use the actual registered domain function and the supplied arguments'
retained objects and constructor parameters. The function's returned declaration is kept
before reducing its carrier; a domain supplied as an argument is recognized from that
argument, not from an unrelated alias. Fixed parameter contexts are retained before
reading numerals, so distinct numeral traces cannot create different choices of domain.
This preserves integral/limit domains and the chosen coefficient objects in root binders
without reintroducing reverse recognition from bare carriers.

When an anonymous parameter already records its complete source and exact full declared
carrier route, `carrierObject` replays that action and retains the source's carrier origin
and chosen structure. Both the replayed image and the actual source carrier must be the
supplied handle. This is forward use of retained provenance, not alias lookup. A raw
carrier without that record stays anonymous. Identity views of Maps and Vec recover only
their explicitly recorded source, even though both have the same function carrier.

Dependent result parameters retain the actual ambient endpoints of their operands' public
inclusions. `inclusionOut?` and `inclusionTargetValue` own this construction. If an endpoint
has no named presentation, it is kept as that same anonymous object; no alias is inferred
and ambiguity or interpreter errors are not suppressed. The factor-result probe checks that
the element-set parameter comes from the nonzero-polynomial domain's declared ambient,
without using a computed answer to choose the formal result or its operations.

## Queries
2026-10-20: `structured parameter provenance` and `selected object parameter transport`.
The returned physics and charge-sector declarations supply no owner for this
interpreter bookkeeping. The existing `typedParameter`, `structuredParameterView`
and `coalesceSelectedParameterViews` computations are reused rather than recreated.

`formalization_corpus.py search`:
- "custom syntax category DSL elaborator declare_syntax_cat": no owner;
- "parse external file runParserCategory": a file-extraction tactic (tcslib), no owner;
- "surface notation registry name lookup": no owner.

The language authors no mathematics. Every name it accepts is a catalogue row's surface name
(`lc-api-names`), and every literal is a catalogue literal (`lc-api-literals`).

## Owner
- Lean's `declare_syntax_cat`, `Parser.runParserCategory` and term elaboration.
- The catalogue rows (`lean-categories`), and the kernel's resolution of methods, objects and
  limits (`method%`, `obj%`, `limit%`).

## New code, and why no dependency supplies it
The syntax category of SPEC.md's statements and its elaboration through the catalogue.

Binder domains are fixed before their bodies are read. Once the body supplies its
selected values, the existing full-parameter witness computation records missing
structured sources of those same declared constructors. It does not replace the
domain or recover a named object from a carrier. Every checked source presentation
and its exact registered action is retained. Type-valued parameters keep their
existing declaration identity. This adds no mathematics or subject-specific rule.

## Compositional application and selected identity

The reader's `applyFamily` starts from the registered declaration's dependent telescope. Supplied
structure parameters are read at their declared types, numeral and map parameters are checked at
their own positions, and the operands must reach the declared source through their actual typed
objects and admitted inclusions. The result is the complete declaration application, including
implicit arguments, instances, maps, and established closed hypotheses. Unresolved parameters or a
type-incorrect complete application are rejected. A requested result object constrains that same
application; it does not license a replacement operation or a guessed structure on its carrier.

Source inference first matches a registered source declaration's ordered arguments against
the actual source application. Retained nested arguments can supply their complete selected
objects directly or through their registered refinements. A speculative joint assignment is
committed only when every explicit parameter, the complete declaration application, and all
actual source endpoints are closed and type correct. Distinct compatible complete parameter
witnesses remain ambiguous. This prevents a requested result object from replacing an operand's
coefficient structure merely because their carriers permit a conversion.

Each successful local application therefore composes the retained operand maps with one accepted
typed arrow. The binder rule composes these same applications with its declared domain and
admission; it has no independent arithmetic or analysis interpretation. The argument is local and
compositional: a larger expression is formed only when each operand, parameter, source map, and
selected arrow supplies the premise required by its enclosing application.

Selected object identity is retained separately from a carrier. A value keeps its exact object,
category, named declaration and ordered parameters when present, and the chosen structured value
when viewed through a carrier. A declaration match identifies its own registered object before
carrier unfolding is considered. Distinct declaration identities are not made interchangeable by
a definitional equality of their carriers. Anonymous structures supplied by an accepted
declaration remain exact typed bundled values; absence of a separate named row does not justify
replacing them with a named refinement.

Structural parameter transport uses actual registered functor routes. The selected source remains
in the trace with the route and target category; route comparison consumes the admitted cells and
propagates ambiguity. Registered presentation syntax similarly retains the chosen isomorphism's
complete parameters, orientation, actual source and target, and applied argument. Its carrier map
is the action of the admitted route on that actual isomorphism arrow. A shared carrier or an
identity-shaped backend value cannot substitute for these selected data.

When the demanded category lies on a named refinement's declared carrier route to the exact
set, acquisition uses those route prefixes. Otherwise it checks the registered incoming routes
against complete structured images, retaining ambiguity between distinct images. A selected
named structure also uses declared prefixes when available. This retains the declared
operation: an additive-to-multiplicative relabelling elsewhere in the category graph does not
replace the multiplication selected by a ring's carrier refinement. Route choices are first
resolved within each source through admitted comparisons. Different incoming source declarations
are merged only when their complete objects at the expected structured type are definitionally
identical, with a kernel-checked equality proof for every image. The trace retains every source,
full parameter list, chosen route, complete carrier route, registered refinement identifications,
and typed image. The deterministic representative affects serialization alone; distinct full
structures remain ambiguous even when their carriers coincide.

The approved quotient-arithmetic notation `ℤ/n` denotes the public ring object
`obj.rings.integers_mod`, whose declaration is `NamedRings.ringIntegersMod n`.
Its refinement to `obj.sets.integers_mod` specifies the multiplicative `ringsToSets`
route and `ringIntegersModIdentification`. The reader instantiates that full ring at
the declared parameter, then exposes its carrier while retaining the ring, route and
identification. An explicit requested category converts this chosen object through
the existing checked structural interface. The same carrier's separately selected
additive group or monoid does not replace the quotient ring's multiplication; different
complete structures still remain ambiguous. This follows the notation's mathematical
source definition and does not select a structure by carrier equality or by the operation
later applied to it.

A dependent structure parameter may also be supplied by a registered declaration whose actual
structural forgetful image is the operand's selected structure. This comparison is at the bundled
structure, never just at its set carrier; distinct compatible declarations remain ambiguous. A
remaining morphism parameter is inferred only after its complete endpoint type is fixed, from a
unique registered declaration with all arguments determined. Its actual application remains in the
trace, so a coefficient map is not replaced by an unrelated inclusion of underlying sets.

A distinguished generator binds a variable locally inside an explicitly written selected object.
The binding comes from that object's generator declaration, respects existing external bindings,
and removes only those local occurrences from free-variable collection. Distinct presentations
may consequently use the same written variable name while retaining distinct generator values.

The explicit object-action surface is `view X along F` or `view X along F(a₁,…,aₙ)`.
Here `F` is the complete public registered functor identifier, including its dotted components;
the parenthesized arguments supply its declaration's explicit binders in declaration order.
The selected object `X` must belong to the declared source category. The reader uses its actual
complete object type to infer remaining parameters, synthesizes the declared instances and
establishes closed obligations, and rejects any unresolved parameter. It applies that exact
registered declaration and retains its complete chosen arguments, source object, target category,
and actual image. No default functor or inverse to a forgetful map is inferred.

`id(view X along F)` is the categorical identity of the actual selected image. A registered
kernel or other limit applied to that identity uses its actual category, diagram, and chosen
limit declaration. Observing an inclusion or pairing requires the corresponding public
registered observation; the view surface does not invent one. The object value retains the
original supplied value, actual source, ordered edges and complete action arguments, and every
checked full source presentation even when semantic reading runs without a trace. A structural
view may recover a named carrier only through its declared refinement and checked route suffix;
a general functor image obtains its own carrier through its actual target structure.

`K.leg(n)` selects the defining cone leg of the actual registered construction `K`.
The ordinal `n` is interpreted at the complete diagram-index type: finite enumerations use
their actual declaration constructor order, with every constructor nullary after its full
parameters are instantiated; `Fin` uses its actual bound. Unresolved parameters, recursive
constructors, and out-of-range indices are rejected. The resulting arrow retains the actual
apex, diagram, typed index, and creation lift. Reading without a trace validates the same
registered construction presentation. For a parallel-pair kernel, index `0` selects its
source leg; this follows the actual shape declaration rather than a kernel-specific rule.

These invariants describe the reader's composition of accepted premises. They do not establish
mathematical input completeness, backend implementation, result reconstruction, or final B0
acceptance; those are independently required by the owning computational-core plan.

Registered name calls are resolved by complete argument signatures across object, morphism,
method, and construction rows. A candidate is discarded only when its declared signature is
inapplicable; unresolved semantic ambiguity survives. Construction applicability is checked
at the actual receiver category before building its diagram. Multiple applicable complete
signatures remain ambiguous, including signatures returning different categories.

Registered admission evidence receives a definitionally equal presentation of its original
complete target. Closed chosen class dictionaries may use another same-class presentation
only after kernel conversion checks equality of the entire supplied dictionary. Predicate
heads and chosen data remain fixed. The same registered evidence procedure first receives
the original target, then distinct checked equivalent presentations after ordinary rejection
only. Every attempt shares the existing heartbeat allowance. A malformed or incomplete result
cannot trigger another view. Its closed result is checked at the original target, including
Type-valued admission witnesses. Different structures on one carrier cannot pass the full
dictionary equality check.

The reconstructed constrained-point reader inspects the constructor of the independently
fixed target record through Lean's structure metadata. It accepts exactly one fixed data
field and proposition-valued remaining fields; it does not select a predicate or infer a
target from data. `proof(...)` supplies a closed term at the actual declared proposition.
For generalized points each obligation is quantified over the original domain, and the
actual constructor is applied pointwise. `ConstrainedPoint` reuses `Codec.conditionProof`
and `Decide.kernelAccepts`; it adds no mathematical admission rule. The runtime retains the
original data map and all of its owners in the public `constrainedPoint` descriptor, while
proof terms remain on the formal side. Unresolved obligations remain interpreter failures,
distinct from a proof of invalidity. This is a reconstruction from the conversation's
implementation record, not recovery of the lost source bytes.

Structural traces retain the exact ordered complete edge applications constructed with the
source and endpoint constraints. Parameter equivalence records every source presentation,
its complete applications, and its full image identity; replay does not infer new parameters
from a route identifier.

Carrier presentation exposure preserves ordinary semireducible type heads: actual closed
structure and class data may be exposed fully, while their carrier aliases use reducible
projection exposure. This retains the declared carrier presentation needed by registered
evidence rather than unfolding a type alias into an implementation datatype. The complete
original target and returned witness are still checked by kernel conversion.

A supplied closed map of sets may expose its stored function through the ordinary categorical
map constructor. Before reducing its value, the reader protects registered comparison and
operation declarations. It checks the complete map type and the complete map value by kernel
conversion, then checks the entire presented evidence target against the original target.
This presentation step supports the same registered procedure's recognition of constant
point actions; it supplies no new theorem or chosen instance. These checks concern formal
admission and convergence statements and consume no backend answer data.

## Shared context-free binder arguments (2026-10-11)

The corpus queries `Lean elaboration shared argument syntax candidate overload` and
`forallMetaTelescopeReducing withoutModifyingState` found metaprogramming guidance and
other syntax elaborators, not an owner of this DSL's binder selection. Reuse the existing
`binderReading`, `eval`, `typedParameter`, and `parameterTrial`; Lean owns the dependent
telescope and isolated metavariable trials.

When there is one supplied argument and every candidate signature requests its unscoped
reading, evaluate that common argument once before candidate selection. Each candidate
still checks its own complete parameter type, body, and target. Evidence runs only after
the unique candidate is selected. Contextual and dependent multi-argument readings are
unchanged. The shared value retains its original chosen structure and trace; no row is
selected by a timeout, registration order, or a notation-specific rule. The ordinary
heartbeat budget remains unchanged. The existing admitted root-sum/root-product texts
are used in reader-mechanics probes without accepting numerical answers or changing the
permanent assertion corpus.

## Retained forward carrier views (2026-10-11)

The existing `coercionMap`, `retainedCarrierRoute`, `structuredParameterView`, and
`retainedActions` supply the needed ownership and actual-action checks. A complete
ring and its retained multiplicative-monoid view formerly failed the identity-carrier
test solely because their selected categories differed. The kernel now admits this
forward view only when the recorded full source agrees, the recorded route is a prefix
of that source's declared carrier route, and replay of every retained application gives
the exact selected target. The existing carrier and named-origin checks still apply.
No inverse recovery, general carrier matching, arbitrary functor, or new mathematical
comparison is introduced. ParameterStructureProbes checks the valid forward view,
refuses the reverse recovery, and refuses the same carrier after its action witness is
removed; its existing distinct-structure checks remain unchanged.

## b0-typed-application: constants at witnessed coefficient views (2026-10-11)

Corpus queries `Polynomial.C forgetful functor natural transformation coefficients` and
`Polynomial.C`, together with the local `constants` declarations and coercion probes, locate
the existing mathematical owner: `CasCatalogue.Algebra.Polynomials.coefficients`, registered
as `ObjectEntry.constants`, uses Mathlib's `Polynomial.C`. The kernel needs no new constant
map or comparison theorem. Its own `coercionMap` already checks exact selected identity
views with retained carrier-route applications; `identityCarrierView` factors out that check.

When the target independently fixes its constants declaration and complete parameter, a
coefficient in that parameter's witnessed forward carrier view can be passed to this same
declared arrow. The arrow is elaborated with the target's original parameter and checked
at the fixed endpoints. No reverse structural coercion is enabled, no nonidentity map is
inverted, and an unretained or different parameter cannot be supplied by matching carriers.
The engineering probes verify the actual declared arrow and reject structural recovery,
a missing action witness, and a different coefficient parameter.

## b0-domain-preservation: supplied carrier projections (2026-10-11)

The local searches for `evidencePresentation`, `plumbingRoots`, `carrierAlias`, and
`deltaExpand`, and the corpus query `deltaExpand`, identify Lean's existing restricted
definition expansion. Reuse it with the unchanged `plumbingRoots` policy. No new mathematical
normalizer, evidence procedure, lemma, instance or type-specific case is needed.

A supplied carrier may remain a projection of an actual registered categorical action after
reducible weak-head normalization. The published constant-polynomial evidence cannot recognize
that projection as its polynomial carrier, although the complete obligation is definitionally
equal to the one it handles. After dictionary presentation, expand only the existing plumbing
owners in closed type expressions that still weak-head reduce to a projection, then use the
existing reducible normalization. Predicate heads and mathematical value
expressions are not rewritten by this carrier step. The existing full-target conversion check
and the returned term's original expected type remain mandatory.

EvidencePresentationProbes constructs the selected carrier through the registered algebra
and monoid views, runs only the units row's published evidence, checks its term at the original
obligation, and confirms that the zero constant polynomial remains invalid. The accepted
domain and formal admission map are never replaced by a different object.

The initial all-carrier expansion was rejected by the new positive probe: it exposed
function-wrapper dictionaries before their presentation phase, hiding the value's existing
arithmetic heads. The restricted final-projection pass preserves those heads and passes the
isolated positive and negative checks; no unsuccessful build or probe is counted as a hold.

## b0-typed-application: dependent registered structure arguments (2026-10-11)

Corpus queries `forallMetaTelescopeReducing` (the inherited scalar-parameter investigation)
and `forallMetaTelescopeReducing identityAt` (no matches), together with local searches for
`registeredStructuredParameter`, `registeredArrowParameter`, `identityAt`, and the published
`scalarAlgebra`, locate the existing owners. Lean owns dependent telescopes, isolated trials
and definitional equality; Mathlib owns categorical identity. The scalar constructor and
coefficient maps are already registered by lean-categories. This extends the two existing
generic inference functions; it adds no mathematical construction or semantic row.

The constructor's requested type and its image at an actual structured operand jointly
determine its ordered arguments before the complete application is required to be closed.
Anonymous carriers supply no missing structure. Remaining arrow parameters can use only a
unique registered arrow or the identity of their already fixed complete endpoints. Identities
compete with named maps rather than suppressing them. All successful constructor applications
are retained until ambiguity is resolved; different full structures remain ambiguous. The closed
candidate is checked again by the ordinary registered route classifier, so the inference trial
does not decide between un-compared routes. Original operand and result type checks remain in
`applyFamily`. The new engineering probes test complete self and nonidentity scalar maps,
refuse anonymous-carrier acquisition and a missing coefficient map, and preserve the ambiguity
between a named endomap and the categorical identity.

Only source witnesses whose actual outgoing action reaches the operand participate;
coefficient objects elsewhere in its provenance do not choose an alternative scalar target.
Repeated full structured images are coalesced within the same target category. After unique
selection, `Semantic.recordNamedObject` preserves the exact constructor and ordered parameters
without reinterpreting them against unrelated provenance views. Inferred arrows are recorded
at their unchanged complete types. `applyFamily` keeps the isolated inference result and its
private trace, committing that trace only after the actual operand and full application checks
succeed. It does not rerun the same search merely to recover its trace, and it does not raise
the reader's heartbeat budget.

The nonidentity scalar control exposes both the generic scalar constructor and an existing
named scalar-algebra presentation. When their complete structured values are definitionally
equal, the existing `ParameterPresentation` / `Node.parameterEquivalence` records retain every
declaration id, full ordered parameter and checked complete-object equality witness. Sorting
occurs only after the full equality checks and chooses a serialization representative, not a
preferred mathematical structure. Carrier equality alone never admits this identification.

## b0-typed-application: retain explicit subset result contexts (2026-10-11)

Corpus search `registered callable dependent parameter provenance` found generic unification
material, not an owner of this reader. Local searches of `applicationOf?`, `comprehension`,
`powerSetOf?`, `evalIn`, and `applyFamily` identify the existing mechanism: explicit result
contexts flow to `applyFamily`, which checks the complete declared result type before retaining
the selected target. The mathematical primitive map remains the published declaration; its
polynomial evaluator remains the published `ObjectEntry.application`.

The subset-comprehension domain and unary primitive application previously dropped an explicit
`in 𝒫(X)` context. Their actual result then retained only its raw base carrier, without a chosen
callable object. Forward the supplied context through these existing calls. Do not recover a
name from the carrier, change the registered map, or provide missing admission evidence.
An incompatible result type must still be invalid. Without an explicit context, an anonymous
result must stay anonymous. The unchanged normalized-primitive binding supplies its own
`𝒫(ℚ[x])` target; that target, not a guessed polynomial alias, supplies the evaluator for `h(0)`.

## Action-bound source realization (2026-10-20)

Corpus searches `FunctorRealization sourceRealization` and
`CategoryRealization familyFibre` returned no indexed matches; direct existing
`LeanCategories/Catalogue/Realization.lean` supplies the complete typed source
realization, and existing `Semantic.realizedFunctorEndpoints` projects it while
checking the exact supplied action. The module-kernel diagnostic confirms a
fresh source schema cannot recover a RingCat bundle from its carrier, whereas
the existing action-bound realization retains that bundle. The kernel now checks
the declared source metadata and exact receiver type against this supplied
realization. Where the named source explicitly supplies a published family-fibre
witness, existing structured-receiver elaboration and full family-parameter
alignment still infer omitted parameters before that final action-bound check.
A plain category schema supplies no such witness. No mathematical constructor,
source equality, or carrier-based parameter recovery is added.

## V1 registry-driven dependent interpretation (2026-10-23)

The existing Lean dependent telescope, category-family fibre witnesses,
registered object notation/component fields, and registered terminal point
own the required constructions. The interpreter consumes those interfaces for
selected `Vec` parameters, destructured map arguments, quotient notation, and
closed points. It introduces no object-specific mathematical constructor.

The observed normalized-integration obstruction came from repeating complete
structured-parameter searches inside the same candidate. Rigid declaration
filters retain expression metavariables (universe metavariables do not disable
the filter); candidate-invariant work is shared. Successful transactional
recognition retains its checked state once, while invalid speculative readings
restore state and ambiguity/internal failures propagate. No elaboration budget
is increased and no mathematical evidence is weakened.

### Reconstruction of complete declared inputs (2026-10-24)

The missing conversation-state work is reconstructed from its source record;
the original commit bytes are unavailable. The corpus queries
`forallMetaTelescopeReducing` and `finite function vector tuple` were attempted
in the cloud container. Both stopped at the corpus API's network access boundary
(`Operation not permitted`). The existing searches and owners above remain the
reuse basis. Local source inspection additionally located
`CasCatalogue.Modules.Operations.zero` and `scalarAction`, the registered ring
and semiring numeral declarations, and
`CasCatalogue.Algebra.LinearAlgebra.{empty,cons,vectorComponent,rows}`.
Mathlib's `ModuleCat`, `PUnit.module`, and finite-function types supply the probe
objects. No mathematical definition, registry row, or leaf is added.

The reader now compares the original declaration and all ordered arguments
before comparing an unfolded operation result. In particular, two constant
functions cannot erase different scalar or module parameters during selected
operation dispatch. Every complete retained source witness participates, and
the actual complete declaration source checks the operands before selection.
This check precedes ambiguity: a polynomial's coefficient ring is retained
context, but an operation on that ring is inapplicable when the actual operands
are polynomials. The surviving application retains its already checked value
and private trace; the reader does not repeat the same elaboration for recording.
Explicit `•` and juxtaposition consume both registered operations and registered
morphisms with the action surface; multiple applicable readings remain
ambiguous. Empty registered calls, raw identifier method fields, and applications
of already formed expressions pass through the same declared-call machinery.

A point whose actual codomain is the independently fixed declaration endpoint
may retain that endpoint without replacing its original generalized map. Its
source context survives. This rule applies at declared inputs and codomains;
the ordinary full-identity coercion rules are unchanged. When the callable fixes
its input, that input comes from its actual application signature, including a
unary tuple or matrix argument. A further dependent structure determined by an
independently supplied operand keeps the existing operand reading.

An anonymous coordinate may form a numeral from an independently supplied
complete registered owner. The owner and its full type close before its carrier
is compared with the coordinate. Candidate numerals compare the full owners
and the ordered declaration applications; every alias of the same owner is
retained. A bare coordinate carrier provides no missing ring structure, and the
coordinate remains anonymous.

Tuple and matrix literals use the actual nondependent `Fin n → A` declaration
type and its fixed lengths. Applicable registered component maps supply a named
coordinate context; otherwise the coordinate object remains anonymous and
retains the declaration's source witnesses. Nested finite-function dimensions
support rectangular declared matrices through the existing tuple constructors
and declared-result check. A category family's independent object universe is
closed only after the actual object's full type has constrained it.

Context traversal expands each exact syntactic witness once. Only duplicates
with the same registered origins, complete selected objects, ordered parameters,
routes, and comparison data are coalesced. This avoids repeatedly expanding the
same retained context while preserving distinct aliases and structures.
Endpoint recognition also merges the contexts of an exact same selected value:
its handle, category, constructor identity, ordered parameters, and selected
structure must match syntactically. Both complete context payloads survive that
merge. Additional provenance is not a second selection, while a different
selected structure still participates in the ordinary ambiguity checks.
`CasAcceptance/Kernel/DependentElaborationProbes.lean` exercises these reader
mechanisms without changing permanent mathematical assertions or executing a
leaf. Compilation is a reader-engineering check, not acceptance evidence.

Cloud-container verification passed `CasCatalogue.Language`,
`CasAcceptance.Kernel.DependentElaborationProbes`, and the unchanged
`CasAcceptance.DependentReaderProbes` target. The last target retains the selected
vector, destructured-map, bilinear admission/formed-pairing chain, independent
variable stage, and repeated matrix application checks. No permanent assertion,
full suite, leaf execution, or acceptance decision was run or changed by this
reconstruction.

### Exact identity of proof-bearing source inputs (2026-10-25)

The existing `Value.sameSource` context traversal and Lean's exact `Syntax`
comparison own repeated source identity. The corpus searches for
`Lean Meta isDefEq transparency`, `CategoryRealization family fibre`, and
`Subtype constrained point` and direct source inspection found no additional
mathematical owner or construction required. Exact explicit proof syntax now
participates in source comparison, just as each original constructor parameter
does. The whole object, category, selected structure, ordered arguments, routes,
and comparison data still have to match; different syntax or lexical macro
scopes are not identified. No proposition is erased or replaced, and
`typedParameter` still rejects proof syntax at a Type-valued parameter such as
`Invertible`. The omission had made a proof-bearing constructor fail reflexive
source comparison and repeatedly expand its retained context. The engineering
probe checks reflexivity, lexical separation, repeated full-context retention,
and the Type-valued-data boundary; the frozen RX05 export keeps its original
input, inventory, and ordinary per-statement heartbeat budget.

### Fixed data fields and complete family source binding (2026-10-25)

The same corpus queries above and direct source inspection identify the existing
owners: `ConstrainedPoint.schema?` fixes every record data field,
`declaredResult` checks an original point at an independently fixed endpoint,
and `CategoryContext.exposeStructureParameters` exposes all fields of a fresh
full structure parameter. The constrained reader now uses that existing endpoint
check before the unchanged actual constructor and proof checks. It preserves
the original point map and generalized domain; it does not add an ordinary
coercion or choose a named presentation from a shared carrier.

The structure exposure helper moves to `Semantic`, with the existing
`CategoryContext` name forwarding to it, so the complete family-source binder
can use the same operation. Only unresolved parameters of the already selected
realization are exposed, and the original full receiver and actual action-source
comparisons still have to succeed. Mathlib's existing `Equiv.ring` transfer
supplies the same-carrier/different-structure negative control. No dictionary,
mathematical declaration, registry row, proof obligation, or selected action is
replaced.

Structure-parameter type inspection unfolds the actual type with full
transparency before identifying its existing structure constructor. This also
handles a category alias such as `Cat`, whose full `Bundled Category` fields
are then constrained by the original whole functor. Exposure itself leaves the
fields unresolved; it supplies no carrier or category dictionary. The existing
automorphism construction supplies the complete-action control for this case.

### Reuse of independent closed file bindings (2026-10-25)

Corpus searches `Lean Syntax free identifiers macro scopes` and
`Lean Expr metavariables cache` locate syntax traversal and expression cache
facilities, but no dependency owns this DSL's selected file scope and stage.
The reader already had transitive bound-name analysis for closed declaration
arguments. That same analysis is shared with file bindings: only a binding
independent of every actual bound name, with no requested category, ambient,
or ring-generator binding, can use its original global reading. The original
global point is then restaged through the existing terminal map. Direct and
transitive stage dependencies keep their original evaluation context.

The existing per-question, per-trace cache also retains closed complete maps and
derived objects. Every retained endpoint/source context must be closed before a
map is cached. The existing exact-scope guard, speculative rollback, selected
structures, original arrows, and full Hom endpoints remain in force. No new
mathematical construction, ambient inference, question, or elaboration budget
is introduced. Engineering controls retain the exact global point and selected
target, preserve transitive bound variables under changed bindings, and check
that closed maps keep their full provenance.

Cache closure uses a dedicated complete-context traversal. The existing
`Value.terms` accessor remains the question-operand boundary: it intentionally
does not enumerate every retained application or an already judged question.
`sourceParameterValues` shares exact complete children, and the closure guard
checks each child's direct expressions, including full comparison applications,
question operands and types, and derived category bundles. Controls compare the
guard with the existing complete evidence encoder and reject metavariables,
universe metavariables, free locals, and loose binders hidden behind otherwise
closed map endpoints. This changes eligibility for reuse, not question identity
or mathematical equivalence.

The complete result endpoint returned by `invariantOf` is also passed to the
existing `applyFamily` target check. This retains the selected family owner's
context while avoiding a second reconstruction from operand carriers. The
original full application, operand source, result type, and callable-address
checks still run. A field-valued family control checks the original generalized
domain and complete selected result context. Stage-only measurements isolated
this duplicate endpoint reading; those measurements are localization evidence,
not successful fixed-question exports.

Complete family parameters also remain endpoint witnesses after the declaration
has been checked. Their actual full types determine the registered categories;
the original receiver and every full parameter remain available. The existing
`endpointWitnesses` preference and retry path chooses among these supplied
witnesses separately for each product factor. No parameter is discarded merely
because it occurs inside a preferred complete owner.

For an already checked defining construction leg, Lean's existing
`Meta.whnfHeadPred` can reduce its diagram/index projection until it reaches an
exact supplied endpoint handle. At that boundary the reader reuses the original
complete value. The same `sameSelection`/`retainObjectContext` rule already used
by `recognize` keeps every additional context payload; different full selections
fall back to the original endpoint and ambiguity checks. The original cone,
registered presentation, diagram, index, typed hom, and trace node remain checked
and retained. If primitive projection reduction passes an intact handle, absence
of an exact match also uses the unchanged fallback. No positional interpretation
of general retained context or equality of bare carriers selects a factor.

The generalized-map argument trial forks the current question's accepted trace
and closed-reading cache into separate references. Cached values therefore keep
their original operation records, and independent nested declarations need not
be rebuilt in an empty context. Speculative writes remain isolated; the existing
successful-trial trace merge and invalid-reading fallback are unchanged. Cache
entries obey the same full-context closure, stage, ambient and lexical guards,
and the temporary cache is never substituted for the caller's cache. Without an
existing trace, the trial starts with the existing empty-context behavior.

The exact unchanged first-pairing binding and full assertion now read within
the original 200000-heartbeat limit (125062 and 152825 respectively). Remaining
factor/final readings are separate open defects; neither stage measurements nor
this focused source checkpoint are full fixed-export or mathematical acceptance.

### Complete endpoint and point-source ownership (2026-10-26)

The corpus searches `Lean Meta profileitM isDefEq retained expression` and
`Lean Syntax cache scoped expression`, together with the existing reuse record
above, identify the reader's own complete-value and projection machinery as the
owner. Lean's existing projection metadata and `unfoldDefinition?` expose a
declared projection path while stopping at an exact supplied whole object.
`endpointWitnesses` uses that path when several complete parameters occur in an
endpoint: a parameter in a projection's implicit type does not replace the
actual projected owner. Ordinary field discovery keeps its existing transparency;
only this exact-owner check unfolds intervening declaration wrappers. Complete
same-carrier selections without an owned projection keep the ambiguity checks.

The existing `contextualNumeral` construction now retains the original point
together with its checked complete source, using the same `Value.element`
context representation already used by `forwardNumeral`. Identity carrier views
retain the source and target contexts. Source binding may reuse that exact
point's independently selected owner through its registered structural action;
it does not identify points by their computed values or choose a structure from
carrier equality. All original declaration parameters, point maps, selected
targets and admission obligations remain checked. Unresolved numeral operands
are formed only after the other supplied points fix a complete typed family.
The accepted whole parameter transport is replayed into an isolated family
recorder. Only a closed, type-correct whole application publishes those records;
the exact original receiver and every actual registered edge application remain
in the parameter's trace. Failed source trials publish no speculative actions.

`completeParameterObjects` shares the existing `invariantOf` parameter reading
with ordinary named-family applications. Each complete argument is retained in
its actual registered category before dependent endpoints are reconstructed;
the original supplied contexts remain alongside it. This avoids rediscovering a
fully supplied monoid while constructing its declared unit object. A directly
recognized inclusion target also retains its original complete domain context,
as the other endpoint paths already do. Literal
admission also reuses the existing global-point/restaging boundary: the original
numeral is admitted with its full proof, then precomposed with the actual stage's
terminal map. A variable never gains that numeral-specific admission.

`DeclaredContextBindingProbes` now checks the original scalar-module fraction
globally and at a stage, including the complete ring source and actual structural
actions in the division parameter's trace. Its existing same-carrier controls,
`ClosedBindingReadingProbes`, and `ReaderContextContinuityProbes` pass. A focused
reader extraction of the unchanged final structured-family block also preserves
both registry orders and the distinct-family ambiguity controls.

The first owner-repair checkpoint reads the unchanged original final statements
at lines 127, 130, 133 and 136 of `rx-lift-prescribed-stages.cas` in 175305, 185257,
189594 and 153349 heartbeats respectively under the ordinary 200000 limit.
Each starts with the complete
original preceding scope and its own trace and cache. The final factorization
and comparison at lines 146 and 149 also read (128402 and 151743). The additional
final factor samples at lines 152 and 155 still reach the same ordinary limit
inside `isDefEq` at that checkpoint. These are reader engineering
checks, not complete typed exports, real execution, or mathematical acceptance.

### Closed carrier actions within a declared endpoint (2026-10-26)

The remaining original final factor samples expose repeated reconstruction of
the same complete ring and module carriers while reading a typed function
parameter. A narrow production-reader profile attributes 14542 of the parameter's
21374 heartbeats to its declared function coordinate. Failed whole-endpoint
recognition rebuilds the same full supplied carriers before the function's
domain and codomain rebuild two of them again. The actual registered action,
full category checks and second telescope elaboration are not the hotspot.

The existing owners are `carrierObjectWithAction`, `Value.sameSource`, the
complete `Value.closedReading` traversal, `optionalReading` rollback and the
per-application carrier table already recorded above. One inclusion endpoint
read now owns a local table of these completed views. Exact source comparison
includes all original contexts, selections, declaration arguments, actions and
comparison witnesses. Stage or bound-variable contexts and trace-free trials
use their ordinary reading. No table is shared with a later independent endpoint request.

A reusable view retains only closed object-action records, with their complete
receiver, edge applications and category bundles. Its trace delta is replayed
only when every record required by its original reading is still present
unchanged. Missing or changed prior records cause ordinary reconstruction.
`Node` record comparison is syntactic, including complete bundles and accepted
binding IDs; it supplies no mathematical equality. Failed endpoint trials keep
their normal trace rollback, while a later successful use of the same complete
view restores exactly its checked action records. Other newly recorded constructions
and open retained inputs prevent reuse by this table.

The new engineering controls retain both complete modules and their actual
carrier actions after unsuccessful whole-function recognition. A failed trial
publishes no action, a retry recovers the original full ring action, and different
complete rings on the same carrier remain non-coercible in either direction.
No mathematical source, fixed question, expected answer, input context or caller
heartbeat budget changes.

The final source passes `DeclaredContextBindingProbes` (including the new trace
and failure-isolation controls), `ClosedBindingReadingProbes`,
`ReaderContextContinuityProbes`, and the unchanged `SelectedCarrierProbes`.
The unchanged final structured-family reader block also passes in both registry
orders with its distinct-family ambiguity controls. All eight original final
readings now fit the ordinary 200000-heartbeat budget:

| Original line | Heartbeats |
|---|---:|
| 127 | 166209 |
| 130 | 176163 |
| 133 | 180497 |
| 136 | 135292 |
| 146 | 119347 |
| 149 | 133704 |
| 152 | 191861 |
| 155 | 192278 |

These measurements use the complete original preceding scope and a fresh trace
and closed-term cache for each statement. They close the remaining measured
reader failures; full typed export, real execution and independent mathematical
acceptance are separate obligations.

## Inferred family endpoints retain their actual object-action sources (2026-10-26)

### Queries

The corpus queries `functor object forgetful carrier identity` and `Functor.obj forget`,
and local searches for `completeParameterObjects`, `structuredParameterView`,
`selectedParameterFromWitnesses`, `retainedCarrierRoute`, `identityCarrierView`,
`recognizeObjectApplication`, and `Semantic.objOf` identify the existing owners.
No new mathematical map, carrier identification, or proof procedure is required.

### Owner

Upstream registered morphism families determine their complete dependent parameters.
`Semantic.objOf` elaborates an actual object action as an explicit `Prefunctor.obj`
application. The language's `recognize` retains an already supplied complete parameter;
`selectedParameterFromWitnesses` checks that same whole parameter against the supplied
sources and retains its actual structural action when a source view is still missing.
`coalesceSelectedParameterViews` preserves every checked source presentation. The
ordinary carrier and coercion readers consume the resulting retained data.

### New code

When a family must reconstruct its result endpoint, `completeParameterObjects` now
reuses those readers for explicit object-action parameters before adding a bare
parameter witness. Previously it discarded the actual ring-to-monoid action after
the variable-exponent family had already selected its complete monoid. Its result
carrier therefore lost the named power-series origin, and the original series binder
could not pass that summand to its independently specified target.

A complete result target supplied by the caller already retains its own endpoint
context. `applyFamily` keeps that value and the original parameter-witness path.
Other complete bundled parameters also retain their ordinary endpoint reading. A
profile of the unchanged RX-LIFT pairing finds `CommRingCat.of` and `ModuleCat.mk`
parameters reconstructed from the supplied category fields; trying to discover new
source views for those fixed bundles adds unnecessary work. The actual object-action
boundary distinguishes these cases without naming a question, operation, or category.

The repair retains every original supplied context and fixes the complete structure
before checking its source actions. It leaves `identityCarrierView`, `coercionMap`,
accepted comparisons, and ambiguity controls unchanged. Rejected broader prototypes
produced determinant ambiguity or ordinary-budget timeouts; their exact measured
sources and failed logs remain in the separate engineering evidence archive.

The unchanged `DependentReaderProbes`, `ParameterStructureProbes`,
`SelectedCarrierProbes`, `DeclaredContextBindingProbes`, `ClosedBindingReadingProbes`,
and `ReaderContextContinuityProbes` pass. The exact original power-series expression
also passes its narrow reproduction. All eight original final RX-LIFT readings pass
with their complete preceding scope, a fresh trace and cache for each statement,
and the ordinary 200000-heartbeat limit:

| Original line | Heartbeats |
|---|---:|
| 127 | 166254 |
| 130 | 176210 |
| 133 | 180540 |
| 136 | 135329 |
| 146 | 119391 |
| 149 | 133742 |
| 152 | 192521 |
| 155 | 192526 |

These are isolated reader engineering checks. They preserve the original questions,
selected structures, complete contexts, expectations, and budgets. Full native
integration, typed question export, execution, and independent mathematical acceptance
remain separate observations.

## Numeral selection from each retained complete source — 2026-10-26

The corrected mathematical catalogue adds an accepted Ring-to-Semiring action.
The original rational arithmetic and declared scalar-module context then exposed
an existing reader inconsistency: `contextualNumeral` searched every inherited
numeral family even when the same complete named source already fixed its
literal reading. Exact diagnostics identified the retained named commutative
rational ring, its original Ring image, and the additional inherited Semiring
image; no owner was inferred from their common carrier.

`registeredNamedNumeral` already gives a named set's declared numeral
refinements priority, and `toElement` already gives a complete selected source
its own direct numeral family before inherited views. These row-selection rules
are now shared. Each contextual witness keeps its direct family if one exists.
Otherwise, a named source with an accepted set refinement reuses the existing
`setOf` and named-numeral rule. An admitted source or admitted base receives no
shortcut; an anonymous source receives no invented named presentation.

Only eligible numeral rows are selected this way. `bindSelectedReceiver` still
receives the untouched original complete witness and closes the whole owner
before the target coordinate is considered. `structuredParameterView` retains
the actual source and accepted action. Every original witness remains in
context, and the existing complete-owner and full-application comparisons remain
unchanged. A separately supplied Semiring stays independent of a supplied Ring,
even when their carriers and numeral values agree.

The corpus query `"Int.castRingHom" "Nat.castRingHom"` locates Mathlib's existing
cast declarations and rational-map extensionality lemmas. They supply no new
reader bookkeeping primitive, and no mathematical construction is introduced.
The implementation owners are the existing registered numeral families, named
refinement metadata, `setOf`, `bindSelectedReceiver`, `structuredParameterView`
and the full selected-source checks.

The original selected-carrier and declared-context controls pass on the clean
production source under the ordinary budgets. `ContextualNumeralOwnerProbes`
checks each sole complete Ring/Semiring source, independent-owner ambiguity in
both orders, and the named commutative source's exact Ring action and retention.
All eight unchanged original arithmetic assertions and prior bindings also read
successfully after this repair. Earlier named-only and direct-category-only
prototypes, their original failures and exact supplied-witness diagnostics are
retained as rejected engineering evidence. Actual connected execution is the
separate subsequent consumer check; no assertion, registration, mathematical
source, leaf or heartbeat budget changes.


## Closed comparison evidence within one claim (2026-10-26)

### Queries

The corpus queries `rigid type unification`, `category route reachability`, and
`memoization closed metavariables` supplied no replacement for the existing
consumer owners. Local searches read `Value.closedReading`, `Value.sameSource`,
`carrierReadings`, `parameterTrial`, `retainedCarrierRoute`, `checkedRouteAction`,
`RegistryState.completeRoutes`, `RegistryState.classify`, and
`Semantic.validateRouteComparisons`. The existing declared-context probe is the
only external construction of the carrier table, using an empty reference.

### Owner

`transportedStructureWithAction` already owns every complete target/type trial,
route enumeration, coherence class, and selected actual action. Its comparison
validator forms each accepted comparison at the actual complete receiver,
resolves required parameters, and checks the resulting evidence. It returns the
very same actual terms whose validation the reader was repeatedly discarding.
`Value.sameSource` compares complete supplied objects and retained contexts;
`Value.closedReading` and `closedReadingTerm` own reuse eligibility. Existing
carrier entries already retain their full trace preconditions and closed replay.

The unchanged full-import-context line 22 makes ten Bil-to-Sets transport calls
with four routes each before the earlier timeout. An isolated measurement of
that actual named source uses 82 heartbeats for all four routes, fewer than one
for classification, and 11229 for validation of the four comparison terms. The
returned comparison terms are closed. Category-shape rejection cannot remove
any further target: every measured call already independently demands Sets.

### New code

Share only completed comparison evidence within one fixed original claim, keyed
by the exact whole source `Value` and complete ordered `RouteComparison` array.
Every stored source context and every returned evidence term must be closed,
including absence of free variables. The original validator runs before any
entry is stored; a local class hypothesis cannot become reusable evidence.
The table retains the actual checked terms, not merely a success flag.

Every category trial, complete route enumeration, actual object application,
coherence classification, final selected action check, and trace record still
runs through the original owner. No target choice, unresolved requested type,
failed search, or stage-dependent point is cached. Existing carrier entries keep
their exact source and prior-trace checks. A failed enclosing reading may retain
closed comparison evidence but publishes no speculative trace.

The earlier reachability, full selected-transport, and pre-target action caches
are rejected diagnostic prototypes, preserved outside the repository. The action
prototype had no eligible complete edge applications on the failing equation.
The selected-transport prototype also required an additional comparison-evidence
closure guard; removing it entirely avoids that choice-reuse boundary. None of
those prototypes is part of the delivered code.

The three original RX-LIFT statements at lines 22, 73, 76 now complete all seven
production typed-export stages with the original full six-module import scope,
original preceding bindings, published mathematics ac9bb80, and unchanged ordinary
200000 option. Instrumented totals are 176035, 202567, 203162 heartbeats; the latter
totals include subsequent pure export work and are not asserted to be below the
option. No timeout occurs. The three original composed consumers also read.

Unchanged selected-carrier, declared-context, parameter-structure, closed-binding,
and context-continuity probes pass. The unchanged full dependent-reader probe
still reports a numeral-owner ambiguity at line 63 on the corrected mathematical
release; that distinct original-input blocker remains recorded, not counted as
a passing probe. Focused engineering controls cover real warm comparison reuse,
distinct retained full contexts, open-source refusal, failed outer reads and
trace retry, and unresolved-target ambiguity. An isolated opaque alias of an
existing generic comparison adds only an unused local class hypothesis: the
upstream cell validator accepts its original interface, the actual result keeps
the local free variable, no cache entry is stored, and retry outside the local
context fails. No mathematical source, registry, original input, selected owner,
ambiguity rule, caller budget, or shared artifact is changed by this repair.


## Declaration identity of newly retained complete parameters (2026-10-26)

### Queries

The corpus queries `declaration application provenance` and `registered numeral
owner` found unrelated verification records. Local searches read
`completeParameterObjects`, `recognize`, `recognizeObjectApplication`,
`contextualNumeralRows`, `namedNumeralRows`, and `sourceParameterValues`.
The exact original dependent-reader capture has two supplied Values with the
same complete `NamedCommutativeRings.integers` term. One retains the named row
and its original integer context; the other was introduced as a plain object
with no origin, selection, or view data. The latter contributes an inherited
Semiring numeral alongside the named source's declared Ring numeral. The
failure occurs only at the final subsequent zero in the original line 63 block.

### Owner

`recognize` already owns declaration identity. It matches the actual registered
declaration head, checks its complete arguments and types, and reconstructs the
same selected object row through `recognizeObjectApplication`. It does not infer
a parameter-free named alias from a shared carrier. `completeParameterObjects`
already retains each complete declaration parameter and every original supplied
Value. The existing named-numeral rule is correct when that declaration identity
is retained; no numeral-owner selection rule needs to change.

### New code

Before introducing a fresh plain parameter witness, reuse `recognize` only when
that exact parameter application names an object declaration registered in its
already checked category. Pass the unchanged original witnesses and complete
fixed parameters. Failed recognition retains the previous path, including the
existing source-action retention rule. No original supplied witness is deleted,
renamed, or merged; in particular, an independently supplied anonymous full
structure remains independent. No arbitrary alias is recovered by unfolding a
carrier, and no new structural search is added for an undeclared application.

An additive control reproduces the same ambiguity before this change when the
already supplied named integer object is revisited as a complete parameter.
A separate negative retains an explicitly supplied anonymous full witness in
both orders and requires the original ambiguity to survive. The original probe,
mathematics, fixed statements, expected answers, and budgets remain unchanged.

The narrow counterexample now reads, while explicitly supplied anonymous full
witnesses remain ambiguous in both orders. The unchanged original full
`DependentReaderProbes` passes, including its line 63 sequence and original
power-series binder. Unchanged parameter-structure, selected-carrier,
declared-context, closed-binding, context-continuity, and the existing
Ring/Semiring numeral-owner controls also pass on the final source. The three
full-context RX-LIFT readers complete every typed-export stage with total
counters 113508, 201054, 201631; the unchanged ordinary option remains 200000, and
these counters include later pure export work. The three unchanged composed
consumers also pass. All source guards close unchanged. Exact failed/successful
runs, full source-witness capture, and diagnostic restoration receipts remain
in the separate engineering archive. No new original-probe failure remains in
this reader workstream; full native/export/execution integration stays separate.

## Retain the actual closed action of a local route trial (2026-10-26)

### Queries

The corpus query `reuse complete typed functor application` could not reach the
corpus API in the isolated execution environment. Local source searches identify
the existing owners: `Semantic.routeFunctorWithApplications`,
`Semantic.bindFunctorSource`, `Semantic.objOf`, `parameterCompatible`,
`transportedStructureWithAction`, and `checkedRouteAction`. This change consumes
those same constructions and introduces no mathematical operation or registry row.

An exact original RX-LIFT factor-sample read, with all 32 preceding bindings and
its original six-module scope, takes approximately 184391 of the ordinary 200000
heartbeats before question construction and execution. The full original profile
has 211 distinct trace roots; a repeated-root cache cannot remove this work.
The original full 26-ID outcomes and pure questions remain the reference inputs.

Corrected IO-dependent measurements of the twenty retained closed Values cost
about 2 heartbeats for all flattened terms, 7 for source traversal, and 8 for
closure checks. Earlier pure-action timings could evaluate their inputs before
the timer and do not support the same inference. This exclusion is limited to
the actually retained Values measured by the corrected diagnostic.

On the actual complete source of the original `i1`, enumeration of all four
routes costs 82 heartbeats, classification 35, and cached comparison evidence
less than one. Constructing and applying the four candidates costs approximately
1075, 988, 590, and 508 heartbeats. The selected route is then constructed again
for its final check. All four trial images and all their actual edge applications
are closed. Directly constructing the same two object-projection applications
preserves every tested expression, inferred type, category bundle, and application,
but saves only about 93 heartbeats across all four candidates; it is not this repair.

### Owner

`transportedStructureWithAction` already forms every candidate by the registered
route at the actual complete receiver and expected type. Its speculative trial
discards metavariable assignments and emits no trace. Classification and accepted
comparison validation determine the unique source route. `checkedRouteAction`
then checks its complete inferred endpoint type, instantiated image, every actual
edge application, and type correctness before recording the retained route.

### New code

Each successful local applicability trial may retain its actual instantiated
image and ordered edge applications only when all those terms are closed,
including absence of free and loose bound variables. The candidate keeps this
optional payload alongside its original target and full Route. Every original
candidate and its order remain present; the same target key, full route,
prefix filter, classification, comparison witnesses, and ambiguity rules apply.

After selecting the unique source, reuse its closed actual construction and run
all the original final checks and trace recording. In particular, re-match the
complete inferred type against the live expected expression. The expected type
may initially contain universe metavariables; its speculative assignments are
discarded and are not retained as evidence. An open image or application uses
the original fresh construction. The common final validator contains the
unchanged checks and is called for an actual construction from these original paths.

This reuse lasts for one invocation only. It stores no route choice or success
across calls, changes no registry key or state ownership, and weakens no existing
carrier-cache trace precondition. The additive `ClosedRouteTrialProbes` compares
complete selected images, inferred types, applications, and trace records with
the original fresh action for both a closed group and a genuinely open local
group. Existing full-context, nonidentity, ambiguity, and closed-binding probes
remain unchanged.

### Verification and remaining execution margin

The reviewed implementation compiles in an isolated artifact prefix, using the
unchanged native dependency closure. The first compile rejected a private helper
referenced by public declarations; the final revision makes the ordinary checking
helper public without changing its body or callers. All seven unchanged controls
pass: `ClosedBindingReadingProbes`, `DeclaredContextBindingProbes`,
`ReaderContextContinuityProbes`, `SelectedCarrierProbes`, `ParameterStructureProbes`,
`DependentReaderProbes`, and `MethodComparisonRetentionProbes`. The additive
closed/open group control also passes. Source, input, selected-artifact, and
shared-library guards close unchanged on each execution.

Both original factor-sample assertions, with all 32 original preceding bindings
and their complete six-module import scope, now finish interpretation and
computation-only evaluation within the observed unchanged 200000-heartbeat option:

| Original assertion suffix | Interpretation heartbeats | Total heartbeats | Outcome |
|---|---:|---:|---|
| `first_factor_sample_one` | 194599.735 | 198280.584 | existing `mor.sets.tuple_cons` implementation gap |
| `first_factor_sample_two` | 195114.394 | 198788.432 | existing `mor.sets.tuple_cons` implementation gap |

The complete canonical question strings are byte-identical to the original full
26-ID profile, including all typed terms and operation records. The external
diagnostic opens the `CasCatalogue` namespace, so its displayed proposition omits
261 namespace prefixes in each case and wraps lines differently. Removing only
those display prefixes and whitespace makes the displays equal; no normalization
is used for the canonical question comparison.

The prior pre-evaluation internal timeouts are removed on this measured tuple,
but these are gaps, not computed assertions, and no backend dispatch occurred.
Only about 1719 and 1212 heartbeats remain after these executions. The combined
kernel's exact two-case preflight is still required before claiming enough budget
for its additional complete module execution. The final unchanged full production
run remains separate; this bounded diagnostic does not replace it or discharge
the original mathematical assertions.

The initial additive module fixture failed identically on the untouched baseline
and the candidate. That fact alone did not establish fixture invalidity. A
separate diagnostic preserves the full supplied receiver/category and shows that
its open `ModuleCat ℚ` type contains one unresolved universe metavariable. The
same metavariable remains in `cell.additive_groups.carrier`, whiskered by the
fibre inclusion and additive-group action; there are no residual term metavariables.
`CategoryContext.ofNamed` independently rejects this incomplete category before
comparison. The original closed module and a separately supplied open
`ModuleCat.{0} ℚ` both reconstruct the exact complete category and leave no
unresolved comparison parameters. No universe default is supplied to the original
fixture. This failure is not evidence of a comparison defect at a complete module
category, and the group control establishes only local action reuse and fallback.

## Original evidence targets and isolated equivalent views — 2026-10-28

### Queries

The author searched the formalization corpus for `withoutModifyingState` and
`evidencePresentation`; both queries were blocked by the corpus API's
`Operation not permitted` error. Local searches and reads covered Lean's
`MonadBacktrack.withoutModifyingState`, `Term.SavedState`, `Meta.SavedState`,
`Core.SavedState`, `Tactic.run`, `Lean.collectAxioms`, and the existing
`Language.runProcedure` and `EvidencePresentation` consumers.

### Owner

Registered evidence procedures and their mathematical targets remain owned by
`lean-categories`. Lean owns rollback, kernel checking, auxiliary declarations,
and transitive axiom analysis. Existing stored-field and closed-type
presentations supply definitionally equal views; no new mathematical procedure
or registry declaration is introduced here.

### New code

The consumer distinguishes ordinary rejection from malformed logged output and
tries original, stored-field, and type-visibility targets lazily with the same
provider and budget. Each returned term must inhabit the complete original target.
Caller metavariables and ordinary messages are restored between attempts; only a
successful, rechecked environment is retained. Newly returned constants must
exist in the checked environment and cannot hide `sorryAx` or add an assumption
absent at the original question. `EvidenceViewEngineering` exercises ordering,
state and budget continuity, malformed-output refusal, auxiliary persistence,
failed-auxiliary isolation, and hidden-hole/new-assumption refusal.

The exact final source/control patches and their evidence-presentation preimage
were recovered after a workspace replacement. Earlier prototype passes do not
substitute for compiling and running the original production controls against
the recovered source. Protected questions, expected answers and budgets are unchanged.

## Retain the original admission producer — 2026-10-31

`Language.admit` creates a new interpreted producer. It now keeps the handle
returned by `Trace.recordProduced` for the checked admission and any original
terminal comparison composite, then uses `Trace.aliasProduced` after the unchanged
`homIn`. The original declaration, evidence, ordered parameters, categories and
endpoints remain exact. The outward expected-type wrapper therefore retains the
address required by the existing canonical invocation owner. The passing public
admission control checks distinct equal-formal producers and stable reuse of
each complete result; the original first RX-LIFT preparation also passes. The
[realizer reuse record](cc-realizer-first.md#original-admission-parameters-and-producer-retention--2026-10-31)
records the causal packet comparison, focused receipts and remaining engine gate.

## Private complete snapshots and bounded profiling (2026-10-29)

### Preserve an existing producer when recording a fixed-parameter view

The unchanged integer-coordinate control in `ReaderFamilyParameterProbes` exposes a call
from `recognize`'s fixed-parameter endpoint branch to `Trace.record`: it tries to attach
`parameterEquivalence` to an exact key already owned by `object obj.rings.integers`.
The collision refusal is correct. The existing owners are `Trace.record` for recovery of
the same complete node and `Trace.recordProduced` for a new producer with ordered typed
children. Source inspection of those functions, `coalesceSelectedParameterViews`,
`retainedCarrierRoute` and the equivalence consumers in `Realize` supplies the reuse argument;
no new mathematical declaration, identity mechanism or equivalence test is introduced.

After unchanged full-view coalescing, the fixed-parameter branch now inspects only the exact
key in the same writable trace. If its complete node already agrees, the old parameter is
returned without a new wrapper. If a different record owns that key, a fresh equivalence
producer is returned, with the original parameter and every original evidence child retained.
If the key is absent, the old self-record path remains. This distinction matters: forwarding
an unrecorded representative could reopen named recovery and lose an already checked view.
The lookup does not consult a source recorder, normalization, carrier equality or data bytes.

The outward value uses the new handle; its evidence source, complete route applications,
ordered alternatives and original literal action receiver remain exact children. Carrier
conversion replays that original evidence and checks the complete result before using the
outward handle. All category, full-type, prefix/result, endpoint and ambiguity checks remain.
The two adjacent analogous branches remain unworked rather than receiving an unexercised
blanket rewrite. `ReaderFamilyParameterProbes` and `ProducerOccurrenceProbes` are the existing
verification boundaries; source inspection is not a passing runtime result.

### Existing snapshot and performance work

Source inspection of `readingTrace?`, `eval`, `structuredParameterView`, the joint
family-argument trial and the generalized-map argument trial locates the existing
owners of the original records. A private recorder now copies the complete
`readingTrace?` snapshot before clearing only its redundant `sourceTrace` field.
The inherited records remain in that isolated copy; subsequent writes remain
private until the existing success path commits them. A recorder that starts
empty retains its inherited source. No producer, parameter, comparison or
mathematical reading is removed. This restores the recorded correction after
the workspace restart; the unavailable original commit is not claimed recovered.

Optional profiler regions separate carrier-map applicability, selected map
reconstruction and final checks, joint family binding and subsequent rebinding,
complete parameter reconstruction and declared endpoint reconstruction. The latter
also separates field discovery from endpoint recognition. They use
the existing `profileReader` switch and preserve the original execution order
and checks. The original 200000 question budget is unchanged. Earlier measured
producer-wrapper construction was negligible and is not an optimization target.
Fresh-reading engineering comparisons use the existing full typed-question
comparator, while repeated exports of one prepared question still require exact
identity equality; fresh administrative occurrence numbers are not mathematics.

The first latest-main factor-sample profile stops at the original preparation
budget. Lean 4.33's `Lean/Util/Profile.lean` specifies exclusive group totals:
endpoint reconstruction accounts for 3.57 seconds and complete parameter discovery
for 1.43 seconds of the observed 18.307 seconds. Committed family rebinding is
25.7 milliseconds; no carrier-map group appears. These measurements do not justify
changing carrier-map applicability, dropping candidate categories or caching a
semantic reading by equal carriers. The two inner endpoint regions attribute the
next correction before any sharing of structural owner analysis is implemented.

That split attributes 3.73 seconds to recognition and 757 milliseconds to field
discovery in the next unchanged sample; no structural-owner cache is selected.
Three pure changes remove demonstrably unused work: empty context retention returns
its original value immediately, declaration-head recognition skips unused witness
expansion, and the fixed declaration-row filter is computed once before its supplied
witness loop. Optional subregions now measure carrier conversion, full-handle
comparison, endpoint preference and parameter category trials. No source witness,
candidate multiplicity or comparison is removed. Global witness deduplication is
not substituted: preference currently branches on multiplicity and must retain its
existing complete-owner selection until separately justified.

On published source `695210`, the same original sample still exhausts its 200000
budget (19.481 seconds, 200000261 raw ticks). The new exclusive regions report
4.94 milliseconds for full-handle candidate comparison, 0.821 milliseconds for
witness preference, 878 milliseconds for carrier conversion and 1.56 seconds for
parameter category trials. Remaining endpoint recognition takes 2.64 seconds;
field discovery takes 618 milliseconds. These measurements rule out candidate
comparison as the dominant target. Lean 4.33's `Meta.SavedState.restore` preserves
the WHNF cache used for closed expressions under the same configuration, so
explicitly hoisting repeated closed-endpoint `whnf` calls would mostly duplicate
existing sharing. No such cache or hoist is introduced. The existing preparation
and explicit-export controls pass on this source, including fresh full-question
comparison, dispatch agreement and missing-producer refusal before execution.

The next optional attribution wraps the existing complete `recognizeObjectApplication`,
`selectedParameterFromWitnesses`, `structuredParameterView` and
`coalesceSelectedParameterViews` bodies. The named-object label distinguishes the actual
constructor rows. No branch, comparison, candidate or returned value changes. This separates
supplied-witness applicability from committed conversion and provenance coalescing before
deciding whether any completed local interpretation can be retained safely.
