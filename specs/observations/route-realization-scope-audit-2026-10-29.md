# Scope audit of the route and realization proposals

Assessment date: 2026-10-29.

The current issue comments retain semantic resolution and distinguish simple structural routes from arbitrary composites. The earlier proposal to remove resolution used the output of that stage as a reason to remove it. Other claims remain that confuse mathematical meaning, executable data, and a representation of programs.

This assessment concerns the proposals and their stated reasons. It does not establish an execution failure or accept a replacement architecture. The current work order remains [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10) and [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69).

## Evidence inspected

The issue sources are [#79 and its comments](https://github.com/dzackgarza/lean-cas-dsl/issues/79), [the revised #99 comment](https://github.com/dzackgarza/lean-categories/issues/99#issuecomment-6473711857), and [the implementation-reuse comment on #76](https://github.com/dzackgarza/lean-cas-dsl/issues/76#issuecomment-6471649631). The live corrected #79 comment proposes a map from resolved formal questions to programs. The first two entries below record corrected claims and the source facts that settle them; the remaining entries identify claims that still need correction.

Source checks used kernel `60771b7c3fba512ad19c0974a009cd8435133165` on `work/kernel-v1-20261023` and upstream `8782c22ba613a022a84a1e910b6489cc2503e29a`. The claims below are source analysis and explicit mathematical arguments. No build or execution result is claimed.

| Claim in the proposals | Defect | Required distinction |
| --- | --- | --- |
| A fully elaborated question makes route discovery and ambiguity handling unnecessary; corrected in the current comments | It assumes the output of the stage being removed | Surface resolution versus execution of a resolved question |
| Cyclic paths prevent any finite route-enumeration argument; corrected in the current comments | It substitutes all walks for the implemented simple structural routes | Expressible composites versus the automatic-discovery domain |
| Fixed formal types remove computational dependence on answers | Later computations must consume actual earlier results | Semantic authority versus computational data dependence |
| Reply-shape branching requires dependent effects; an ordinary free monad is inspectable first-order syntax | These are separate type and representation questions | Fixed-result branching, dependent result types, and explicit program syntax |
| Every composite realization must sequence the generating calls | It excludes permitted direct implementations of a composite | Formal composition versus the selected execution plan |
| Every strict categorical pullback needs isofibration evidence | It turns a sufficient comparison theorem into an existence requirement | Strict limits versus equivalence with pseudo-limits |
| A CAP leaf can replace the generic derivation mechanism | It moves a backend-independent obligation into one engine | Formal reductions versus an engine's implementation inventory |

## Resolution must produce the route that execution consumes

An earlier version of the [#99 correction](https://github.com/dzackgarza/lean-categories/issues/99#issuecomment-6473711857) removed both discovery and ambiguity search because an elaborated expression already contains its route. That argument applies after resolution. It does not supply resolution. The current version restores this phase distinction.

The intended surface includes `X.cardinality()` and `#methods`, without a manually supplied composite. [CC-RESOLVE and CC-COHERE](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/specs/computational-core.md#cc-resolve--composite-resolution-with-provenance-and-ambiguity) require the reader to derive that composite and handle competing structural projections. [CC-CLOSURE](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/specs/computational-core.md#cc-closure--the-user-visible-method-surface-is-generated) also requires a new category to inherit applicable old operations without forwarding declarations.

The source implements exactly this phase distinction. [`resolveMethod`](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/CasCatalogue/Resolve.lean#L402-L419) forms candidates before producing a resolution. [`Trace.MethodApplication`](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/CasCatalogue/Trace.lean#L103-L118) then retains the selected applications for execution.

Execution should consume that selection without repeating it. Requiring every caller to provide the selection, or dropping the ambiguity cases, would change the language. Replacing enumeration with another adequate resolution mechanism remains possible; the existence of its required output is not such a mechanism.

## Infinite path syntax does not refute the implemented finite bound

Cycles give arbitrarily long walks. They do not give arbitrarily long simple paths in a finite graph. These are different mathematical sets.

The upstream [`SemanticState.routes`](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/LeanCategories/Catalogue/Registry/Semantic.lean#L1612-L1625) maintains a visited-category list and excludes revisits. Its [edge inventory](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/LeanCategories/Catalogue/Registry/Semantic.lean#L1564-L1577) uses designated structural functors and classifier forgetful maps, rather than every functor in the catalogue. An adjunction elsewhere in the catalogue does not by itself show that both adjoints are implicit structural edges.

The kernel's [`completeRoutes`](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/CasCatalogue/Resolve.lean#L343-L369) first discovers a reachable enclosure, then passes its size to this simple-route enumerator. The elementary bound is valid even when the enclosure contains cycles: a path without repeated vertices in an enclosure of size `n` has at most `n - 1` edges. A self-loop supplies infinitely many walks but no extra nonempty simple path from its vertex to itself.

There is still a real obligation. Finite registration does not alone prove that constructor-generated category expressions have finite reachable closure. Nor does enumerating simple routes prove that every cyclic composite is redundant. Simple paths are not closed under composition. The source therefore supports a finite bound for its stated search domain, not completeness for arbitrary path syntax.

The required analysis is to relate the admitted implicit structural routes to that domain while retaining explicitly expressed composites. It is not an acyclicity requirement, and it does not justify deleting inherited-method discovery. The enclosure cap is also a resource limit: exceeding it establishes failure to close within that limit, not mathematical nonexistence of a finite enclosure. The current error text at `Resolve.lean:323–325` overstates that conclusion.

## Fixed meaning does not eliminate dependence on actual results

The #79 body and its first disposition infer that computational dependence on an answer disappears once all formal result types are fixed. This is false even for `g(f(x))`: executing `g` requires the data returned by the selected execution of `f`. The meaning of the formal composite can remain fixed throughout.

For a structured result, let a formal request specify a kernel with its inclusion. After execution, projection and application must use the apex and inclusion from that particular returned result. A closed formal expression for the kernel does not supply those computed components. This is the central deliverable of [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69), not an optional effect-system feature.

Likewise, closedness does not mean absence of functions or dependency. The term `fun x => x` is closed. A closed application can contain a function argument and dependent intermediate interfaces. The existing [language](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/CasCatalogue/Language.lean#L38-L120) already includes maps, binders, integrals, limits, and indexed operators. [`Trace.Node`](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/CasCatalogue/Trace.lean#L179-L258) retains callable bodies and binder inputs.

This does not establish a need for higher-order effects. An ordinary mathematical map is not automatically an effectful computation argument. A first-order instruction language can carry explicit callable references and dependent interfaces. The proof obligation is that it represents the existing operations and their data flow. The firewall fixes mathematical authority; it does not erase data flow.

## Branching, dependent effects, and inspectability are separate questions

The [first #79 disposition](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6472941668), section 3, treats branching on a reply's sum shape as dependent continuation machinery. That implication is false. For example,

```text
k : (Nat ⊕ Bool) → Prog Nat
```

can choose a branch while retaining the same result type `Prog Nat`. Ordinary free-monad sequencing supports this. A genuinely dependent result type indexed by the returned value is a different question. Which reply shapes the published contract permits remains a separate contract fact.

Conversely, fixing `R q` does not turn

```text
Call : (q : Q) → (R q → Prog A) → Prog A
```

into first-order inspectable instruction data. Its continuation is a host-language function. It supports execution, including repeated execution, but does not provide a generic finite serialization or inspection procedure for that function. The [later #79 correction](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6473712582) repeats the first-order conclusion without resolving this representation issue.

The proposed explicit instructions and bindings can address inspectability. Whether their interface is sufficient must be checked against the supported operations. Neither closed formal terms nor the mere presence of sum types proves the answer. These facts do not require an owner choice between effect libraries.

## Composition must also admit a direct implementation of the composite

The [later #79 obligations table](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6473860708) states KM4 as sequencing the realizations of a route's generating cells. As an unconditional execution requirement, this loses a supported case.

[CC-ROUTE](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/specs/computational-core.md#cc-route--capabilities-register-against-semantic-operations-never-backend-methods) permits registration against a normalized composite. Suppose a provider implements `G ∘ F` on the declared input form, while no provider implements the separate requests for `F` and `G`. The composite has a registered implementation. Requiring separate calls would incorrectly produce `NoImplementation`. When both alternatives exist, a single fused call and a sequence of calls also need not have the same effects or returned data.

Sequencing is the interpretation rule for a selected sequential program. A directly registered composite is another permitted program for the same fixed formal operation. The kernel must retain the operation's meaning and required comparisons in either case. It cannot infer equality of the two executions from a formal composition equation. The current #69 work explicitly preserves fused execution; no new decision is needed to keep it.

## Strict pullbacks do not require isofibrations to exist

The revised #99 acceptance requires isofibration evidence for a registered strict pullback. That adds a false mathematical restriction.

For functors `F : C → E` and `G : D → E`, the strict pullback has objects `(c,d)` with `F(c) = G(d)`, and corresponding pairs of morphisms satisfying equality. The iso-comma instead retains a specified isomorphism `F(c) ≅ G(d)`. These constructions have different universal properties. An isofibration leg is a sufficient hypothesis for the canonical comparison from the strict pullback to the iso-comma to be an equivalence; it is not a condition for forming the strict pullback.

Here is a concrete distinction. Let `I` have distinct objects `0,1` and a unique morphism between each pair. Let two functors from the terminal category to `I` select `0` and `1`. Their strict pullback is empty, because the selected objects are distinct. Their iso-comma is terminal, because the selected objects have exactly one isomorphism between them. Neither selecting functor lifts that isomorphism. The strict pullback nevertheless exists and has its strict universal property.

Replacing it by the iso-comma changes empty to nonempty. The kernel must consume the construction that the formal specification names, including its actual hypotheses. It must not add an isofibration requirement to every strict limit or substitute a pseudo-limit. This distinction also prevents reducing the role of isofibrations to a blanket construction-validity flag: their defining lifting data transport structure along isomorphisms, while other constructions require their own hypotheses.

## A CAP implementation does not replace generic formal derivation

The [#76 reuse table](https://github.com/dzackgarza/lean-cas-dsl/issues/76#issuecomment-6471649631) proposes removing the derivation planner through a CAP leaf. CAP is relevant prior art, but that substitution does not discharge the same responsibility.

The inspected [`ComputationDerivation`](https://github.com/dzackgarza/lean-cas-dsl/blob/60771b7c3fba512ad19c0974a009cd8435133165/CasCatalogue/ComputationDerivation.lean#L1-L130) consumes upstream-checked whole-family identities, specializes their dependent parameters, and tracks prerequisite computational support. [CAP's mechanism](https://homalg-project.github.io/CAP_project/CAP/doc/chap8_mj.html) instead installs implementations in a CAP category from its available primitives and derivation rules.

A CAP leaf can compute an already registered composite. That does not supply generic execution of admitted reductions whose prerequisites come from other providers, or replace the formal authority for those reductions. The useful reuse is the derivation design, or CAP behind a leaf. A common program interpreter may replace the current module, provided it retains the same backend-independent responsibility. Deleting a module and moving its work to one engine is not that result.

## Consequence for the existing work

Keep the current inherited-method, ambiguity, dependent-interface, retained-result, and independent-extension requirements. Treat the proposed data structures as candidate implementations of those requirements. Establish the required behavior before using a representation change to declare an obligation absent.

The existing #76 disposition already rejects phantom indices as complete checks, unconditional codec replacement, and deletion by line count. Those claims need no new owner decision. The additional defects above concern the mathematical reasons offered for removing or narrowing required behavior.
