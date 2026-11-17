# Mathematical execution model

This document explains the required architecture of `lean-cas-dsl`. It is a specification,
not a statement that the current implementation satisfies it. The normative obligations are
[C1–C8, C22 and C23](../.specify/memory/constitution.md). The November 17, 2026
repository-wide clarification authorizes this maintained local explanation and its feature
requirements. Issue records continue to own assignments and implementation evidence.

## Mathematical authority and category interfaces

`lean-categories` owns the formal universe and the abstract computational obligations.
`lean-cas-dsl` reads and composes those declarations. Leaves supply computations for the
published obligations. A category declaration determines its objects, morphisms, endpoints,
identities, composition, named operations, structural functors and additional data or laws.
These are formal mathematical objects, not a software taxonomy derived from backend classes.

A leaf can choose an algorithm and private storage. It cannot choose what counts as an object,
which laws apply, or what an answer means. A constructed object has its category's whole
applicable mathematical interface. Whether an installed provider can compute a requested
operation is a separate question. Lack of a provider produces the specified execution error;
it does not remove the method or change its meaning.

## Functorial inheritance and target construction

Let `F : C → D` be an admissible structural functor and `P : D → E` a declared method.
The interpretation of an inherited call on `X : C` is `(P ∘ F)(X)`. On an arrow
`f : X → Y`, its action is `(P ∘ F)(f) = P(F(f))`. A new forwarding method on `C`
is not part of this definition.

The realization of `F` computes data from the public interface of `X` and passes them to a
public constructor of `D`. Its arrow action similarly constructs an arrow in
`Hom_D(F(X), F(Y))`, with the actual selected endpoints. Reusing a selected target value is
valid when that is the declared action. Public construction can be lazy; completeness concerns
the specified interface and selected dependencies, not eager computation or fresh allocation.
The formal laws are `F(id_X) = id_{F(X)}` and `F(g ∘ f) = F(g) ∘ F(f)`.
Independent mathematics fixes these laws; a leaf is not asked to prove its own correctness.

After construction, `F(X)` supports the operations of `D`. An unchanged implementation of `P`
can consume it through that interface. Origin remains relevant to selected dependencies and
maps, but is not a prerequisite for target-category method applicability. Neither leaf needs
access to the other leaf's private representation. A fused algorithm can realize `P ∘ F`
provided it meets that same mathematical and dependent computational obligation.

Not every method is an ordinary functor from its owner category. For example, cardinality is
an isomorphism invariant: its categorical domain can be the core groupoid. It is not a functor
from all set maps to a discrete category of cardinal numbers. `MethodShape.object` and
`MethodShape.isoInvariant` distinguish these cases in the formal registry. Operations on
parameter objects, dependent sections, slices, arrow categories and higher cells retain their
own formal types. Implementations must consume those types rather than force every operation
into an object-only method model.

## Resolution precedes provider selection

An inherited name is resolved through source-sanctioned functors to a declared operation.
A route `F_n ∘ … ∘ F_1` denotes a particular composite, including parameters and comparisons.
Reachability, equal endpoints, short route length or registration order do not identify two
routes. For parallel routes `F` and `G`, a comparison must have the exact formal consequences
needed for the requested operation. A natural isomorphism `η : F ⇒ G` gives components
`η_X : F(X) → G(X)`; it does not assert judgmental equality of arbitrary results.

C6 permits an explicit preferred binding through the released contract. Such a preference
records a selection and asserts no equality between routes. Definitional equality of the complete dependent operation families can also establish agreement.
Without a valid selection or the required agreement, report ambiguity before execution. Provider availability, caches and
successful computations cannot settle that mathematical ambiguity.

## Properties, refinement and choice

For `p : E → C`, the classifier query is `Nonempty (p⁻¹(X))`, using the formal categorical
fiber. A refinement requires the declared rule and its evidence. For example, formal evidence
that an integer interval is finite can support its specified lift into finite sets, with the
prescribed identification of its underlying set. A backend's finite list is not that evidence.
A computational predicate reply remains a candidate answer; it is not a new Lean proof.

Existence of structure and selected structure differ. A proof of existence of a basis supplies
no chosen basis for a later coordinate computation. A computation that selects a basis must
retain that basis and its relation to the original object. The same rule applies to orientations,
enumerations, presentations and lifts. Several refinements may apply at once. The operation's
formal domain determines which evidence it needs; a unique most-specialized runtime class is
not assumed. If the required classifier or refinement theorem is absent upstream, downstream
code must expose that missing formal input rather than invent a classification rule.

## Selected constructions remain usable

For a selected limit of `D : J → C`, retain its cone, apex, legs and universal operation.
The request for a leg at `j` projects the selected cone. Two cones can share an apex, so an
apex expression cannot identify the selected diagram or its maps. Colimits obey the dual rule.

For a selected lift of `i : K ↪ U(X)`, retain its result `X′`, map `i′ : X′ → X`, and the
specified comparison `α : U(X′) ≅ K`, with `U(i′) = i ∘ α` when these are the formal directions.
A later action uses those selected values and maps. A forgetful image cannot recover discarded
structure; further structure needs retained data or a new specified construction with its choices.

Mathematical equality does not identify computational occurrences. Independent computations may
have equal formal results while retaining different choices or dependencies. Each use must keep
its exact binding and returned occurrence through projections, substitutions and subsequent
calls. Expression matching, payload equality and global endpoint searches cannot supply that
association. Dependent outputs consume the earlier fields prescribed by the formal interface,
without runtime cases named for one particular construction.

## Execution and diagnosis

The common path is a checked source judgment with context and selected data, followed by
categorical interpretation, preparation of the complete dependent request, leaf realization,
and continued use of the actual result. Initial, deferred and provider-requested public calls
use the same mathematical preparation. The runtime resolves scoped actual operands and retains
results; it does not build an independent interpretation of a wire description.

C22 permits structural elaboration and composition of published operations. It prohibits Lean
reduction as an unpublished mathematical computation. Registered formal proof procedures have
the separate propositional role stated there. Backend answers cannot revise a prepared denotation.

When a continuation fails, trace the selected declaration, its complete interface, the returned
occurrence and the consuming argument. Locate the boundary that lost the required association.
Repair that boundary and its consumers, and remove the recovery substitute in the same change.
For a missing endpoint, retain the selected morphism's projection. For a missing limit leg,
retain its cone. For a missing dependent argument, preserve the formal dependency. For a missing
method, establish the admissible composite and comparisons. For a refinement, obtain the formal
evidence and construction. Improving a recognition heuristic does not discharge these repairs.

## Required growth and evidence

An independently added category and its immediate functors must work with unchanged existing
categories and target consumers. An independently added generic method must apply to existing
eligible objects without edits to their leaves. Generic execution must accept new admitted
constructions without adding category-specific interpretation cases. Replacing a provider may
change computational coverage or correctness, but cannot change the formal denotation.

The [feature scenarios](001-categorical-research-language/spec.md#mathematical-model-acceptance)
state observable obligations. They supplement the original mathematical workloads and independent
extension requirements; routing logs, opaque peers and successful helper checks do not establish
those mathematical results. Acceptance remains independently authored under C9–C12.

## Owning sources

- [Independent mathematical API and ownership](https://github.com/dzackgarza/lean-categories/blob/main/INTENT.md).
- [Functor target construction](https://github.com/dzackgarza/sage-categories/blob/main/specs/functor.md#functor-actions-are-concrete-constructors) and [public category interfaces](https://github.com/dzackgarza/sage-categories/blob/main/specs/leaves.md). These supply the constructor-composition principle; their Python class and trust conventions do not replace this repository's independent Lean authority or acceptance rules.
- [Formal method domains](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Catalogue/Registry/Entry.lean).
- [Classifier.Holds](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Catalogue/Holds.lean).

# Implementation and issue references

- [Project constitution](../.specify/memory/constitution.md)
- [Current Spec Kit artifact index](001-categorical-research-language/plan.md)
- [Current architectural decision and status of superseded proposals](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6708266418)
- [Consolidated implementation plan](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6664354269)
- [Actual selected-data and independent-source contract](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664276482)
- [Architecture, ownership and evidence](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574949858)
