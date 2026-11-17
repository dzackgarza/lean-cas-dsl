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
public constructor of `D`. Writing `m_i` for public source operations and `Φ` for the leaf
algorithm, the object action has the form

$$
\widehat F(X)=\operatorname{Construct}_D(\Phi(m_1(X),\ldots,m_k(X))).
$$

The independently declared `F` determines the obligation that this algorithm must satisfy. Its arrow action similarly constructs an arrow in
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
records a selection and asserts no equality between routes. Definitional equality of the complete
dependent operation families can also establish agreement. Without a valid selection or the
required agreement, report ambiguity before execution. Provider availability, caches and successful
computations cannot settle that mathematical ambiguity.

## Properties, refinement and choice

For `p : E → C`, the classifier query is `Nonempty (p⁻¹(X))`, using the formal categorical
fiber. A refinement requires the declared rule and its evidence. For example, formal evidence
that an integer interval is finite can support its specified lift into finite sets, with the
prescribed identification of its underlying set. A backend's finite list is not that evidence.
A computational predicate reply remains a candidate answer; it is not a new Lean proof.

Concretely, let `X = {n : ℤ | 0 ≤ n ∧ n < 5}`, with its inclusion `j : X ↪ ℤ`.
For the forgetful functor `U : FiniteSets → Sets`, the declared finiteness refinement supplies
`X̃ : FiniteSets` and its specified identification `e : U(X̃) ≅ X`. Its inclusion into the
original ambient set is `j ∘ e`; refinement must preserve this relationship. When the formal
rule and evidence are available, the kernel applies that refinement to make the justified
interface available, without a backend-type classification step. This illustrative interval
is distinct from the upstream square-bound family linked below; it does not assert a particular
surface syntax or that this exact interval is currently executable.

The upstream `Finiteness.finiteHolds_iff` relates the classifier query to `Finite X`.
`IntegerSquareBounds` supplies a concrete family with `finiteExtent`, `finiteIdentification`
and its original integer inclusion. These declarations exemplify retaining the actual subset
and its map while adding the justified finite-set interface.

Existence of structure and selected structure differ. A proof of existence of a basis supplies
no chosen basis for a later coordinate computation. A computation that selects a basis must
retain that basis and its relation to the original object. The same rule applies to orientations,
enumerations, presentations and lifts. Several refinements may apply at once. The operation's
formal domain determines which evidence it needs; a unique most-specialized runtime class is
not assumed. If the required classifier or refinement theorem is absent upstream, downstream
code must expose that missing formal input rather than invent a classification rule.

## Selected constructions remain usable

For a selected limit of `D : J → C`, retain its cone, apex, legs and universal operation.
With apex `L`, its legs are `π_j : L → D(j)`. For `u : j → k`, they satisfy
`D(u) ∘ π_j = π_k`. Its universal property supplies the specified unique factor from each
cone. The formal construction fixes these laws; retaining unrelated arrows with the right
endpoints does not supply its cone or universal property.
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

The input is the original checked judgment `(Γ; S ⊢ t : A)`: `Γ` contains the mathematical
parameters and hypotheses, while `S` records the selected structures, functors and comparisons.
Interpretation determines the admissible composite, refinements and complete dependent request.
Realization invokes its public leaf operations. Continued use applies further categorical
operations to the actual result with those retained selections. The result remains a candidate
realization of this judgment; it does not become authority for a revised judgment. Initial, deferred and provider-requested public calls
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

## Reconstructed owner intent: constructors, functors and category-aligned computation

This section is **mathematical design input**, not a claim about the current executable kernel.
It reconstructs the original category-based implementation model directly stated by
the owner on November 17, 2026. The original chat is not an operative repository
dependency: [source passages in #91, record A](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942015918),
[complete independent reconstruction, record B](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942060158),
and the [current-source implementation map, record C](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942116552)
supply the relevant evidence, distinctions and exact owner statements. The
mathematical authority is still `lean-categories`; an example below is not a
new formal declaration or authorization to invent missing category theory.

### Constructors are themselves typed mathematical constructions

For a category `Y`, a family of admitted public constructors has, in the
owner's intended model, the shape

`C_i : D_i → Y`,

where `D_i` is a category of defining presentations or tuples, not a wire
schema. For a constructor defined only by an object assignment `c:I_i→Ob(Y)`,
the **minimal** well-defined constructor functor is
`Disc(I_i)→Y`: on each identity `id_i` it sends to `id_(c(i))`,
which respects the functor laws because the discrete source has no other
arrows. It is **not** necessary to invent nonidentity presentation maps for
every constructor. If a richer `D_i` is intended, its additional morphisms,
the constructor's action on them and the laws require actual upstream
mathematical declarations.

Do not conflate these object constructors with
`LeanCategories.Catalogue.Registry.ConstructorEntry`:
the latter defines **category-level** constructors such as `Arr(C)`;
its `functorialAction` maps a category functor `C→D` to an induced
functor `Arr(C)→Arr(D)`. That field is not evidence that an arbitrary
object-valued `C_i:D_i→Y` has been supplied. The exact mathematical
source and unresolved constructor declarations are recorded in
[#91 decision docket D2](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942323747).

A source category `X` has public mathematical observations `m_j`, each with
its genuine domain and codomain. Those codomains may involve the appropriate
mathematical categories associated with booleans, naturals, integers or tuple
presentations; this does not mean untyped wire tags. The computational
realization of an accepted functor `F : X → Y` can assemble its target defining
data from the source's public methods and apply a public target constructor:

`F(x) = C_i(Φ(m_1(x), …, m_k(x)))`.

The actual typed `F(f) : F(x) → F(x')` must likewise be realized through the
public target hom/morphism interface; merely implementing the object formula
does not make an arbitrary assignment functorial.

The **constructor-completeness invariant** is not a demand for eager algorithms:
every admissible public method on `Y` has its established mathematical
meaning for objects made by **any** `C_i`. A constructor may choose a private
representation or return `NoImplementation` for a demanded computation. It may
not give its products a different mathematical public API depending on their
source presentation. A selected mathematical basis, map, presentation or
comparison is retained, not discarded as a mere implementation detail.

For example, over a PID `R`, a finitely generated module can be constructed
from an `R`-action `R → End_Ab(A)`, or from a free rank and appropriate
invariant-factor data. These give objects in the same module category,
not automatically judgmentally equal objects. Both have the same meaningful
`action_morphism` and `invariant_factors` interfaces where those are
mathematically defined. A leaf may have no algorithm to extract invariant
factors from arbitrary action data; that is missing computation rather than a
different category or a missing mathematical method.

### A leaf is not a single capability registration

The owner's **category-aligned computational leaf** implements a category's
accepted constructors, common methods and the **computational actions of its
immediate formal functors**. Formal definitions, laws and proofs remain in
`lean-categories`; no leaf may invent them. The generic `lean-cas-dsl`
**kernel** enables category-to-category interoperability and is a prerequisite
to making these category-aligned implementations independent.

A leaf manifest entry `(operation, input form, backend)` advertises one
**computational port**. The port is not itself a mathematical category or the
entire category-aligned leaf. A package may expose many such ports; it must
fulfil the independently selected interfaces and cannot determine method
availability or mathematical ownership by registering them. In particular,
the existing three-field protocol need not be replaced to correct this
conceptual separation, but the actual grouping and constructor completeness
must be realized through the public contract.

Thus `x.P()` is not a leaf-defined forwarding method. For an accepted
structural `F : X → Y` and suitably typed and admissible method `P`,
the kernel resolves the mathematical composite

`(P ∘ F)(x) = P(F(x))`.

The `Y`-object can be constructed **on demand** through `C_i`. No runtime
hierarchy or translator between private `X` and `Y` representations creates
this relationship. Runtime references, scopes and operands can exist but do
not supply or reconstruct mathematical meaning. Not every functor makes every
operation inheritable; the exact formal domain, structural admissibility,
comparisons and selected choices control resolution. The current
`lean-categories` [`FunctorEntry.structural`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Catalogue/Registry/Entry.lean)
identifies underlying-object functors for **unqualified method inheritance**;
this is already an upstream formal rule, not a runtime engineering option.
Its agreement with the full original mathematical requirement must be
checked on actual examples, as specified in [#91 D3](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942323747).
An explicit mathematical composite `P(F(x))` is not the same question as
automatically exposing an unqualified `x.P()`. In particular an isofibration
does not, by itself, supply arbitrary limit or quotient lifting.

### Mathematically complete examples that determine implementation

**Free lattice cardinality.** Given an appropriate formal structural functor
from lattices to their underlying modules and sets, and the correctly typed
set-cardinality operation, `L.cardinality()` means the admitted composite
`card(U(L))`. If `L ≅ ℤ^n`, it has one element when `n=0`, and
countably infinitely many when `n≥1`: a nonzero finite product of countably
infinite sets is countable and contains a copy of `ℤ`. The kernel is not
authorized to compute this by a lattice-rank special case or an unpublished
Lean reduction. Existing applicable methods must reach a newly defined
lattice without a new lattice forwarding implementation.

**Enumeration of a presented lattice.** A selected surjection
`q : ℤ^n ↠ L` and a supplied enumeration `e_n : ℕ ↠ ℤ^n` construct
`q ∘ e_n : ℕ ↠ L`. Surjectivity follows directly by choosing a preimage
under each surjection. An object of the epi portion of the coslice
`ℕ ↓ Set` can therefore be constructed *as an object* through the public
enumerated-set constructor. There is a **separate formal morphism obligation**:
in the literal coslice, a morphism `(e : ℕ→S) → (e' : ℕ→T)` must satisfy
`f ∘ e = e'`. Arbitrary lattice homomorphisms do not necessarily give such
arrows (e.g. `-1 : ℤ→ℤ` cannot preserve a surjective fixed enumeration).
The exact source category and functor's arrow action are **not settled by the
owner transcript**. Moreover, the existing formal
[`EnumeratedSetCat`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Foundation/Sets.lean)
uses a selected `Encodable` structure with **all functions** as morphisms,
rather than a literal epi coslice with commuting-triangle morphisms. These are
non-equivalent definitions. Under the existing formal category ordinary lattice
maps have an underlying-arrow action, but converting a mere epi `ℕ↠L` into
a computationally effective `Encodable L` may require additional encoding
or search information. The exact mathematical target and arrow contract must
be **reconciled at the independent mathematical owner** before this proposed
new functor is admitted: [#91 decision docket D1](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942323747).
The response is *not* an ad-hoc backend reindexing or a “transport” between
serialized lattice vectors.

**Toric and formed integral lattices.** Chosen bases `m_i` of characters
and `n_i` of cocharacters, dual under evaluation, provide
`⟨m_i,n_j⟩ = δ_ij` and selected Euclidean forms
`b_M(m_i,m_j)=δ_ij`, `b_N(n_i,n_j)=δ_ij`.
The resulting formed integral lattices inherit their public general lattice
algorithms. For `v=Σ a_i m_i`, `b_M(v,v)=Σa_i²`; a norm bound
`≤R` bounds each `|a_i|` by `⌊√R⌋`. An independent toric engine with
its own public “lattice” and bespoke enumeration/short-vector functions is
the duplicated-ontology failure this project exists to avoid. The bases are
**chosen structure**, not a claim of a canonical basis-free Euclidean form.

**Refinement of a computed subset.** The original illustrative phrase
`{n∈ℤ | n<5}` is actually infinite (the injection `k↦4-k` from
`ℕ` proves this). The corrected bounded subset
`B={n∈ℤ | 0≤n<5}={0,1,2,3,4}` has a finiteness proof.
The *formal* classifier/refinement rule can produce a selected
`FiniteSets` lift with an identification of its underlying set with `B`
and retention of the original inclusion `B ↪ ℤ`. A backend array of five
elements is not the proof and may not change semantic placement. A proof of
existence of a basis or enumeration likewise does not select one.

**A selected limit's defining leg.** A selected limit is its actual diagram
`D:J→C`, cone, apex `L`, projections `π_j:L→D(j)` and universal
factorization. Its `leg(j)` is the corresponding projection of **that
cone**, not a reverse search of all cones whose apex happens to match.
Two selected limits may share an apex without having the same defining maps.
The subsequent operation must consume those actual maps and the selected
returned computational occurrence.

### What implementers must demonstrate, and what must not be inferred

A new contributor, using **only this checked mathematical source and the
repository**, must locate the owner category, its actual declared methods,
constructor data category, admitted functor and morphism action, and the
unchanged **later mathematical use**. If any mathematical category/action or
theorem is missing, the exact formal input is an upstream
`lean-categories` obligation; neither the core nor a leaf can silently
create an implementation-shaped mathematical replacement.

No private internal test may promote itself to independent acceptance.
In particular, successful transport of an opaque lift token through a test
peer is a useful structural probe but does **not** establish the original
lift's map/comparison/factorization equations. Those independently required
assertions must run through the connected public kernel and adequate actual
computational implementations.

Before refactoring a historical source path, inspect the current integration
revision. The Nov 17 source audit documents that some historical
reconstruction functions have already been removed and the reader/kernel
have been split; [record C](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942116552)
gives their exact inspected replacements. Removing a nonexistent function or
mechanically repeating a past file split is not remediation. The only
committed work order remains [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10):
T016/#84 was recorded complete on November 17 in
[#84](https://github.com/dzackgarza/lean-cas-dsl/issues/84)
(with its own measured evidence). The current task is the **first unfinished**
entry of the [fixed #10 queue](https://github.com/dzackgarza/lean-cas-dsl/issues/10),
not a permanent re-run of T016. The precise evidence and later acceptance
belong to the same existing owner issues.


## Owning sources

- [Independent mathematical API and ownership](https://github.com/dzackgarza/lean-categories/blob/main/INTENT.md).
- [Functor target construction](https://github.com/dzackgarza/sage-categories/blob/main/specs/functor.md#functor-actions-are-concrete-constructors) and [public category interfaces](https://github.com/dzackgarza/sage-categories/blob/main/specs/leaves.md). These supply the constructor-composition principle; their Python class and trust conventions do not replace this repository's independent Lean authority or acceptance rules.
- [Formal method domains](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Catalogue/Registry/Entry.lean).
- [Classifier.Holds](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Catalogue/Holds.lean).
- [Finiteness and the classifier fiber](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Catalogue/Semantics/Foundation/Finiteness.lean).
- [Square-bound refinement with its original inclusion](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Catalogue/Semantics/Foundation/IntegerSquareBounds.lean).

# Implementation and issue references

- [Project constitution](../.specify/memory/constitution.md)
- [Current Spec Kit artifact index](001-categorical-research-language/plan.md)
- [Current architectural decision and status of superseded proposals](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6708266418)
- [Consolidated implementation plan](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6664354269)
- [Actual selected-data and independent-source contract](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664276482)
- [Architecture, ownership and evidence](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574949858)
