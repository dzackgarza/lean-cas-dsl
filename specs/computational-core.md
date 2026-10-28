# Computational core: Lean-owned semantics over untrusted realization engines

**Status.** Requirements specification under [architecture.md](architecture.md), which controls where they differ; recorded 2026-09-28 from the owner's directive
of that date. It extends [#53](https://github.com/dzackgarza/lean-categories/issues/53)
(functorial method resolution) and
[#54](https://github.com/dzackgarza/lean-categories/issues/54) (typed constructors and
family applications). Neither issue is reopened or superseded: #53 fixes *what a method
is*, #54 fixes *how category-valued constructions are typed*, and this
document fixes *how data moves*, *what a backend leaf may contribute*, and *what the Lean
side must own so that a badly written backend cannot deform the public mathematics*.
The execution order is in [computational-core-plan.md](computational-core-plan.md); the
mathematical denotations remain in [FOUNDATIONS.md Part IX](https://github.com/dzackgarza/lean-categories/blob/main/FOUNDATIONS.md#part-ix-mathematical-semantics-of-the-computational-language).

**Grounding.** [`INTENT.md`](../INTENT.md) governs this document. `dzackgarza/sage-categories`
is a record of lessons, not a requirements source. Its implementation is not reproduced, and
neither is its leaf model, in which leaves declare functors and categories. Section 3 maps its
responsibilities to their replacements here; section 9 records what it discovered the hard
way.

---

## 1. The two governing invariants

\[
\boxed{\text{Lean owns every user-visible mathematical object, functor, operation and structural route.}}
\]

\[
\boxed{\text{Sage, GAP, Julia, OSCAR, FLINT, … are opaque engines behind typed contracts owned in Lean; a leaf ships no Lean.}}
\]

Consequence: a backend leaf can be architecturally wrong — invent its own notion of
subgroup, put isotropic operations on generic groups, expose a second `Aut`, forget an
inclusion, short-circuit lattices directly to sets — and none of it reaches the user.

**Scope of the guarantee.** "Backend mistakes do not matter" covers *ontology, placement
and wiring* mistakes only. A backend that returns a false group order still produces a false
answer. A CAS proves nothing. The permanent acceptance suite is the only evidence about a
computation, and no result carries a proof, certificate or trust status.

The target stack:

```text
mathematician-facing Sage-like DSL                       (lean-cas-dsl surface)
        │  elaboration
        ▼
one coherent semantic category/functor calculus in Lean  (lean-categories)
        │  typed request and result forms, owned upstream (leaves register, ship no Lean)
        ▼
arbitrarily messy Sage / GAP / Julia / OSCAR code         (backends)
```

The upper layers protect the user from the bottom one.

---

## 2. The central semantic claim: `x.f` is `f(F(x))`

For a receiver \(x\in\mathcal C\), a selected structural functor
\(F:\mathcal C\to\mathcal D\), and an operation \(m\) whose declared domain contains
\(F(x)\), method application uses that selected image. When \(m\) is a construction
functor \(\mathcal D\to\mathcal E\), this is the composite below; an invariant instead
has its declared core as domain, and an operation on arrows, elements or dependent data
uses that actual domain with its hypotheses (#53 §5; CC-CLOSURE).

\[
\boxed{x.m \;\leadsto_{\text{elaboration}}\; m\bigl(F_n(\cdots F_1(x)\cdots)\bigr)}
\]

A successful realization supplies the data of each required action, or an adequate fused
realization of the selected composite. Mathematical availability is independent of whether
those computations are installed (CC-ACTION, §7). `L.cardinality()` for a lattice elaborates to

\[
L\;\mapsto\;U_{\mathrm{form}}(L)\;\mapsto\;U_{\mathrm{mod}}(L)\;\mapsto\;U_{\mathrm{set}}(L)\;\mapsto\;\operatorname{card}(\cdot).
\]

Two operations are hidden inside `sage-categories`' dynamic inheritance:

1. **compute \(F(x)\)** — necessary, and kept;
2. **erase the distinction** by grafting \(F(x)\)'s implementation state onto \(x\) so
   that Python dispatch behaves as though the user had written `F(x).f()` — unnecessary,
   and not reproduced.

Lean keeps \(F(x)\) as an explicit typed term. It does not mutate a receiver's type, does
not initialize \(\mathcal D\)-state on \(x\), and does not choose an implementation by
method-resolution order.

---

## 3. Responsibility map from `sage-categories`

`sage-categories/specs/system.md` has five layers: Cat mathematics, `cat_kernel`
interpretation, runtime kernel, leaf, engine. In Lean the first two remain, most of the
third disappears, and the last two become a hard, typed boundary.

| `sage-categories` responsibility | Where it lives there | Lean replacement |
|---|---|---|
| Controlled C3 method order | `resolution.md` "Direct inherited execution" | unnecessary; no MRO exists |
| Dynamic role-class construction | kernel compiler | unnecessary |
| Initializer threading along the implementation DAG | `resolution.md` | unnecessary |
| Target-state grafting (`F.on_object` feeds \(\mathcal D\)'s initializer on the source value) | `functor.md` "Functor actions are concrete constructors", D13 | explicit \(F(X)\) term (CC-TRANSPORT) |
| Runtime placement / refinement after construction | `property-refinement.md` | semantic typing by the catalogue's theorems (CC-PROP) |
| Construction provenance recovery (`_object_inputs`, `_objects_by_datum`) | `resolution.md` "Construction retention" | the formal construction specifies its meaning; its selected computational realization retains the actual apex, defining maps and dependent data (CC-UNIV, CC-MEMO) |
| Selected structure-functor inheritance | `functor.md` | elaborator composes `FunctorExpr` (CC-RESOLVE) |
| `FunctorImageCache` | kernel | explicit-application memo table (CC-MEMO) |
| Property subcategories and their inclusions | `cat_kernel` | typed classifier/refinement expressions (#54, CC-PROP) |
| Semantic collision check (same public name, unrelated owners) | `resolution.md` "Semantic collisions" | registry duplicate/ambiguity errors at elaboration (CC-RESOLVE) |
| Diamond handling by declaration order plus executable comparisons | `resolution.md` "Diamond diagnostics" | explicit `NatTransExpr` comparisons; ambiguity is an error (CC-COHERE) |
| Universal constructions with retained apex, legs, mediator | `functor.md` "Diagram shapes and universal constructions" | Mathlib/project constructions returning complete universal data (CC-UNIV) |
| Engine lowering and native reconstruction | `leaves.md` "Computation-engine boundary" | still required: a leaf computes on a declared input form, and the kernel reads its answer into the declared result form (CC-ADAPTER, CC-DECODE) |

What is retained from `sage-categories` is its *requirements*: explicit object and
morphism actions, retained defining maps, comparison cells instead of priorities,
properties outside leaf control, and the separation between formally established laws
and empirical checking of untrusted computations (CC-LAWS).

---

## 4. Requirements

Each requirement has a stable identifier. The plan's nodes cite these identifiers; a node
closes only when every cited requirement's acceptance holds.

### CC-TRUE — Every semantic notion is standard mathematics, from step 0

No registry notion, data structure or resolver concept may stand in for mathematics that
the literature already names. Before a mechanism is built, its mathematical denotation is
stated with a source (a definition in FOUNDATIONS with a citation, or a Mathlib
declaration). An indexed family is legitimate mathematical data; its additional transport
and coherence must be stated when claimed (CC-FIB). Vocabulary such as "profile", "parent
edge", "method host" or "capability" may name an *encoding*, and every such encoding states
what it denotes. Where no precise denotation can be stated, the mechanism is not built.

This applies with full force to the first work: CC-FIB is the first instance, and the
existing registry's `CategoryFamilyEntry` is its first audit target.

**Acceptance.** Each semantic entry kind and constructor identifies its accepted
mathematical construction, actual domain, parameters, defining maps and required laws
or coherence, with a FOUNDATIONS anchor or library declaration. The encoding preserves
those data and the claimed operations on them; a docstring alone does not establish
that correspondence. The existing denotation audit records the declarations, the
consumer obligations and any precise missing input.

### CC-REUSE — Every obligation is first discharged by search; only glue and residue are written

Every definition *and every proof obligation* — a category, a functor, a fibration, a
coherence law, a lemma needed inside a proof — is first attempted through **broad searches
of the formalization-corpus API** (`scripts/formalization_corpus.py`, whose OpenAPI
document is served by `formalization-corpus.dzackgarza.com`), under several formulations:
the mathematical name, synonyms and dual notions, the Mathlib-style identifier, and the
statement's key lemma names, across the whole corpus (Mathlib, Lean 4 category-theory
libraries such as the ∞-cosmos project and `sinhp`'s fibred categories, UniMath, 1Lab,
agda-categories, the Isabelle AFP, and the rest of the index). A Lean hit is imported or
ported with provenance; a non-Lean hit is a reference implementation to follow.

Searches follow the kind of obligation. Mathematical definitions and proofs retain the
formalization-corpus search and the existing rules for semantic ownership. Runtime
representations, interpreters, codecs, caches, engine interfaces and related implementation
work also search relevant software libraries and reference implementations. Use package
indexes such as Reservoir for discovery and inspect actual source; relevant CAS designs
include CAP/homalg, Catlab/GATlab, Sage categories, Aldor/FriCAS and MitM/MMT, with prover-side
CAS interfaces where the boundary is the obligation. This is a source-appropriate search,
not a requirement to query every named project for every change.

The existing work record identifies the inspected source/revision, the specific responsibility
it supplies, and whether it is imported, ported/adapted or rejected, with compatibility and
boundary reasons. An unavailable index or unsuccessful query is not evidence that no
implementation exists. A software reference does not determine mathematical meaning, the
trust boundary or acceptance. Current program/lifecycle work has already selected the
sources in `cc-realize-2cat`: the existing selected-plan owner, a bounded adaptation of
PolyFun's suspension/return transitions, CAP's supplied-construction discipline, and no new
external evaluator dependency. `cc-dsl-language` selects the existing Lean APIs for #66.
Implement those decisions and establish actual compatibility; the archived #79/#80 surveys
do not assign another source-selection task. No new index service, per-type gate or bulk
retrospective rewrite is a prerequisite.

Only the **glue** between found results, and the **residue** that no indexed source
supplies, is written by hand. The searches, their hits, and the reason each hit does or
does not discharge the obligation are recorded with the work (in the commit and in the
owning spec or audit), so the residue claim can be checked.

This extends AGENTS.md's reuse gate from Definitions-sweep units to every obligation this
programme creates, including those that arise in the middle of a proof.

**Acceptance.** Every commit that adds a definition or a nontrivial proof under this
programme cites its search record; a reviewer can rerun the queries.

### CC-HIGHER — Retain the coherence required by the construction

The mathematical ambient is the model-independent higher-categorical setting of
[FOUNDATIONS §§1–2](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L57-L86), consistent with
[the inherited higher-invertibility requirement](https://github.com/dzackgarza/sage-categories/blob/37ec1642fe19f24fb00f402fe45350341ebf6920/DECISIONS.md#L96-L102).
Ordinary categories, functors and natural transformations form a supported fragment;
they do not impose a dimension-two ceiling.

For every construction claimed as supported, identify its full diagram, comparison-cell
boundaries and higher compatibilities required for composition, substitution, transport
and its universal property. Retain that coherent extension in every dimension the
construction needs. Invertibility supplies inverses to existing cells; it does not provide
missing comparisons, identify arbitrary parallel cells or establish all higher coherence
from pairwise comparisons. A boundary and its coherent extension are different mathematical
data ([FOUNDATIONS §§9–10](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L622-L684)).

Use the identities, compositions, whiskerings and compatibility supplied by the accepted
mathematical presentation. A formal generator, its mathematical interpretation and a
computation of its components remain distinct obligations. Mathematical declarations and
their validity belong upstream; an external computation cannot create a comparison or
supply trusted evidence of its laws.

A strict or truncated presentation may realize the intended construction only with the
appropriate adequacy/comparison argument. In particular, a strict categorical pullback can
exist without an isofibration hypothesis, while using it for the invariant homotopy
pullback of [Remark 7.4](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L502-L504) needs the required comparison theorem.
A missing required higher declaration or realization remains an explicit, owned gap; it is
not discharged by a lower-dimensional library or an engine's claim.

Chosen adjunctions are a concrete instance. Retain the selected unit, counit and the
coherence required by the specified category or space of adjunction structures. Even for
ordinary rational vector spaces, `Id ⊣ Id` admits unit `a · id` and counit `a⁻¹ · id`
for each nonzero rational `a`: the triangle identities hold, but the strict unit/counit
data differ. An appropriate uniqueness or contractibility theorem does not license literal
substitution of those data without its specified comparison. Distinguish the category of
adjunctions, the fibre over a fixed ordered pair of functors, and the space of right adjoints
to one left adjoint ([FOUNDATIONS adjunction addendum](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L8411-L8527));
the ordinary Mathlib structure is a supported fragment, not a general higher replacement.

**Acceptance and ownership.** #82 states the construction-specific higher scope; #66
(KM2/KM3/KM8) preserves its complete selected question; #69 (KM4–KM7) consumes the declared
actions and construction data; #24 (KM9) independently checks the promised mechanisms.
#23 identifies the required higher/coherent constructions in consumer mathematics.
For each claimed construction, identify its accepted source, actual consumer and full
boundary/extension, or its precise missing input. Existing ordinary constructions remain
valid in their justified fragment. This does not demand unrelated completion of all higher
category theory, or change the fixed V1 questions to fit an implementation.

### CC-CALC — The semantic calculus denotes the declared mathematical constructions

The catalogue supplies categories, functors with their object and morphism actions and
laws, natural transformations and the comparison/coherence data required by CC-HIGHER.
An indexed category with claimed change of base supplies its variance and transport
(CC-FIB). Composition uses the actual common category and selected parameters.

The required constructions include categories of elements, slices and coslices, arrow
categories, cores, discrete and diagram categories, subobjects, property subcategories,
and the products, pullbacks, kernels, cokernels and images used by the surface. Each has
its actual domain and hypotheses. Distinguish a subobject class from its chosen
monomorphism representative (CC-UNIV), and a construction from the defining maps and
universal property it carries. An ordinary categorical presentation is used within its
justified fragment; it does not impose a ceiling on CC-HIGHER.

`CategoryExpr`, `FunctorExpr`, `NatTransExpr` and the catalogue entries encode these
declarations. The earlier missing-`constructor` observation was a historical implementation
gap, not a current source claim or the mathematical definition of completion.

**Acceptance.** For the claimed instances of `Elements(U)`, `Arr(C)`, `Core(C)`, `Slice(C,X)`
and `Sub(C,X)`, identify the accepted construction and check that the supplied objects,
morphisms, endpoints and defining maps have that meaning. Composition with a declared
functor must preserve them. The constructor encoding and its denotation implement that
obligation generically; adding an enum case or an isolated example alone does not discharge
it. No construction is restricted to a smaller domain merely because one realization or
ordinary library uses that fragment.

### CC-FIB — Indexed categories retain their specified variance and transport

The assignment \(R\mapsto R\text{-}\mathbf{Mod}\) is a mathematical indexed family.
An assignment of fibres alone does not specify transport between them. When change of
base is claimed, retain the corresponding functor or pseudofunctor, its variance and its
coherence; equivalently use the specified cartesian or cocartesian fibration. In the
ordinary module example:

- restriction of scalars gives \(\mathbf{Ring}^{\mathrm{op}}\to\mathbf{Cat}\), with
  \(\varphi^*:S\text{-}\mathbf{Mod}\to R\text{-}\mathbf{Mod}\) for \(\varphi:R\to S\).
  Its total category has objects \((R,M)\) and morphisms \((\varphi,f)\) with
  \(f:M\to\varphi^*N\) \(R\)-linear; its projection to rings is cartesian;
- extension of scalars gives the covariant pseudofunctor
  \(\varphi_!=S\otimes_R-\), with its composition comparisons, and a cocartesian
  projection. The adjunction \(\varphi_!\dashv\varphi^*\) identifies the two descriptions
  of semilinear maps and supplies the usual module bifibration. A particular use still
  selects restriction or extension and its actual data;
- left module objects \(\operatorname{LMod}_A(\mathcal V)\) and bimodule families require
  their stated monoidal/base hypotheses and the variance of the claimed transport.
  A notation with one or two parameters supplies none of those choices by itself.

The precise source for these variances and fibres is
[FOUNDATIONS §§83–84](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L5983-L6140), with the bimodule analogue in
[§86](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L6221-L6328). In particular, restriction is cartesian and extension is
cocartesian; the reversed “respectively” in Definition 13.2 is not the convention used here.

For the selected module projection \(p\), the fibre over \(R\) is
\(R\text{-}\mathbf{Mod}\), with inclusion \(\iota_R\) into the total category. Reindexing
along \(\varphi\) is its declared transport, not an inferred relationship between two
family applications. The underlying-set functor on the total category forgets to the
actual module carrier; its restriction is \(U\circ\iota_R\).

Different projections of a structured object have different fibres and variances. For
fixed commutative \(R\) and value module \(W\), a form on \(N\) pulls back along a
carrier map \(f:M\to N\) by \(b\mapsto b\circ(f\otimes f)\). Change of values along
\(u:W\to W'\) is instead postcomposition \(b\mapsto u\circ b\). The cocartesian tower
in [FOUNDATIONS Example 31.2c](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L2722-L2739) projects a form to its **value** module
\((R,W)\); it is not the carrier-forgetting functor to \((R,M)\). Its base change uses
the hypotheses and coherence of [§15](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L1209-L1323). A lattice classifier or other
property refinement does not automatically inherit transport: closure under the
particular base change and its effect on the structure must be established upstream.

`CategoryFamilyEntry` and `CategoryExpr.familyApp` encode the declared indexed
construction. Where transport is claimed, the declaration names its fibration or
pseudofunctor and `familyApp` denotes the specified fibre. No change-of-base operation
may be manufactured from parameter syntax alone.

**Acceptance.** For \(\varphi:\mathbb Z\to\mathbb Z/4\) and a declared
\(\mathbb Z/4\)-module \(N\), restriction has the actual \(\mathbb Z\)-action
\(n\cdot x=\varphi(n)x\), with the same underlying set and additive group. The selected
reindexing and forgetful composites therefore give the same declared cardinality
invariant. Their realizations are checked against that independently fixed expectation.
Extension of scalars, a change of value module and a restriction of the form along a
carrier map remain distinct operations with their own parameters and comparisons.
The implementation must consume these declarations rather than choose a variance from
registry order or reuse an unrelated projection.

### CC-ACTION — A functor has declared actions and their required laws

A functor of the catalogue has object and morphism actions with the laws and coherent data
required by its mathematical ambient, all declared in `lean-categories`, never an enum tag.
The `lean-cas-dsl` enum

```lean
inductive ObjMap | cyclicToFiniteSet
```

is retired as a mechanism. Executing a functor on presented data is one more registered
operation: a leaf may realize it on a declared input form, and the kernel composes realized
steps along the resolved route. The kernel never takes a leaf's word for what a step means.

**Acceptance.** \(\operatorname{Lattices}\to\operatorname{FormedModules}\to\operatorname{Modules}\to\mathbf{Set}\)
is formed by ordinary composition in the catalogue; no lattice-to-set edge is registered; the
kernel's resolution of `cardinality` on a lattice is that composite, whichever leaves are
installed.

### CC-TRANSPORT — Data transport is the central resolver operation

Method inheritance means *construct the exact semantic receiver on which the operation is
defined*, never *search categories until a method name appears*. A resolution returns

\[
(F,\;F(X),\;m:\mathcal D\to\mathcal E)
\]

with \(F\) the selected structural composite. The displayed functor notation applies
when \(m\) has that domain; invariants and operations on arrows or dependent data use
their actual domains (CC-CLOSURE). Execution consumes the realized image and required
maps associated with this selection, not merely another object with the same expression.

**Acceptance.** For a lattice \(L\), `L.cardinality()` has the declared cardinality
invariant of its actual underlying set. The complete selected chain through formed
modules and modules is retained, and each realized action supplies the input consumed by
the next one, or an adequate fused realization supplies the same specified composite.
No parameter projection may silently replace that chain. Elaboration and retained-data
checks establish the association; the permanent assertion judges the computed answer.
This is the content implemented by a composite expression and its realization (#53 §13).

### CC-UNIFORM — Inclusions are functors like any other

Subcategory inclusions, classifier forgetful functors, fibre inclusions, projections
from Grothendieck constructions and other forgetful functors are all functors of the
declared calculus. Their meanings do not depend on separate "parent" and "functor"
dispatch mechanisms. Which of them supports an inherited application is the catalogue's
structural-admissibility decision (#53 §8), not a consequence of being a functor alone.

*Admissible structural functors* (the distinction recorded 2026-09-28): the catalogue
selects underlying-structure functors, subcategory inclusions and fibre inclusions for
inherited application. Being a functor alone does not make every operation on its target
an operation on the receiver. The projection \(\int\operatorname{Mod}\to\mathbf{Ring}\)
reads the scalar ring; the value projection \(\operatorname{Bil}\to\int\operatorname{Mod}\)
reads the value module. They are explicit parameter operations, not the structural
forgetful functors that supply a module's or formed module's carrier cardinality.
Base change, change of values and reindexing similarly use their specified additional
map and parameters. Their explicit application must not be inferred from target
reachability or used to choose a hidden structure.

**Acceptance.** Removing the special case "parents first, transport only on failure"
(`lean-cas-dsl` `Resolve.lean`, "NEVER A PREEMPTION") changes no resolution in the
existing test corpus except those that the old rule resolved by priority; each such case is
listed and either receives a declared comparison or becomes a reported ambiguity.

### CC-IMMEDIATE — A formalization declares its immediate structural functors

A new category is formalized in `lean-categories` with its actual objects, morphisms,
parameters and immediate underlying-structure functors. For example a declared lattice
category has a functor to the corresponding formed modules, with the actual underlying
module, form and morphism action. Where both categories have a selected base projection,
the functor has the required comparison over that base. A projection alone does not
assert that lattices form a fibration or are closed under arbitrary base change (CC-FIB).

Composites to modules and underlying sets are derived from these declarations. Operations
on those images are available on their actual domains; returning a structured kernel,
subobject or quotient requires the further declared hypotheses and lifting data of
CC-LIFT and CC-CLOSURE. A useful name is not itself a new mathematical owner, and no leaf
declares any of this mathematics.

**Acceptance.** For a newly admitted category, the derived structural composite and its
actions agree with the declared immediate functors, retaining the selected parameters
and comparisons. A redundant primitive declaration of the *same intended structural
functor*, with no new mathematical content, is rejected with its existing composite.
Reachability of a target alone does not prove two functors are the same: distinct
structures remain distinct and competing interpretations are ambiguous under CC-COHERE.
An operation remains owned at its declared generating level (#53 §5).

### CC-SEP — Semantic object, presentation form, fact, implementation are four things

A backend object conflates (1) what mathematical object it is, (2) how the backend
represents it, (3) which facts are known about it, (4) which algorithms work on it. The
system keeps them apart, and gives the leaf only (4):

```text
SemanticObject      -- a point of a registered category (lean-categories)
PresentationForm X  -- a typed request/result form and what it denotes (lean-categories)
Fact X P            -- a theorem of lean-categories; nothing else is a fact
Implementation op   -- a leaf's opaque computation from a declared input form to the
                       operation's declared result form
```

A computed answer, including a computed decision, is not a fact: its only evidence is the
permanent acceptance suite. A backend object is never the authority for category membership,
and no leaf supplies a denotation, a proof, an identification or evidence.

**Acceptance.** No code path assigns a category to a value by inspecting its backend
representation, and no leaf-supplied datum decides a value's meaning. (`lean-cas-dsl`'s
`profileFrom rules o` is the counterexample this acceptance excludes.)

### CC-CARRIER — A property does not supply a carrier

Knowing \(R\in\operatorname{Rings}.\mathrm{Finite}\) says nothing about what set the set
operations consume. Inheriting set operations requires a functor
\(U:\mathbf{Ring}\to\mathbf{Set}\) and its object action \(U(R)\) = *this* ring's chosen
carrier.

- \(\mathbb F_2\) presented on residues \(\{0,1\}\): \(U\) returns that set, and the map is
  explicit.
- \(\mathbb F_{p^n}\) presented as \(\mathbb F_p[x]/(f)\): \(U\) returns the residue classes
  of that presentation.
- Two presentations of isomorphic fields give different concrete carriers. A comparison
  between them is additional mathematics, formalized in `lean-categories`: never a silent
  identification by backend identity, and never an isomorphism a leaf asserts.

**Acceptance.** The two defining presentations
\(K_1=\mathbb F_3[x]/(x^2+1)\) and
\(K_2=\mathbb F_3[y]/(y^2+y+2)\) are retained as distinct presentations of a field
isomorphic to \(\mathbb F_9\). A comparison uses its declared mathematical relation;
isomorphism of fields does not by itself identify chosen carrier elements or
presentations. Conversely, differing presentation data is not a proof that their fields
are nonisomorphic. A selected admitted isomorphism transports actual elements, and a
missing required comparison is reported as missing rather than replaced by a backend
identity or a guessed answer. The existing historical correction remains: over
\(\mathbb F_2\), \(x^2+x+1\) is the only monic irreducible quadratic.

### CC-MEMO — Retain selected results; memoize only under justified reuse semantics

A formal application \(F(X)\) or \(F(f)\) does not establish purity or determinism of an
opaque computation intended to realize it. Distinguish the actual selected result from a
lookup that makes that result easier to find, and from a fresh execution of the same request.

Retained construction data includes its actual supplied apex, defining maps, chosen
presentation, selected comparisons, input/result association and required owner/session.
These are not disposable while subsequent mathematics refers to that result. A lookup may
be discarded only while the required data and associations remain available through their
authoritative owner; an expression key is not a replacement for them. This preserves
explicit applications without reviving target-state grafting.

A fixed operation and selected input keep their declared mathematical answer and relation
of comparison. They cannot be reinterpreted as an arbitrary choice because a backend varies.
Where the operation itself permits a choice in a specified fibre, distinct fresh executions
may select different allowed data; once one result is selected, subsequent use keeps that
choice and its maps. Where the operation fixes that choice, a different answer is a potential
wrong answer, not another meaning of the request.

Memoization of a specified pure computation may be an optimization with the same result in
the declared comparison relation. There is no blanket guarantee that cached and fresh opaque
executions return identical data. Each answer remains subject to the independent fixed
expectation; agreement between two executions is not evidence of correctness by itself.

Loss of a retained result or its required session is reported through the existing lifetime
and failure behavior. An explicit replay is a new execution occurrence. It cannot silently
replace the selected data or attach its newly chosen basis/apex to old defining maps. Any
reuse across a newly produced presentation requires the declared comparison and the actual
transport it requires, or is unavailable.

**Acceptance.** Existing cache/session/replay controls distinguish retained use, fresh
execution and replay. Disabling disposable lookup preserves actual selected data and its
owner/map associations. A pure computation's cached and uncached answers satisfy its
specified comparison; fresh opaque answers are judged separately against the same admitted
mathematical expectation, including any choice relation it actually specifies. No equality
of packets or agreement between executions substitutes for that expectation.

### CC-RESOLVE — Composite resolution with provenance and ambiguity

Resolution of `receiver.method(args)` follows #53 §8 steps 1–10. In addition:

- the result retains the full selected structural composite and its comparison data;
  normalization may not discard a selected structure, comparison or required higher cell;
- two competing composites to the same method source are reconciled only by the declared
  comparison with the strength and direction the operation requires (CC-COHERE); otherwise
  the call is **ambiguous** and elaboration reports both;
- no shortest-path rule, declaration order, typeclass priority or "first found" rule
  selects a route. (`lean-cas-dsl`'s `parentClosure` keeps "a shortest [chain]" and
  "diamonds collapse to a single entry"; both are excluded.)
- the base object is part of identity: the fibre over \(R\) and the fibre over \(S\) are
  different categories; change of base is the fibration's reindexing along
  \(\varphi:R\to S\) (CC-FIB), never a parameter carried unchanged along a name edge.

**Acceptance.** The ring diamond: \(\mathbf{Ring}\to\mathbf{AddCommMon}\) and
\(\mathbf{Ring}\to\mathbf{Mon}_\times\) remain distinct for `is_commutative` and are
identified at \(\mathbf{Set}\) for `cardinality` by a registered comparison (#53 §9, §12).

### CC-COHERE — Selected comparisons act on data; declaration order supplies no coherence

For declared \(F,G:\mathcal C\to\mathcal D\), a natural transformation
\(\alpha:F\Rightarrow G\) supplies components \(\alpha_x:F(x)\to G(x)\) and
naturality. It gives a directed comparison, not in general an identification or an
inverse. Reversible transport requires the stated natural isomorphism or equivalence;
equality and higher comparisons retain their own declared meaning and compatibility
(CC-HIGHER). Distinct intended structures remain distinct. No route-order rule provides
any of these data.

For example, an ordinary generalized point \(p:S\to F(x)\) transports to
\(\alpha_x\circ p:S\to G(x)\). For \(f:x\to y\), naturality is the formal law
\(G(f)\circ\alpha_x=\alpha_y\circ F(f)\). The accepted declaration owns that law;
a realization must compute the selected component and use the actual resulting data.
Recording the comparison's name does not perform its action, and observing a few
commuting squares does not establish the formal naturality theorem.

The historical `sage-categories` requirement for retained executable invertible
comparisons is preserved; its declaration-order fallback is excluded.

**Acceptance.** Competing structural interpretations without the needed comparison are
reported as ambiguous. With a selected comparison, a nonidentity component acts in the
declared direction on actual supplied data, with the specified source and target; its
result is then consumed through the unchanged public interface. Check that next
mathematical observation against the independent fixed expectation. A reverse use
requires an admitted inverse, and a distinct selected comparison may not be replaced by
the first registered one. Source/constructor checks establish preservation of the
selected data and required coherence, rather than treating a provenance label as success.

### CC-PROP — Properties live in Lean; backends only compute them

`Finite`, `Commutative`, `Free`, `PID`, `Nondegenerate`, … are semantic classifiers owned at
their correct level in `lean-categories`. A backend may compute whether a presented object has a
property. Its answer is a computation, evidenced only by acceptance. It cannot redefine what
the property means, supply evidence, or place an object in a property category.

This extends `lean-cas-dsl`'s existing distinction
*semantic availability ≠ implementation availability* from methods to all properties.

**Acceptance.** A backend computation of `IsAbelian` registers against the classifier
(commutativity of the multiplicative port, #53 §12); a backend "abelian group" category is not
expressible.

### CC-DECIDE — Three-valued decisions, and a wrong `false` is the worst error

A computed decision is *true*, *false*, or *undecided*. Undecided is absence of a decision
procedure, not a third truth value (FOUNDATIONS Def. 46.4). A backend that cannot decide must
return undecided; it must never collapse a conjunction of undecided components to `false`.
A decision is a computation like any other: it carries no evidence, and acceptance judges it.

`sage-categories` exhibits exactly this failure: at `39be374` its limit-category morphism
equality returns `False` for two equal homomorphisms \(\mathbb Z/2\to\mathbb Z/4/\langle 2g\rangle\)
whose every component comparison is undecided (recorded in that repository's
`COMPLAINTS.md`, "Limit-category morphism equality decides False for equal abelian
homomorphisms").

**Acceptance.** The decision result type distinguishes the three outcomes; an acceptance
assertion with pointwise-equal but differently constructed morphisms is never answered `false`.

### CC-UNIV — A construction retains its chosen objects, defining maps and universal data

The mathematics distinguishes a subobject class from a chosen representative
\(i:H\hookrightarrow G\). In the ordinary setting `MonoOver G` retains that
monomorphism, whereas `Subobject G` is its quotient by isomorphisms; extracting a
representative requires a choice. They are related constructions, not interchangeable
records ([Mathlib `MonoOver`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/CategoryTheory/Subobject/MonoOver.lean#L17-L31),
[`Subobject`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/CategoryTheory/Subobject/Basic.lean#L17-L41)). A subgroup realization keeps the
selected representative and its actual inclusion whenever subsequent mathematics uses
them. Passing to a subobject class cannot justify silently replacing its chosen apex.

For \(f:X\to Y\) in an ordinary category with the required zero morphisms and kernel,
the selected construction includes \(i:K\to X\), \(f\circ i=0\), and the universal
factorization of every \(k:W\to X\) with \(f\circ k=0\)
([Mathlib `kernel.ι`, `kernel.lift`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean#L13-L21)).
For a diagram \(D:J\to\mathcal C\), a chosen limit retains its apex \(L\), cone
\(\pi_j:L\to D(j)\) with naturality, and the universal mediating construction;
the diagram need not be finite ([Mathlib `Cone`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/CategoryTheory/Limits/Cones.lean#L106-L120)).
Quotients likewise retain their selected projection and factorization on the declared
domain, including the required congruence or normality hypotheses. The corresponding
higher universal properties keep the comparison and coherence required by CC-HIGHER.

These formal constructions and their laws belong to `lean-categories`. Their result
presentation interfaces specify the actual computational apex, defining maps,
parameters and dependent data to retain, together with the declared operations that use
the universal property. A leaf answer is an untrusted candidate for that realization;
decoding it does not prove the universal property or establish an identification with
the specified formal result. Missing computational defining data is a malformed answer,
not an invalid mathematical question. A missing realization of a required mediator or
next operation is a computational gap, not permission to weaken the construction.

**Acceptance.** For the independently specified subgroup construction
\(H\le O(L)\), consume the actual supplied inclusion in a subsequent subgroup action,
inverse image, restriction or other already-declared operation, through the public
subgroup interface. Compare that mathematical observation with the fixed expectation.
The source leaf's private class must not determine the subgroup's meaning or require
target-consumer wrappers. Reject a response missing the required inclusion; detect an
incorrect but well-formed inclusion through the independent assertion. Preserve the
selected apex/map association throughout the use. No leaf response is installed as a
semantic subgroup, proof of monicity or proof of its advertised universal property.

### CC-ADAPTER — A leaf is a registration, not a module of mathematics

A leaf ships no Lean. It is a registration of:
- the operation, or composite of operations, it computes, named by its `lean-categories`
  identity;
- the input form it accepts, one of the presentation forms declared upstream for that
  operation;
- an opaque implementation, in any language, speaking the port protocol, whose answer is
  decoded into the operation's declared result form.

The registration has no field for anything else. So a leaf cannot express a category, method,
property, placement, forgetful route, coercion, natural transformation, denotation, proof,
identification, evidence or status: those moves are unrepresentable, not rejected. Python
cannot create a semantic method by exporting a function; Julia cannot create a category; GAP
cannot claim that a group-specific operation belongs to all groups.

**Acceptance.** The registration type has exactly the three fields above, and replacing every
installed leaf changes no meaning, type or available operation of the language.

### CC-DECODE — Decode the declared presentation without importing backend semantics

The selected mathematical operation fixes its result presentation interface and the
comparison by which its answer will be judged. A backend response supplies an operation
identifier and encoded data in that interface. The decoder checks the declared form and
its required components; it does not infer the result's meaning from a backend class or
promote a well-formed packet into a proof of the operation's answer.

For the declared kernel construction, the computational result must retain a candidate
apex and its defining inclusion with the actual endpoints and selected parameters
(CC-UNIV). A missing inclusion or incorrectly shaped field is a malformed computational
response. A correctly shaped but mathematically wrong inclusion remains a possible
wrong answer, judged by acceptance; decoding cannot assert monicity or the kernel
universal property on the leaf's authority. The same distinction applies to all
structured results and to maps supplied for later universal factorizations.

The bridge omits backend ontology while retaining the construction data that the
declared result interface and subsequent operations require.

**Acceptance.** The missing-defining-map control is rejected as malformed without
changing the admitted question. On the fixed small corpus, use each well-formed answer
in the declared mathematical comparison or subsequent map operation and check it
against the independently specified Lean-native result or other accepted expectation
(#53 §14 E). The comparison relation is explicit; packet equality and successful
decoding do not establish agreement. The wrong-but-well-formed control must fail its
mathematical assertion rather than be counted as malformed or as invalid mathematics.

### CC-ROUTE — Capabilities register against semantic operations, never backend methods

A backend says "I implement semantic operation \(m\) on input forms satisfying \(P\)",
keyed by a `FunctorId` or normalized `FunctorExpr` (#53 §10 `BackendRealizationEntry`). It
never says "I have a method called `.kernel()`". The backend's method inventory is discovery
input only. Several backend functions may realize one operation; one backend function may
serve several operations through adapters; duplicate or misplaced backend APIs are ignored.

**Acceptance.** Two backends realizing the same composite are two realizations of one
semantic operation; the method audit reports one owner.

### CC-LIFT — Returning to a structured category requires its declared lifting construction

For a selected structural functor \(U:\mathcal C\to\mathcal D\), applying an operation
to \(U(x)\) initially gives its result in that operation's actual codomain. A required
result in \(\mathcal C\) needs the declared additional structure, maps, compatibility
and hypotheses that construct it there. Preservation of a limit compares the image of
an already existing source limit; it does not alone construct a source object over
every target limit. Creation of a limit or an explicit lift supplies a stronger,
different obligation.

Use the particular mathematics: restriction of structure along a specified inclusion,
a cartesian or cocartesian lift over a specified base map, an equivalence and its
selected transport, a chosen adjunction, or the declared universal construction.
An isofibration lifts the relevant isomorphisms; it is not by that fact a supply of
cartesian lifts over arbitrary morphisms. Each use retains the comparison and coherence
its construction requires, instead of inferring a return path from common carrier
types or a reachable category name.

**Acceptance.** For the declared formed-module kernel question, retain the actual
module inclusion \(i:K\to M\) and restrict the selected form by
\(b_K(x,y)=b_M(i(x),i(y))\). The returned formed object and its inclusion have the
declared meaning on that question's domain. The restricted-form construction alone
does not prove that it is a categorical kernel in every category of form-preserving
maps: that stronger claim needs its actual zero morphisms and universal property.
Preserve the fixed question's meaning and identify its accepted declaration or the
precise missing input, rather than silently changing it. Any additional classifier
(for example nondegeneracy) requires its own closure hypothesis and cannot be inferred
from the bare restriction. The next operation uses this very \(K,i,b_K\), and its
realization is judged by the fixed independent expectation. If the required formal
lifting declaration is absent, record that precise upstream input gap; if its
realization is absent, report the computational gap. Neither returns a bare module as
though it satisfied the unchanged structured question.

### CC-CLOSURE — Available operations follow from their actual domains and selected structure

For \(X\in\mathcal C\), inherited application is derived through the catalogue's
admissible structural functors, with their selected parameters, comparisons and
hypotheses. Its mathematical domain is not merely a target category name:

- a set-valued invariant \(I:\mathcal D^{\simeq}\to S\) restricts along the functor
  on cores induced by \(F:\mathcal C\to\mathcal D\), on the stated classifier or
  domain of \(I\). Cardinality and rank are invariants on their natural domains, not
  generally functors from all morphisms of \(\mathcal D\) to a discrete set
  ([FOUNDATIONS Definition 46.2](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L3607-L3620));
- an operation on arrows consumes an actual arrow \(f:X\to Y\) through the induced
  arrow functor, with the hypotheses its construction needs. An underlying module
  functor alone does not make a kernel of every map into a structured kernel in
  \(\mathcal C\); returning there requires CC-LIFT;
- an operation on elements or dependent data consumes the selected underlying functor,
  elements, parameters and hypotheses of its declared source. Its result and subsequent
  applications keep those selections.

`#methods X`, documentation, completion and dot notation derive from that same
mathematical closure (#53 §8). Every subgroup receives the applicable generic subgroup
operations; specialization can supply additional structure and operations without
redeclaring the generic ones. Mathematical availability is independent of whether
their required realizations are installed.

**Acceptance.** Introduce the fixed independently authored category and its immediate
structural functor to the declared module category. Derive its underlying-set
cardinality invariant, and rank where its actual rank-domain hypotheses hold, through
the corresponding functors on cores. For a declared morphism, compute its underlying
module kernel; return the structured kernel only with the separately admitted lift
and its defining maps. The pre-existing target consumers remain unchanged, and the
fixed questions judge their realized answers. A missing lift, hypothesis or realization
is recorded at its proper boundary rather than manufacturing availability from
reachability. No receiver-specific mathematical wrapper or leaf declaration supplies
the inherited meaning.

### CC-LAWS — Formal constructions carry their laws; realizations are tested

Every mathematical structure admitted from `lean-categories` carries the formal laws and
coherent data required by its accepted definition: identity and composition preservation,
naturality, triangle or pentagon identities, and the higher compatibility required by the
particular construction. Required proof fields or coherence data cannot be replaced by a
promise to test examples. Missing formal mathematics remains an explicit upstream gap.

The kernel consumes those accepted declarations and preserves their selected data. Ordinary
Lean elaboration and proof checking remain required. It does not ask an opaque backend to
evaluate defining equations in order to establish or admit the formal mathematical structure.

A realization's answers remain untrusted computations. Their agreement with the specified
mathematics is judged by permanent independent acceptance; those observations neither create
formal laws nor prove arbitrary subsequent answers. The historical D26 prohibition on
repeated runtime admission checks is retained in this computational sense, not as an
exemption from the formal laws.

**Acceptance.** Identify the accepted upstream laws/coherent data for each claimed
construction. No leaf response or finite test substitutes for them, and semantic registration
does not depend on opaque engine law queries. Ordinary Lean proof checking is not such a
query. This adds no result certificate or trust status.

---

## 5. The leaf contract

A leaf holds zero semantic authority, and nothing from it is trusted (`INTENT.md`;
[architecture.md](architecture.md), "The evidence model: nothing from a leaf is trusted"). It contributes only an implementation of an already-declared
operation on an already-declared input form (CC-ADAPTER). It never contributes, by any route:
- a category, a method, a property, a subcategory or placement, a forgetful route or coercion;
- a natural transformation or an identification of two values;
- a denotation of its values, a proof or certificate about its own code, evidence for a
  decision, or a trust status for its answers;
- mathematics of any kind. New mathematics is formalization work in `lean-categories`, which a
  leaf author does not do as part of writing a leaf.

That leaves the backend free to be messy internally. Its answers may be wrong; acceptance finds
that out. A leaf is meant to be glue over a mature engine: declared input form, engine input, the
engine's routine, engine result, declared result form, with no hand-rolled algorithm, no kernel
machinery and engine values kept private ([`lean-cas-dsl-leaves` AGENTS.md](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/e2f8537/AGENTS.md), "A leaf is glue
over existing backends"). That is writing guidance for an engineering review, and following it
earns no trust.

---

## 6. Division of ownership between the two Lean repositories

[architecture.md](architecture.md) owns this division; the owner's direction of 2026-09-29
corrects the earlier text of this section.

- `lean-categories` owns all mathematics: categories, functors, fibrations, classifiers,
  operations (every method), coherences, typed constructors and families, and their theory
  (CC-TRUE's and CC-FIB's mathematical content, CC-LAWS). It also owns which of these are
  registered as the CAS's semantics, as a proof-carrying registry (lean-categories #49, #53).
  It holds no resolver, realization or backend code.
- `lean-cas-dsl` (this repository) derives the language from the pinned release (its catalogue):
  - the resolver and closure (CC-RESOLVE, CC-CLOSURE, CC-UNIFORM, CC-COHERE, CC-PROP);
  - the registry of leaf registrations (CC-SEP, CC-ROUTE, CC-MEMO);
  - the leaf API and the port protocol (CC-ADAPTER, CC-DECODE);
  - the surface syntax and elaborator;
  - the permanent acceptance suite.

  Backend programs are owned by their leaves.
- The symbolic semantic registry (the catalogue, `LeanCategories.Catalogue`) is `lean-categories`';
  this repository reads it at the pin and writes none (`cc-sem-upstream`, `cc-sem-derive`).

This follows #53 §7 ("no second semantic method registry"). The name-level graph
(`CatDecl`/`FunctorDecl`) was deleted (lean-cas-dsl `90608e6`, `a191b61`). All foundational mathematics lives in
`lean-categories`. The kernel owns the Lean of its own mechanics and no mathematics. Leaves own
no Lean at all.

---

## 7. Mathematical meaning and available realizations

A semantic object is a point of its registered category, with the meaning supplied by the
accepted upstream mathematics. Its existence, category membership and available mathematical
operations do not depend on installed computations.

- The semantics is `CategoryExpr`/`FunctorExpr` with accepted mathematical denotations in
  `lean-categories`.
- Each selected operation has declared input and result presentation interfaces and their
  denotations. Those interfaces do not narrow its mathematical domain to installed capabilities.
- A realization may compute that action on some admitted presentations. The kernel preserves
  its selected parameters, endpoints and required comparison data while executing it. An
  absent or unavailable realization is a computational gap, not an absent mathematical object.
- A successful computation supplies the data required by the selected result interface,
  including actual defining maps and retained construction data where required. Reusing an
  already adequate datum may satisfy this requirement; a fresh allocation or a nontrivial
  computation is not itself a mathematical requirement.
- A decoded, well-formed answer is not thereby proved correct. The permanent acceptance suite
  compares it with independently fixed expectations from proof, citation or an independent
  oracle, using the declared mathematical comparison.

This keeps #53 §6.1's goal (elaboration emits an ordinary Lean term for the meaning) while
execution runs through untrusted leaves. A question's meaning survives absent implementations;
its required computation remains an open obligation rather than a weakened question.

---

## 8. Nuances recorded from `sage-categories`

Each is a requirement discovered by failure there; ignore them and the Lean system will
rediscover them.

1. **A realization must implement the selected action.** An identity-shaped placeholder is
   defective when the selected action requires different target data (`POL-LEAF-070`).
   Identity actions and justified reuse of supplied target data remain legitimate.
2. **An accessor does not establish a functor.** A forgetful functor may implement its object
   action by reading retained underlying data. Its object action, morphism action and required
   laws must nevertheless be declared upstream; an accessor cannot introduce a second semantic
   meaning or substitute for those declarations (`POL-LEAF-078`).
3. **One fact, one spelling.** `POL-LEAF-079`: two declarations of one fact drift.
4. **A retained projection must not be rewritten** (`POL-LEAF-071`); universal data is
   retained, not recomputed.
5. **Declaration order is not coherence** (see CC-COHERE).
6. **Identity is not equality.** Retained identity (the same construction) and decided
   mathematical equality are different relations; caches key on identity; `=` elaborates to
   a proposition decided by `ask`-like procedures (#53 §1: no user-level `==`).
7. **A finite engine must not narrow a shared constructor's domain**
   (`computational-generality.md`): an engine that enumerates is one realization; the
   semantic construction keeps its infinite and nonenumerable domain.
8. **Formal constructions carry their laws; realizations are tested** (CC-LAWS, D26).
9. **Undecided is not false** (CC-DECIDE).
10. **Distinguish an object from an element of its underlying data.** A point of a category
    \(\mathcal C\) is an object \(X\in\mathcal C\) (FOUNDATIONS Definition 1.4). For an
    ordinary underlying-set functor \(U:\mathcal C\to\mathbf{Set}\), an element
    \(x\in U(X)\) gives the object \((X,x)\) of `Elements(U)`, the declared source for
    element methods (#53 §3). A generalized point \(S\to X\) is a morphism with that
    specified domain. Preserve the selected \(U\), object and parameters rather than
    conflating these levels; not every category has such an underlying-set functor.
11. **Backend category names do not determine module or algebra semantics.**
    [Sage 10.9's `Modules` source](https://github.com/sagemath/sage/blob/10.9/src/sage/categories/modules.py#L33-L109)
    documents the ordinary symmetric-module setting and warns that its meaning outside that
    context is unsettled. A `Bimodules(R,R)` supercategory entry is not an identification
    with all bimodules. Record each operation's actual domain, selected left/right actions,
    morphisms and symmetry assumptions, then match the independently accepted mathematics
    (#20/#22/#23). Over ℚ, the two unital rational actions are forced to agree, so the QQ
    fixture preserves parameters but does not distinguish rational bimodules from vector
    spaces. Use an actually nonsymmetric example for that distinction. Likewise classify
    `C.Algebras(R)` by its actual linearization/construction, not by silently identifying
    the name with internal algebra objects. Backend observations supply no semantic authority.
12. **Leaves pull generic mathematics in the wrong direction.** In the research repository a
    generic predicate-subgroup module imported from `orthogonal_quotients`. Under this
    architecture that import is ill-typed: the generic subgroup construction is owned above
    every leaf, and a leaf cannot be a dependency of it.

---

## 9. Open questions (do not reopen the governing decisions)

1. Which existing session or operation boundary owns required retained results, and which
   lookups are disposable under CC-MEMO? Their lifetimes must preserve selected data and
   dependent maps; a cache label does not settle that distinction.
2. How does `FunctorExpr` represent a fibration's reindexing \(\varphi^{*}\) and fibre
   inclusions \(\iota_R\): as constructors derived from a registered fibration entry, or as
   `atomic` functors whose registration must cite that fibration? Either way the
   fibration, not the pair of `familyApp` endpoints, is the owner.
3. #53 §16's ten questions remain open and are inherited unchanged.
4. For a particular property subcategory, does an accepted closure-under-subobjects theorem
   supply the structured-kernel lift and its comparison with the underlying kernel? For a
   category carrying additional chosen data, what further construction supplies that data on
   the kernel? CC-CLOSURE inherits the underlying operation only on its actual domain;
   CC-LIFT requires the actual structured return. A closure theorem for a property alone
   is not a general reconstruction of arbitrary extra structure.
