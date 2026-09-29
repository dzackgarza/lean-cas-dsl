# Computational core: Lean-owned semantics over untrusted realization engines

**Status.** Requirements specification, recorded 2026-09-28 from the owner's directive
of that date. It extends [#53](https://github.com/dzackgarza/lean-categories/issues/53)
(functorial method resolution) and
[#54](https://github.com/dzackgarza/lean-categories/issues/54) (typed constructors and
family applications). Neither issue is reopened or superseded: #53 fixes *what a method
is*, #54 fixes *how category-valued constructions are typed*, and this
document fixes *how data moves*, *what a backend leaf may contribute*, and *what the Lean
side must own so that a badly written backend cannot deform the public mathematics*.
The execution order is in [computational-core-plan.md](computational-core-plan.md); the
mathematical denotations remain in [FOUNDATIONS.md Part IX](https://github.com/dzackgarza/lean-categories/blob/main/FOUNDATIONS.md#part-ix-mathematical-semantics-of-the-computational-language).

**Reference implementation.** `dzackgarza/sage-categories` implements most of the
required semantics in Python and is the requirements source for this work. Its
implementation is *not* to be reproduced. Section 3 maps each of its responsibilities to
its replacement here; section 9 records what that repository discovered the hard way.

---

## 1. The two governing invariants

\[
\boxed{\text{Lean owns every user-visible mathematical object, functor, operation and structural route.}}
\]

\[
\boxed{\text{Sage, GAP, Julia, OSCAR, FLINT, … are realization engines behind typed Lean adapters.}}
\]

Consequence: a backend leaf can be architecturally wrong — invent its own notion of
subgroup, put isotropic operations on generic groups, expose a second `Aut`, forget an
inclusion, short-circuit lattices directly to sets — and none of it reaches the user.

**Scope of the guarantee.** "Backend mistakes do not matter" covers *ontology, placement
and wiring* mistakes only. A backend that returns a false group order with no certificate
or checker still produces a false answer. That residual trust is recorded per call
(requirement CC-TRUST), never hidden.

The target stack:

```text
mathematician-facing Sage-like DSL                       (lean-cas-dsl surface)
        │  elaboration
        ▼
one coherent semantic category/functor calculus in Lean  (lean-categories)
        │  typed realization / operation contracts        (per-leaf Lean adapter)
        ▼
arbitrarily messy Sage / GAP / Julia / OSCAR code         (backends)
```

The upper three layers protect the user from the bottom one.

---

## 2. The central semantic claim: `x.f` is `f(F(x))`

For a receiver \(x\in\mathcal C\), a method \(m:\mathcal D\to\mathcal E\) owned at its
lowest generating level (#53 §5), and a structural functor \(F:\mathcal C\to\mathcal D\),

\[
\boxed{x.m \;\leadsto_{\text{elaboration}}\; m\bigl(F_n(\cdots F_1(x)\cdots)\bigr)}
\]

Every arrow computes actual data. `L.cardinality()` for a lattice elaborates to

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
| Runtime placement / refinement after construction | `property-refinement.md` | semantic typing plus evidence (CC-PROP) |
| Construction provenance recovery (`_object_inputs`, `_objects_by_datum`) | `resolution.md` "Construction retention" | the typed term already *is* the construction |
| Selected structure-functor inheritance | `functor.md` | elaborator composes `FunctorExpr` (CC-RESOLVE) |
| `FunctorImageCache` | kernel | explicit-application memo table (CC-MEMO) |
| Property subcategories and their inclusions | `cat_kernel` | typed classifier/refinement expressions (#54, CC-PROP) |
| Semantic collision check (same public name, unrelated owners) | `resolution.md` "Semantic collisions" | registry duplicate/ambiguity errors at elaboration (CC-RESOLVE) |
| Diamond handling by declaration order plus executable comparisons | `resolution.md` "Diamond diagnostics" | explicit `NatTransExpr` comparisons; ambiguity is an error (CC-COHERE) |
| Universal constructions with retained apex, legs, mediator | `functor.md` "Diagram shapes and universal constructions" | Mathlib/project constructions returning complete universal data (CC-UNIV) |
| Engine lowering and native reconstruction | `leaves.md` "Computation-engine boundary" | still required, through typed adapters (CC-REALIZE, CC-DECODE) |

What is retained from `sage-categories` is its *requirements*: explicit object and
morphism actions, retained defining maps, comparison cells instead of priorities,
properties outside leaf control, and the rule that a constructor claims its laws while
only tests compute them.

---

## 4. Requirements

Each requirement has a stable identifier. The plan's nodes cite these identifiers; a node
closes only when every cited requirement's acceptance holds.

### CC-TRUE — Every semantic notion is standard mathematics, from step 0

No registry notion, data structure or resolver concept may stand in for mathematics that
the literature already names. Before a mechanism is built, its mathematical denotation is
stated with a source (a definition in FOUNDATIONS with a citation, or a Mathlib
declaration). Engineering vocabulary — "parameterized family", "profile", "parent edge",
"method host", "capability" — may name an *encoding*, and every such encoding states what
it denotes. Where no precise denotation can be stated, the mechanism is not built.

This applies with full force to the first work: CC-FIB is the first instance, and the
existing registry's `CategoryFamilyEntry` is its first audit target.

**Acceptance.** Each registry entry kind, and each `CategoryExpr`/`FunctorExpr`
constructor, has a docstring naming its mathematical denotation and a FOUNDATIONS anchor or
Mathlib declaration; the plan's first node (CC-P0) audits the existing kinds against this.

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

Only the **glue** between found results, and the **residue** that no indexed source
supplies, is written by hand. The searches, their hits, and the reason each hit does or
does not discharge the obligation are recorded with the work (in the commit and in the
owning spec or audit), so the residue claim can be checked.

This extends AGENTS.md's reuse gate from Definitions-sweep units to every obligation this
programme creates, including those that arise in the middle of a proof.

**Acceptance.** Every commit that adds a definition or a nontrivial proof under this
programme cites its search record; a reviewer can rerun the queries.

### CC-CALC — A typed semantic calculus, not a name graph

The registry holds terms the resolver can compose:

- categories, and **fibrations** where a category varies with an object of another
  category (CC-FIB). There is no primitive "category parameterized by a ring";
- functors with **checked object and morphism actions** (not enum tags);
- composition of functors, and identities;
- natural transformations and comparison isomorphisms (`NatTransExpr`);
- categories of elements, slices and coslices, arrow categories, cores, discrete
  categories, diagram categories, subobject categories (#54 §1);
- products, pullbacks, kernels, cokernels, images and the other generic constructions the
  surface uses;
- property subcategories (classifier refinements);
- construction-owned maps (a kernel's inclusion, a quotient's projection).

The existing typed syntax — `CategoryExpr`, `FunctorExpr` with middle-category-checked
`comp`, `NatTransExpr` (`CasCatalogue/Syntax.lean`) and `FunctorEntry`
(`CasCatalogue/Registry/Entry.lean`) — is the seed. `CategoryExpr` does not yet have the
`constructor` case #54 requires; that is CC-CALC's first gap.

**Acceptance.** `Elements(U)`, `Arr(C)`, `Core(C)`, `Slice(C, X)` and `Sub(C, X)` are
`CategoryExpr` values built by one generic constructor case, evaluate to the Mathlib
categories they name, and compose with registered functors under the typed `comp`.

### CC-FIB — Varying categories are fibrations, never parameterized families

"Parameterized category family" is an engineering encoding, not mathematics, and it is not
admitted as a semantic notion. \(R\text{-}\mathbf{Mod}\) is not "a category parameterized by
a ring". It is the fibre over \(R\) of an actual fibration, stated with its variance, exactly
as FOUNDATIONS Definition 13.2 already does:

- the pseudofunctor \(\mathbf{Ring}^{\mathrm{op}}\to\mathfrak{Cat}\), \(R\mapsto R\text{-}\mathbf{Mod}\),
  \(\varphi\mapsto\varphi^{*}\) (restriction of scalars), whose Grothendieck construction
  \(p:\int_{R}R\text{-}\mathbf{Mod}\to\mathbf{Ring}\) is a **cartesian** fibration: objects
  \((R,M)\), morphisms \((\varphi,f):(R,M)\to(S,N)\) with \(\varphi:R\to S\) and
  \(f:M\to\varphi^{*}N\) \(R\)-linear;
- or the covariant pseudofunctor \(\varphi\mapsto S\otimes_R-\) (extension of scalars),
  whose Grothendieck construction is a **cocartesian** fibration over \(\mathbf{Ring}\);
  since \(\varphi_!\dashv\varphi^{*}\), the module fibration is a bifibration, but a use must
  still say which transport it means [@Lur18c, §§5.1.4, 5.6.1, Def. 5.6.2.4];
- or, where it is the better statement, module objects over a monoid in a monoidal
  category, \(\operatorname{LMod}_A(\mathcal V)\), fibred over \(\operatorname{Alg}(\mathcal V)\);
- bimodules are the analogous fibration over \(\mathbf{Ring}\times\mathbf{Ring}\)
  (FOUNDATIONS §86), not a two-parameter family.

Consequences for the calculus:

- "the category of \(R\)-modules" is the fibre \(p^{-1}(R)\), with its fibre inclusion
  \(\iota_R:R\text{-}\mathbf{Mod}\to\int_R R\text{-}\mathbf{Mod}\);
- "change of rings" is transport along a cartesian (or cocartesian) lift, i.e. the
  reindexing functor \(\varphi^{*}\) the fibration supplies, not a new edge between two
  applications of a family;
- a forgetful functor is defined on the **total** category where it is uniform in the
  base: \(U:\int_R R\text{-}\mathbf{Mod}\to\mathbf{Set}\), \((R,M)\mapsto M\); "the
  underlying set of an \(R\)-module" is \(U\circ\iota_R\);
- a structured category over modules is a fibration only when the mathematics transports
  its structure: bilinear forms are a cocartesian fibration over the total module
  category (FOUNDATIONS §15.5–15.6); lattices are **not** closed under base change, so
  they are a classifier refinement of the bilinear-module category, and closure of a
  condition under a particular base change is a theorem, not registry structure
  ([audit §4](registry-denotation-audit.md#4-mathematical-determinations-owner-rulings-2026-09-28)).

The registry's existing `CategoryFamilyEntry` / `CategoryExpr.familyApp` machinery
(`CasCatalogue/Registry/Entry.lean`, `CasCatalogue/Syntax.lean`) and #54 §2's "typed
parameterized families" are admissible **only** as an encoding of this data: each
family entry must name the fibration (or pseudofunctor with its variance) it denotes, and
`familyApp F args` must denote the fibre over the object `args`. An entry that cannot name
its fibration is not a semantic declaration.

**Acceptance.** \(p:\int_R R\text{-}\mathbf{Mod}\to\mathbf{Ring}\) is registered as a cartesian
fibration whose cartesian lifts are Mathlib's `ModuleCat.restrictScalars`; `familyApp
Modules [R]` evaluates to its fibre over \(R\); restriction along
\(\mathbb Z\to\mathbb Z/4\) is resolved as the fibration's reindexing, not as a registered
edge; and `cardinality` of a \(\mathbb Z/4\)-module and of the same group viewed as a
\(\mathbb Z\)-module agree because both factor through the one \(U\) on the total category.

### CC-ACTION — A functor is its two actions

An object map is an actual typed Lean function on realizations, and a morphism map is an
actual function on morphism realizations, together with a denotation into the Mathlib
functor it realizes. The `lean-cas-dsl` enum

```lean
inductive ObjMap | cyclicToFiniteSet
```

is retired as a mechanism. Instead of

```text
UnderlyingSet  source := Modules  target := Sets  objMap := cyclicToFiniteSet
```

the registry holds \(U:\operatorname{Mod}_R\to\mathbf{Set}\) whose object and morphism
actions are checked terms.

**Acceptance.** \(\operatorname{Lattices}\to\operatorname{FormedModules}\to\operatorname{Modules}\to\mathbf{Set}\)
is formed by ordinary composition; no lattice-to-set edge is registered; the composite's
object action on a concrete lattice returns the same set as applying the three actions in
turn.

### CC-TRANSPORT — Data transport is the central resolver operation

Method inheritance means *construct the exact semantic receiver on which the operation is
defined*, never *search categories until a method name appears*. A resolution returns

\[
(F,\;F(X),\;m:\mathcal D\to\mathcal E)
\]

with \(F\) a composite `FunctorExpr`, and execution receives \(F(X)\).

`lean-cas-dsl`'s `Resolution.concreteReceiver` is the correct seed: it already hands the
executor the transported image. It must grow from one hop to an arbitrary typed composite.

**Acceptance.** `L.cardinality()` on a formed module elaborates to
`card (U_set (U_mod (U_form L)))` (in the repository's arrow-order convention), and the
elaborated `Expr` contains the composite, not a string-keyed dynamic call (#53 §13).

### CC-UNIFORM — Inclusions are functors like any other

There is no separate "parent inheritance" and "functor inheritance". A subcategory
inclusion, a classifier forgetful functor, a property restriction, a projection from a
Grothendieck construction, a forgetful functor: all are `FunctorExpr` values in the same
graph, admitted by the same structural-admissibility rule (#53 §8).

*Which functors are edges* (derivation, recorded 2026-09-28 when `cc-resolve` exposed it): an
edge sends an object to an object it *is* — a forgetful functor, an inclusion, a fibre inclusion
\(\iota_R\). A fibration's projection to its base or value parameters (\(\int\operatorname{Mod}\to
\mathbf{Ring}\); \(\operatorname{Bil}\to\int\operatorname{Mod}\) by values) reads a parameter of the
object and is not an edge: with it as an edge, a module inherited its ring's cardinality and every
formed module's `cardinality` became ambiguous. Such a projection is reached as an explicit method
(`base_ring`), never by inheritance. Construction functors (base change, change of values,
reindexing along \(\varphi\)) are not edges either: they need data the receiver does not carry.

**Acceptance.** Removing the special case "parents first, transport only on failure"
(`lean-cas-dsl` `Resolve.lean`, "NEVER A PREEMPTION") changes no resolution in the
existing test corpus except those that the old rule resolved by priority; each such case is
listed and either receives a declared comparison or becomes a reported ambiguity.

### CC-IMMEDIATE — A leaf declares only its immediate structural images

A leaf says what its immediate underlying objects *are* and nothing further:

```text
category Lattices            -- total category, fibred over its base (CC-FIB)
structure functor  underlyingFormedModule : Lattices ⟶ FormedModules
  object action:   L ↦ the actual formed module underlying L
  morphism action: f ↦ the actual formed-module morphism underlying f
  (a functor over the common base: it commutes with the two projections)
```

It cannot declare `Lattices → Sets`, `Lattices.cardinality`, `Lattices.kernel` or
`Lattices.subgroup` because those are useful. They are derived by composition.

**Acceptance.** Registering a functor whose target is reachable from its source through
already-registered structural functors, with no new mathematical content, is rejected
with a diagnostic naming the existing composite. Registering a method on a category below
the method's lowest generating level is rejected (#53 §5).

### CC-SEP — Semantic object, realization, evidence, implementation are four things

A backend object conflates (1) what mathematical object it is, (2) how the backend
represents it, (3) which facts are known about it, (4) which algorithms work on it. Lean
keeps them apart:

```lean
SemanticObject                      -- a point of a registered CategoryExpr
Realization backend X               -- a backend handle realizing X, with codec
PropertyEvidence X P                -- proof, certificate, decision, or trusted assertion
Implementation backend op X         -- an executable route for a semantic operation
```

A backend object is never the authority for category membership. A Sage finite-field
parent returned by a computation is decoded and *associated* with a semantic object
\(K:\mathbf{Field}\) together with its selected structural images.

**Acceptance.** No code path assigns a category to a value by inspecting its backend
representation. (`lean-cas-dsl`'s `profileFrom rules o`, which derives membership by
matching the presentation `Obj`, is the counterexample this acceptance excludes; a
presentation pattern may select a *realization*, never a category.)

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
  between them is additional mathematical data (a registered isomorphism), never a silent
  identification by backend identity.

**Acceptance.** Two realizations of a finite field from different defining polynomials (e.g.
\(\mathbb F_9=\mathbb F_3[x]/(x^2+1)=\mathbb F_3[y]/(y^2+y+2)\); over \(\mathbb F_2\) the only
monic irreducible quadratic is \(x^2+x+1\), so \(\mathbb F_4\) has a single one — corrected
2026-09-28) yield distinct semantic objects; `ask (K₁ = K₂)` is not decided `true`; a registered
isomorphism between them transports elements, and its absence is reported as absence.

### CC-MEMO — Memoization of explicit functor applications only

A runtime may retain \((X,F)\mapsto F(X)\) and \((f,F)\mapsto F(f)\) keyed by the explicit
application. This is optimization only: dropping the cache changes no result. It never
answers "which pieces of \(\mathcal D\)'s state were grafted onto which instance along which
path", because no grafting exists.

**Acceptance.** Every public operation returns the same value with the cache disabled.

### CC-RESOLVE — Composite resolution with provenance and ambiguity

Resolution of `receiver.method(args)` follows #53 §8 steps 1–10. In addition:

- the result retains the full structural path and its normalized composite;
- two composites to the same method source are identified only by a registered comparison
  (CC-COHERE); otherwise the call is **ambiguous** and elaboration fails with both routes;
- no shortest-path rule, declaration order, typeclass priority or "first found" rule
  selects a route. (`lean-cas-dsl`'s `parentClosure` keeps "a shortest [chain]" and
  "diamonds collapse to a single entry"; both are excluded.)
- the base object is part of identity: the fibre over \(R\) and the fibre over \(S\) are
  different categories; change of base is the fibration's reindexing along
  \(\varphi:R\to S\) (CC-FIB), never a parameter carried unchanged along a name edge.

**Acceptance.** The ring diamond: \(\mathbf{Ring}\to\mathbf{AddCommMon}\) and
\(\mathbf{Ring}\to\mathbf{Mon}_\times\) remain distinct for `is_commutative` and are
identified at \(\mathbf{Set}\) for `cardinality` by a registered comparison (#53 §9, §12).

### CC-COHERE — Coherence is data, never priority

If \(F,G:\mathcal C\to\mathcal D\) represent the same intended structure, a specified
\(\alpha:F\Rightarrow G\) (or equality, or isomorphism, as appropriate) is registered. If
they represent different structures, they stay distinct. The resolver rejects an ambiguous
structural projection at elaboration instead of letting order choose.

`sage-categories` reached the same requirement (`resolution.md` "Diamond diagnostics and
coherence"): it forms the competing composites and consumes a retained executable
invertible natural transformation between them, and "differing representations are
related by the supplied natural isomorphism rather than silently identified". Its
remaining fallback — "declaration order selects the preferred initialization path" — is
the one part not copied.

**Acceptance.** A test registers two structural paths without a comparison and observes an
ambiguity error naming both; adding the comparison makes the call resolve and the result
carries the comparison in its provenance.

### CC-PROP — Properties live in Lean; backends only decide them

`Finite`, `Commutative`, `Free`, `PID`, `Nondegenerate`, … are semantic classifiers owned at
their correct level. A backend may supply evidence, a decision procedure, a certificate or
a trusted assertion for a named object. It cannot redefine what the property means, and
it cannot place an object in a property category by attaching a runtime label.

This extends `lean-cas-dsl`'s existing distinction
*semantic availability ≠ implementation availability* from methods to all properties.

**Acceptance.** A backend decision procedure for `IsAbelian` registers against the
classifier (commutativity of the multiplicative port, #53 §12); registering a backend
"abelian group" category is rejected.

### CC-DECIDE — Three-valued decisions, and a wrong `false` is the worst error

A decision returns *true with evidence*, *false with evidence*, or *undecided*. Undecided is
absence of a decision procedure, not a third truth value (FOUNDATIONS Def. 46.4). A backend
that cannot decide must return undecided; it must never collapse a conjunction of
undecided components to `false`.

`sage-categories` exhibits exactly this failure: at `39be374` its limit-category morphism
equality returns `False` for two equal homomorphisms \(\mathbb Z/2\to\mathbb Z/4/\langle 2g\rangle\)
whose every component comparison is undecided (recorded in that repository's
`COMPLAINTS.md`, "Limit-category morphism equality decides False for equal abelian
homomorphisms").

**Acceptance.** Every decision adapter distinguishes the three outcomes in its type; a
test with pointwise-equal but differently constructed morphisms never decides `false`.

### CC-UNIV — Generic constructions are owned above the backends, with complete data

Subgroups are values of \(\operatorname{Sub}_{\mathbf{Grp}}(G)\) (or `MonoOver G`). A
backend subgroup — GAP subgroup object, generator list, membership predicate, matrix-group
wrapper, finite quotient preimage — is a *realization* of that semantic object. Its public
API is the semantic subgroup API; every subgroup has inclusion, underlying set,
intersection, inverse image and action restriction because the construction provides them.

A construction returns its complete universal data: a kernel is \((K,\,i:K\hookrightarrow G)\);
a limit is apex, legs and mediator; a quotient is \((Q,\,q:G\twoheadrightarrow Q)\) with its
universal factorization. A realization that supplies the apex but not the defining map is
invalid.

**Acceptance.** Given a hostile backend class realizing a subgroup
\(H\le O(L)\), the adapter registers it as a realization of the semantic subgroup; the user's
`H` supports every generic subgroup operation with no forwarding wrappers; `H.inclusion`
is the semantic inclusion, and a decode that omits the inclusion fails.

### CC-ADAPTER — Every leaf has a Lean-side contract module

Arbitrary Python/Julia/GAP modules do not register into the semantic runtime. Each leaf has
a small Lean module whose one registration command is `register_leaf`
(`CasCatalogue/Adapter.lean`):

```lean
register_leaf
  { backend := "sage"
    contributions := [
      .realizer { id := ⟨"rz.orthogonal_groups.sage"⟩, category := ⟨"cat.orthogonal_groups"⟩, … },
      .action { id := ⟨"act.orthogonal_groups.underlying_group.sage"⟩, edge := …, … },
      .implementation { … spinor norm … }, .decider { … }, .isomorphism { … } ] }
```

The permitted contributions are realizers, functor actions, implementations, deciders and
registered isomorphisms; codecs live in the realizer's denotation and the decoders producing its
handles. Each is validated by the registry and must typecheck against the semantic universe.
The forbidden contributions of §5 are constructors of the same contribution type, so an attempt
is expressible, and `register_leaf` rejects the whole contract naming the rule. Python cannot create a semantic method by
exporting a function; Julia cannot create a category; GAP cannot claim that a
group-specific operation belongs to all groups.

**Acceptance.** Each forbidden contribution in §5 has a negative test that fails to
elaborate with a diagnostic naming the rule.

### CC-DECODE — Reconstruct across the boundary; never trust backend object shape

A backend result crosses back as

```text
BackendResult { operation_id, encoded_result }
```

and the adapter decodes it into the operation's **expected semantic result type**. For
\(\ker:\operatorname{Arr}(\mathbf{Grp})\to\operatorname{Mono}(\mathbf{Grp})\subseteq\operatorname{Arr}(\mathbf{Grp})\),
\(f\mapsto(\ker f\hookrightarrow\operatorname{dom}f)\), the backend cannot answer
"here is my `KernelSubgroup` class"; it supplies enough data to reconstruct
\((K,\,i:K\hookrightarrow G)\). If the inclusion is missing, the result is invalid.

The bridge is deliberately lossy with respect to backend ontology.

**Acceptance.** A decoder test feeds a result missing a defining arrow and observes
rejection; a well-formed result round-trips to a value equal to the Lean-native result on a
small corpus (#53 §14 E).

### CC-ROUTE — Capabilities register against semantic operations, never backend methods

A backend says "I implement semantic operation \(m\) on realizations satisfying \(P\)",
keyed by a `FunctorId` or normalized `FunctorExpr` (#53 §10 `BackendRealizationEntry`). It
never says "I have a method called `.kernel()`". The backend's method inventory is discovery
input only. Several backend functions may realize one operation; one backend function may
serve several operations through adapters; duplicate or misplaced backend APIs are ignored.

**Acceptance.** Two backends realizing the same composite are two realizations of one
semantic operation; the method audit reports one owner.

### CC-LIFT — Result lifting is explicit mathematical structure

`lean-cas-dsl`'s "NO RESULT LIFTING" ceiling is removed, but not by coercion. An inherited
\(m:\mathcal D\to\mathcal E\) returns \(m(F(x))\in\mathcal E\) (cardinality). An operation
that must return to the source side — a lift along an isofibration, a preserved limit,
transport along an equivalence, an adjunction, a subobject of the *original* structured
object — requires that functor, section, lift or universal property as registered data,
and the operation's source and codomain say so.

`sage-categories/specs/functor.md` states the same separation: reading an operation on
\(F(x)\) and constructing something back in \(\mathcal C\) are distinct obligations.

**Acceptance.** A kernel of a formed-module morphism returns a formed submodule (via the
registered restriction of the form along the inclusion), not a bare module; with that
restriction unregistered, the call reports the missing lift rather than returning the
module kernel.

### CC-CLOSURE — The user-visible method surface is generated

For \(X:\mathcal C\), the available operations are exactly those whose source is reachable
from \(\mathcal C\) by admissible structural composites, with the necessary coherence and
hypotheses (#53 §8 "Static closure"). `#methods X`, documentation, completion and dot
notation derive from that one closure.

Guarantee: *every subgroup has everything expected of subgroups; a specialized subgroup
has more.*

**Acceptance.** Adding a leaf with one structural functor to modules regenerates its closure
and the new category inherits `cardinality`, `rank`, `kernel` with no further declaration.

### CC-TRUST — Epistemic status is attached, never conflated

Each result records whether it is a kernel theorem, a Lean-checked reflected computation,
a certificate-checked backend answer, or a trusted backend assertion (#53 §10 "Trusted
backends", FOUNDATIONS Remark 46.5), with backend and version provenance.

**Acceptance.** The notebook display distinguishes the four statuses for the same
semantic operation run through different realizations.

### CC-LAWS — A construction claims its laws; computing them is a test

No constructor computes associativity, units, naturality, pentagon, triangle or any other
coherence law in order to admit a value. Computing them is how a test checks a
construction. A slow coherence computation is a slow test, not an unfinished construction.
This is `sage-categories`' D26, restated by its owner repeatedly because it was violated
repeatedly (constructors calling `ask` on their defining equations; `certified_*` bypasses;
per-call comparison wrappers). In Lean the law is either a proof field of the structure or
a stated obligation of a test; it is never an admission-time runtime check.

**Acceptance.** No registration command or elaborator step evaluates a law at runtime to
decide whether to accept a declaration.

---

## 5. The leaf contract

A leaf may contribute only:

1. realizations of already-declared semantic objects and categories;
2. implementations of already-declared semantic functors, including actual object and
   morphism data;
3. implementations of already-declared semantic operations and predicates;
4. backend codecs and conversions;
5. new semantic declarations **only** through a separate `lean-categories` change, never
   from the backend package.

A backend leaf cannot:

- invent a public category because its library has a class;
- attach a method to a mathematical object;
- declare a superclass or subcategory relation;
- create an implicit forgetful route;
- decide that two presentations are the same;
- add public coercions;
- refine an object's semantic type after construction;
- expose backend-specific result classes;
- define generic subgroup, kernel or image semantics.

That leaves the backend free to be messy internally.

---

## 6. Where `lean-cas-dsl` stands (at `a191b61`)

The table records what `ddcf982` had and what became of it in `cc-dsl-migration`.

| At `ddcf982` | Now |
|---|---|
| `Resolution.concreteReceiver`: execution sees \(F(X)\), not \(X\) | **kept, generalized**: `Eval.realizationOf` runs the registered actions along the whole route, or hands the image to a backend route (CC-TRANSPORT) |
| `MethodDecl` (semantic) vs `Route` (computability) separation | **kept**; a fused route is keyed by the composite it realizes (`Route.realizes`, CC-ROUTE) |
| Mathlib anchors: `CatDecl.telescope`/`anchor`, `MethodDecl.anchor`, `Denote`/`Verify` | **kept** as `MethodDecl.anchor` and `TypingRule.classes` (synthesized at registration; `verifyTyping` at the call) |
| Structured gaps (`notApplicable`, `ambiguous`, `functorTargetMismatch`) | **kept** as registry resolution errors and `CapabilityGap` naming the resolved route; `functorTargetMismatch` is unrepresentable (typed functor rows) |
| `ObjMap` enum, one constructor per map | **retired** (CC-ACTION) |
| `Obj` presentations whose categories come from `profileFrom` pattern rules | **changed**: a value is a point of a registered category — by ascription, else by the most specific `TypingRule` at construction; presentations select realizations only (CC-SEP) |
| The transported image's category re-derived from its presentation | **changed**: \(F(X):\mathcal D\) by construction |
| `parentClosure`: shortest chain kept, diamonds collapsed | **removed** with `CatDecl`/`FunctorDecl`/`ProfileRule`/`resolveCore` (CC-RESOLVE, CC-COHERE) |
| Transport consulted only when inheritance fails ("NEVER A PREEMPTION") | **removed** (CC-UNIFORM); the one corpus case it decided (`size` on `Modules` and `Sets`) is a reported ambiguity |
| Parameters "ride along unchanged" on parent edges | **changed**: fibres of stated fibrations, reindexing as change of base (CC-FIB) |
| "ONE HOP", "NO RESULT LIFTING" ceilings | **removed** (CC-TRANSPORT); result lifting is CC-LIFT's |

---

## 7. Division of ownership between the two Lean repositories

- `lean-categories` owns mathematics only: categories, functors, fibrations, classifiers and
  their theory (CC-TRUE's and CC-FIB's mathematical content, CC-LAWS), as a library that this
  package requires. It holds no registry, resolver or realization code.
- `lean-cas-dsl` (this repository) owns the CAS machinery over it: the symbolic registry of
  category and functor expressions with their checked denotations into `lean-categories`
  (`CasCatalogue/`: CC-CALC's syntax, CC-IMMEDIATE, the registry manifest and its exporter),
  the resolver and closure (CC-RESOLVE, CC-CLOSURE, CC-UNIFORM, CC-COHERE, CC-PROP), the
  realization/implementation registry (CC-SEP, CC-ROUTE, CC-TRUST, CC-MEMO), adapters and
  decoding (CC-ADAPTER, CC-DECODE), the surface syntax and elaborator, and the backend
  bridges. Its older name-level graph (`CatDecl`/`FunctorDecl`) was deleted in
  `cc-dsl-migration`; `CasCatalogue` is the only graph.

This follows #53 §7 ("no second semantic method registry"): `FunctorEntry` stays the
unique semantic authority, and the name-level graph must not survive as a parallel one.
Decision of 2026-09-28 (user): all foundational mathematics lives in `lean-categories`;
every other repository owns only the Lean its interfaces need and imports the rest.

---

## 8. The executable-versus-typed tension

A semantic object must be both *typed* (a point of a registered category, with Mathlib
meaning) and *executable* (its structural images computable). Mathlib's `ModuleCat ℤ`
objects carry meaning but no computation; `lean-cas-dsl`'s `Obj` values compute but carry no
type. The resolution adopted here:

- the semantic layer is `CategoryExpr`/`FunctorExpr` with Mathlib denotations (existing);
- a realization of a category `C` is a category of handles `R` with a denotation functor
  `d : R ⥤ C`; each registered functor `F` carries a functor on handles `a_F` and a
  2-commutative square `a_F ⋙ d_D ≅ d_C ⋙ F` (Mathlib `CatCommSq`), and composites are pasted
  squares (CC-ACTION); for trusted backends the square may be a trusted assertion recorded under
  CC-TRUST;
- a semantic point is a pair (category expression, realization) whose realization's
  denotation lies in that category; evaluation of a composite applies the handle functors in
  turn, and the result's denotation is isomorphic, through the pasted square, to the composite
  functor applied to the original's.

This keeps #53 §6.1's goal — elaboration emits an ordinary Lean term — while letting
execution run on realizations. When a Lean-native realization exists the two coincide.

---

## 9. Nuances recorded from `sage-categories`

Each is a requirement discovered by failure there; ignore them and the Lean system will
rediscover them.

1. **A functor that computes nothing is not a functor.** Leaves wrote identity-shaped actions
   to satisfy a declaration (`POL-LEAF-070`). Every registered action must construct target
   data.
2. **An accessor is not a functor.** `POL-LEAF-078`: a method returning the underlying
   object is a second, unverified spelling of the structure functor.
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
8. **Construction claims laws** (CC-LAWS, D26).
9. **Undecided is not false** (CC-DECIDE).
10. **A point is not an object of the category.** The level shift (an object of
    \(\mathcal C\) versus a point of an object of a structured category) caused repeated
    defects; `Elements(U)` is the typed source for element methods (#53 §3).
11. **Sage's `Modules(R)` is \((R,R)\)-bimodules**, and Sage's `C.Algebras(R)` is free
    linearization, not internal algebra objects (#54 §2, §4). Backend category names are
    observations, never semantic sources.
12. **Leaves pull generic mathematics in the wrong direction.** In the research repository a
    generic predicate-subgroup module imported from `orthogonal_quotients`. Under this
    architecture that import is ill-typed: the generic subgroup construction is owned above
    every leaf, and a leaf cannot be a dependency of it.

---

## 10. Open questions (do not reopen the governing decisions)

1. Does a realization carry its denotation proof, or is the denotation a separate trusted
   record for backend realizations? (Affects CC-ACTION acceptance for Sage-only functors.)
2. Is the memo table (CC-MEMO) per notebook session or per elaboration?
3. How does `FunctorExpr` represent a fibration's reindexing \(\varphi^{*}\) and fibre
   inclusions \(\iota_R\): as constructors derived from a registered fibration entry, or as
   `atomic` functors whose registration must cite that fibration? Either way the
   fibration, not the pair of `familyApp` endpoints, is the owner.
4. Where does the negative-test corpus for §5 live: `lean-categories` (semantic
   rejections) or `lean-cas-dsl` (backend rejections), or split by rule?
5. #53 §16's ten questions remain open and are inherited unchanged.
6. (Recorded 2026-09-28 by `cc-closure`.) CC-CLOSURE's acceptance says a new leaf with one
   structural functor into modules inherits `kernel` with no further declaration, while CC-LIFT
   says a kernel returning to the source side needs a registered lift. Both cannot hold for a leaf
   whose property is not known to pass to submodules. The implementation keeps CC-LIFT: the
   leaf's surface lists `kernel` with the missing lift. Open: whether a property classifier may
   register "closed under subobjects" once and have its lift derived.
