# Kernel replacement audit (`cc-kernel-audit`, 2026-09-29)

Step 1 of "Current direction" in [computational-core-plan.md](computational-core-plan.md). For each
`sage-categories` milestone-A kernel node, the capability obligations of its owning contract, and
what in the Lean system replaces each. Read-only audit at lean-cas-dsl `71d6123`, lean-categories
`2794bef`, sage-categories `93c8ff4`.

**Status meanings.** EXISTS: a registered declaration in `CasCatalogue`/`lean-categories` performs
it, with the probe or test that exercises it. PARTIAL: part of it, or only the mathematics (Mathlib
or `lean-categories`) with no registry row and no consumer. GAP: absent. "Mathlib only" is not a
replacement: the resolver cannot compose what is not registered. Mathlib declaration names in
PARTIAL rows were partly recalled, not read; each is verified before use.

## Summary

The Lean system replaces the *mechanism* of the Python kernel (spec §3: C3, role classes,
initializer threading, grafting, runtime placement, image cache) and the resolver-level contracts:
explicit transport `x.f ↦ f(F(x))` along composites, typed functor expressions, distinct structures
on one carrier, comparison cells validated at registration, property classifiers with three-valued
deciding, inverse images, memoization, the leaf contribution firewall.

It does not yet replace most of the *categorical calculus* the Python kernel supplies to leaves.
By node:

| sage-categories node | coverage |
|---|---|
| `core-selected-transport` | mostly EXISTS; missing point functors, level shift, image categories, general result lifting |
| `core-inheritance-coherence` | mostly EXISTS; comparisons are provenance only (never applied to data), no formal/executable split, no invertible cell calculus, no centrally derived comparisons |
| `core-properties-refinement` | about half; missing same-object refinement, `assume`, classifier intersection and sibling containment, reindexing identities |
| `core-static-and-boundaries` | about half; missing import-level boundaries, generated checks for trusted actions |
| `core-functor-cell-calculus` | syntax only; natural transformations not registered or exercised; no inverses, `Op`, `Mor` tower, functor-property categories |
| `core-indexed-calculus` | mathematics exists (fibrations, fibres, reindexing); registry has only discrete-parameter families; adjunctions, equivalences, Yoneda unregistered |
| `core-universal-calculus` | essentially GAP: no diagrams, cones, limits, mediators, adjunctions, Kan extensions in the registry; only subobject inclusion/meet |
| `core-weighted-calculus` | essentially GAP |
| `core-algebraic-calculus` | essentially GAP beyond Set-level algebra and ModuleCat over rings |
| `core-structured-calculus` | essentially GAP |
| `kernel-cat-complete` | GAP (depends on the above) |

## Cross-cutting findings

1. **Probe evidence is not gated.** `just build` runs `lake build CasDsl CasDslTests nbdsl_worker`;
   the `CasCatalogue/*Probes.lean` files are reached only from the `CasCatalogue.lean` root, so the
   repository's own gate never compiles the acceptance probes cited above.
2. **No leaf passes through the adapter boundary.** `register_leaf` is used only in
   `AdapterProbes.lean`. Every realization is a Lean-native handle (tables, Gram matrices, finite
   sets). The only backend bridge is `backends/sage_adapter.py`; none for GAP, OSCAR/Julia, Catlab.
   No `sage-categories` leaf has been migrated.
3. **Unproved axioms in the registry.** `CasCatalogue/Realization.lean:137–185` declares twelve
   `axiom`s asserting family-parameter quotations (`commRingNat`, `domain`,
   `commRingModuleTensorProduct`, …). They are consistent (the target is an opaque `Prop`) but are
   unproved tags inside the semantic layer.
4. **Selection is order-dependent in two places.** `resolveMethod` takes the first route of an
   identified class and never applies the comparison to data; `comparisonBetween?` takes the first
   matching comparison when several are registered. Both contradict CC-COHERE's "no order".

## Per-node obligations

### core-functor-cell-calculus

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| Functor = object action + morphism action; composite `G*F` | functor.md "Functors as morphisms of `Cat`", "Functor actions are concrete constructors" | EXISTS | `Action.lean:RealizedAction`, `Realizes.comp`; `Syntax.lean:FunctorExpr.comp`; probes `ResolveProbes`, `LiftProbes` |
| Identity functor | same | EXISTS | `FunctorExpr.identity` |
| `Fun(C,D)` as a category, evaluation, composition functors | "Functor-category calculus" | PARTIAL | `Constructors.lean:functorCategory` (only `endofunctorsSets` registered); no `ev(i)`, `Fun.composition`, `Fun.evaluation` |
| Natural transformations: vertical, horizontal composition, whiskering | "Functors as morphisms of Cat", "Functor-category calculus" | PARTIAL | `NatTransExpr.{identity,atomic,vcomp,hcomp}`, `Interpretation.lean:evalNatTrans`; no registry row kind, no consumer |
| Associator/unitor isomorphisms retained | "Functor-category calculus" | GAP | — |
| Invertible 2-cells, executable componentwise inverses | TODO decision row "Existing higher cells" | GAP | no inverse/iso in `NatTransExpr` |
| Formal generator vs executable transformation (component rule on unenumerated domains) | "The Mor(n, C) tower" | GAP | transformations have no realizer action |
| `Mor(n,C)` tower, higher cells | "The Mor(n, C) tower" | GAP | — |
| `Op` on C, F, η; `Op∘Op ≅ Id` | "Opposites and dualization" | GAP | — |
| Functor-property subcategories (Full, Faithful, EssSurj, Equivalences) and containments | "Functor property subcategories" | PARTIAL | proofs carried by `PropertyClassifier`/`FibrationEntry` only; no property categories of `Fun` |
| Subcategory mono = monic isofibration | "Monomorphisms of Cat() and placement" | PARTIAL | `PropertyClassifier` lacks repleteness / injectivity on objects |
| `End_C(X).one()` | "Functor-category calculus" | GAP | — |

### core-selected-transport

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| `x.f() = F(x).f()` with explicit image `F(x)` | TODO "Functorial inheritance"; functor.md "Selecting a retained functor" | EXISTS | `Resolve.lean:resolveMethod`, `composeRouteFrom`, `realizedCall`; `ResolveProbes`, `CasDslTests/Transport.lean` |
| Transport along composite structure functors | TODO `core-selected-transport` | EXISTS | `Route` composites; lattice → form → Mod → ∫Mod → Sets |
| Selected edges are faithful isofibrations | functor.md "Monomorphisms of Cat()" | PARTIAL | `FunctorEntry.structural` is an unproved flag |
| Distinct structures on one carrier stay distinct | TODO "Functorial inheritance" | EXISTS | ring ports ambiguity (`ResolveProbes`, `PropsProbes`) |
| Morphism images through selected functors | TODO `core-selected-transport` | PARTIAL | only via `Arr(F)`/`Core(F)` constructMap |
| Results returned to the source category are lifted | functor.md "Induced functors" | PARTIAL | `Lift.lean:MonoLift` (monomorphisms only) |
| Retained images computed once | TODO `core-selected-transport` | EXISTS | `Memo.lean:memoApply` |
| Point functor `* → C`, generated inclusions | "Point categories and point functors" | GAP | element categories are ad hoc atoms (`Leaves/Elements.lean`) |
| Categorical level shift (`ObjectType`/`ElementType` surfaces) | "The categorical level shift" | GAP | — |
| Strict/full/essential images owned by the codomain | "Strict, full, and essential images" | GAP | — |
| Ambient algebraic categories (`Semirings(Cat())`) | "Ambient algebraic categories" | GAP | — |

### core-universal-calculus

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| Diagrams as objects of `Fun(I,C)`; shapes Discrete/Thin/finite presented | functor.md "Diagram shapes and universal constructions" | GAP | — |
| Cones/limit cones with diagram, apex, legs, `lift` | same | GAP | Mathlib `LimitCone`/`IsLimit.lift` not exposed |
| Several presentations sharing an apex | same | GAP | — |
| Cocones/colimits via `Op` | same | GAP | — |
| Products/coproducts, `X*Y` | same | GAP | — |
| Pullbacks/pushouts/(co)equalizers; `C.Limits(I)` | same | PARTIAL | subobject meet (`UnivProbes`), `Classifier.reindex` pullback only |
| `limit_functor()`; induced maps via mediators | same | GAP | — |
| Retained defining maps (subobject inclusion) | "Universal calculus"; CC-UNIV | EXISTS (subobjects only) | `Leaves/Algebra/Subgroups.lean`; `UnivProbes`, `AdapterProbes` |
| `PreservesLimits`/`CreatesLimits` as functor properties | same | PARTIAL | `StrictlyCreates.lean` Prop, not registered |
| Limit lifting along functors, mediator via faithfulness | same | GAP | — |
| Limits from products + equalizers | "Universal calculus" | GAP | — |
| Infinite/nonenumerable products; sequential colimits | TODO acceptance | GAP | — |
| Universal arrows, adjunctions (transpose, mates), equivalences | "Universal calculus"; "Adjunctions and equivalences" | GAP | — |
| Kan extensions with unit/counit | "Induced functors" | PARTIAL | `RiehlPointwiseKan.lean`, not registered |
| Inserter/equifier; `Algebras(T)`, Eilenberg–Moore | "Universal calculus" | GAP | — |
| Currying; weighted limits; ends/coends; profunctors; relations | same | GAP | — |
| Slices/coslices/arrows/elements with projections; `Comma(F,G)` | "Comma categories, slices..." | PARTIAL | `Constructors.lean`; no `Comma(F,G)` |

### core-properties-refinement

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| `C.P()` full subcategory, monic-isofibration inclusion | property-refinement.md "Property category" | PARTIAL | `PropertyClassifier` (no repleteness/injectivity), `CategoryExpr.refine` |
| Property category alone owns the predicate | "Property category", "Defining predicate" | EXISTS | `PropertyEntry`; `PropsProbes` rejects an "abelian groups" atom |
| `X.is_P()` through structural descendants | "Compiled public surface" | EXISTS | `resolveProperty`, `ask%`; `PropsProbes`, `ClosureProbes` |
| Three-valued evaluation; Unknown never False | undecidable-properties.md "Evaluation" | EXISTS | `Decide.lean:Decision`, `answer_ne_false_of`; `PropsProbes`, `ProbeCorpus` |
| Category-owned equality, three-valued | undecidable-properties.md "Equality" | PARTIAL | per-leaf deciders only |
| Typed queries with result category or Unknown | "Typed queries" | PARTIAL | value methods have no undecided outcome |
| Containment `C.P() ↪ C.Q()` as a declared mono | "Property containment" | PARTIAL | nested refinements only |
| Intersections as retained pullbacks | "Property containment" | PARTIAL | no classifier intersection |
| Inverse images `F⁻¹(P)` with both projections | "Inverse images"; functor.md "Inverse-image subcategories" | EXISTS | `CategoricalPullback.lean:Classifier.reindex` |
| Identities `F⁻¹(C)=D`, `i⁻¹(P)=P`, associativity | functor.md "Inverse-image subcategories" | GAP | `ReindexIdIso`/`ReindexCompIso` have no instances |
| Same-object refinement on a positive answer, preserving identity, data, images | "Same-object refinement" | GAP | a proved `Decision` never yields an object of the refinement |
| `assume(p)`/`retract(p)`, ambient hypotheses | undecidable-properties.md "Assumptions" | GAP | — |
| Morphism properties from `Mor(C)` (Mono/Epi/Iso/Aut) | functor.md "The Mor(n, C) tower" | PARTIAL | `isMonoArrow`, `Subobjects(C)` only |
| Fixed-endpoint functor properties; endpoint mismatch rejected | functor.md "Functor property subcategories" | PARTIAL | endpoint typing holds; property categories missing |

Deleted mechanism (no counterpart): C3 linearization and MRO caches; dynamic role classes; initializer threading; target-state grafting (D13); `structure_functors()` as Python bases and declaration-order diamonds; `FunctorImageCache` and construction retention (replaced by `Memo.lean`); runtime class mutation for refinement; SymPy assumption plumbing (replaced by `Decision`/`Decider`); stub generation; collision registries (replaced by resolver ambiguity errors).

### core-inheritance-coherence

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| Form the competing composites of selected paths | functor.md "Structural diamonds and coherence"; resolution.md "Diamond diagnostics" | EXISTS | `Resolve.lean:RegistryState.routes`, `Route.compositeExpr` |
| Comparison is an ordinary invertible natural transformation between the exact composites | DECISIONS "Coherence and compiler diagnostics" | EXISTS | `ComparisonEntry`, `validateComparison` (Mathlib `Iso`, defeq endpoints); `CohereProbes` (`cmp.rings.carrier`) |
| Ill-typed comparison fails at its boundary | resolution.md "Diamond diagnostics" | EXISTS | `validateComparison` rejections in `CohereProbes` |
| Missing comparison → diagnostic naming both composites | DECISIONS "Path selection and compiler integration" | EXISTS (stricter: no order fallback) | `ResolutionError.ambiguous`; does not name the required comparison category |
| Distinct structures sharing a target stay distinct | DECISIONS "Path selection" | EXISTS | `CohereProbes` (magma-owned method stays ambiguous on rings) |
| Comparison components transport values, arguments and results | functor.md "Structural diamonds"; DECISIONS "Path selection" | PARTIAL | comparison is provenance only; `realizedCall` never applies a component; first route chosen |
| Formal vs executable comparisons; several executable ones → ambiguity | resolution.md "Diamond diagnostics" | PARTIAL | evidence is proof-level only; `comparisonBetween?` takes the first match (order-dependent) |
| Cell calculus with inverses supplied by higher invertibility | DECISIONS "Higher invertibility" | PARTIAL | `NatTransExpr` without inverses, rows or consumers |
| Generic structural comparisons derived centrally | DECISIONS "Path selection" / "Higher invertibility" | GAP | only one hand-registered comparison row |
| Coherence governs property resolution | TODO row | EXISTS | `resolveProperty` via `coherenceClasses` |

### core-indexed-calculus

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| `Grothendieck(P)` for a pseudofunctor | functor.md "Indexed categories, Yoneda, and representability" | EXISTS | `FamilyFibration.lean`, `CategoryExpr.familyTotal`; `fib.modules`, `fib.modules_ext`, `fib.bilin_forms`; `FibrationRegistryProbes.lean` |
| Nonstrict compositor | TODO row | EXISTS (math) | pseudofunctor transports in lean-categories |
| Projection is a fibration; cartesian lifts and factorization | functor.md "Indexed categories" | EXISTS math / PARTIAL registry | `projection_isFibered`, `GrothendieckCocartesian.lean`; no registered lift/factorization method |
| Fibre ≌ P(c) with unit/counit | same | EXISTS (math) | `GrothendieckFibers.lean:fibreEquivalence`; not registered |
| Pseudonatural transformation induces total-category functor | TODO row | PARTIAL | Mathlib `Grothendieck.map`, lean-categories `GrothendieckMapCocartesian`; no `FunctorExpr` constructor |
| Reindexing along a base morphism | functor.md "Indexed categories" | EXISTS | `FunctorExpr.familyReindex`, `modulesReindexDeclaration` |
| `F.base_change(p)` for arbitrary fibrations with cartesian lifts | same | PARTIAL | classifier (subterminal) case only |
| `Adjunctions(F,G)` as a category with unit/counit | functor.md "Adjunctions and equivalences" | GAP | Mathlib `Adjunction` data only |
| `Equivalences(C,D)` as a category | same | PARTIAL (Mathlib) | `Category (C ≌ D)`; not registered |
| Δ ⊣ Lim, transpose/untranspose, mates | functor.md "Adjunctions"; "Universal calculus" | PARTIAL (Mathlib) | not in the repos |
| Yoneda / co-Yoneda functors; `Representations(F)` | functor.md "Indexed categories" | PARTIAL / GAP | Mathlib `yoneda`, `RepresentableBy`; not registered |

### core-weighted-calculus

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| `Elements(W)` and its projection | functor.md "Universal calculus" | EXISTS | `Constructors.lean:elements`, `ConstructorRegistration.lean` |
| Weighted limits/colimits with projections, mediators | same | GAP | — |
| Ends/coends; nat-trans ↔ end points | same | PARTIAL (Mathlib) | `Limits/Shapes/End.lean`; unused |
| Kan extensions and adjunctions | TODO row | PARTIAL | `RiehlPointwiseKan.lean`, `CodensityMonad.lean`; not registered |
| Profunctors and their composition via coends | functor.md "Universal calculus" | GAP (composition) | Mathlib `Profunctor/Basic.lean` types only |
| `Relations(C)` of a regular category | same | GAP | — |
| Universal arrows deriving adjoints | same | PARTIAL (Mathlib) | not in the repos |
| Restricted Yoneda `N_j`; separating/dense families; density reconstruction | separating-families-and-categorical-generators.md | PARTIAL (Mathlib) | `restrictedYoneda`, `IsSeparating`, `IsDense`; not in the repos |
| Evaluation epimorphism from the indexed coproduct, natural, infinite indices | same "Evaluation epimorphisms" | GAP | — |
| Executable Hom-end over finite-set indices | TODO row | GAP | — |

### core-algebraic-calculus

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| Supplied nonstrict monoidal V; two structures on one category distinct | magmas-monoids-semirings.md "Ambient categorical data" | PARTIAL (Mathlib) | `MonoidalCategory` is a typeclass; unused |
| `Actions(M,C)` (actegories) | modules.md "Ambient categorical data" | PARTIAL (Mathlib) | `MonoidalLeftAction`; unused |
| `Magmas(V)`/`Monoids(V)`/`Groups(V)` internal to V | magmas-monoids-semirings.md "Monoids", "Groups" | PARTIAL | Mathlib `MonObj`; catalogue magmas/monoids are Set-level only |
| Named Additive/Multiplicative copies; `Semirings(C)` as a pullback | magmas-monoids-semirings.md "Semirings", "Named operations" | PARTIAL | concrete ring ports + `cmp.rings.carrier` only |
| Inserter, Equifier, `Algebras(T)`, Eilenberg–Moore | functor.md "Universal calculus" | PARTIAL / GAP | Mathlib `Endofunctor.Algebra`, `Monad.Algebra`; no inserter/equifier |
| `Modules(A,C)` over an actegory; `U_A`; homomorphisms, transport, restriction, unit module | modules.md "Objects", "Structure functor", "Owned operations" | PARTIAL | Mathlib `Monoidal/Mod.lean`; catalogue has ModuleCat over rings only |
| Selected relative monoidal structure on modules | modules.md "Optional selected relative tensor structure" | GAP | — |
| `Bimodules(R,S,V)` via reversed V; equifier of commuting laws | bimodules.md "Right actions through the reverse" | PARTIAL (Mathlib) | Mathlib `Bimod`; unused |
| Relative tensor via retained coequalizer with mediator, induced actions, coherence | bimodules.md "Relative tensor product" | PARTIAL | Mathlib `Bimod` tensor; lean-categories `NoncommutativeTensor.lean` concrete only; not registered |
| `Algebras(R,C)` = Monoids(V_R); presentation equivalence; restriction | algebras.md "Structure functor", "Owned operations" | PARTIAL (Mathlib) | `Monoidal/Internal/Module`; not registered |
| Preserved-colimit transport of retained universal data | TODO row | PARTIAL (Mathlib) | no repo construction |
| Geometry consumers (section rings, stalk mediation) through generic constructions | TODO row | GAP | — |
| Constructors claim their laws (D26) | AGENTS.md | EXISTS | proof fields at construction (CC-LAWS) |

Deleted mechanism: C3 chains and declaration-order precedence; once-only initializers; dynamic role classes; DEBUG diamond logging; `subcategory_class` invalidation; retention-identity canonicalization and private cone dictionaries; `EquifierCategory.__call__` law admission; Python `MonoidalStructures`/`Actions` runtime classes; per-class initializer threading for semiring legs.

Caveat from the audit: Mathlib declaration names in PARTIAL (Mathlib) rows were partly given from memory; file existence was checked, individual declarations must be verified before use.

### core-structured-calculus

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| `Adjunctions(F,G)` as a category of (η, ε) data | functor.md "Adjunctions and equivalences" | GAP | Mathlib `Adjunction` data only |
| `Equivalences(C,D)` with inverse and unit/counit | same | GAP | Mathlib only |
| Δ_I ⊣ Lim_I selected adjunction | same | GAP | Mathlib only |
| `Grothendieck(P)` in general: total, fibration, fibres, reindexing, cartesian lifts, action of indexed-category morphisms, `F.base_change(p)` | functor.md "Indexed categories" | PARTIAL | `FamilyFibration.lean` for registered discrete-parameter families only |
| Yoneda / co-Yoneda retained functors; `Representations(F)` | same | GAP | Mathlib only; `InitialRepresentable.lean` initial/terminal only |
| Restricted Yoneda, separating/dense families, evaluation epimorphisms | functor.md; separating-families-and-categorical-generators.md | GAP | Mathlib only |
| Inserter, Equifier, `Algebras(T)`, Eilenberg–Moore | functor.md "Universal calculus" | GAP | — |
| Universal arrows, transpose, mates | same | GAP | Mathlib only |
| Currying equivalence | same | PARTIAL | functor-category constructor only |
| Limits from products + equalizers with mediator | same | GAP | — |
| `Elements(W)` with registered cocartesian lifts | same | PARTIAL | constructor registered; lift not registered, no probe |
| Weighted (co)limits; ends/coends; profunctor composition; `Relations(C)` | same | GAP | — |
| Kan extensions with units/counits | functor.md acceptance | GAP | predicates only (`RiehlPointwiseKan.lean`) |
| General `Comma(F,G)` with its natural transformation | functor.md "Comma categories, slices..." | PARTIAL | slice/coslice only |
| Supplied monoidal category and actions with distinct acting/acted categories | TODO `core-structured-calculus` | GAP | Mathlib only |
| Internal magmas/monoids/groups/semirings in a supplied (V, ⊗) | magmas-monoids-semirings.md "Ambient categorical data" | PARTIAL | Set/Type-level only (`Algebra/Concrete/Magmas.lean`, `clf.magmas.*`) |
| Modules over a monoid object, relative tensor, bimodules | modules.md; bimodules.md | PARTIAL | ModuleCat over rings only; relative tensor only as an axiom-tagged parameter |
| Nonstrict / nonidentity comparison cells | TODO `core-structured-calculus` | PARTIAL | the one registered comparison is an identity iso |

### core-static-and-boundaries

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| Constructor parameters, Hom endpoints, functor variance survive statically | functor.md (static projection) | EXISTS | `FunctorExpr : CategoryExpr → CategoryExpr → Type`, `Interpretation.evalFunctor`; `ResolveProbes`, `ActionProbes` |
| Refinement identities and selected structures | same | EXISTS | `CategoryExpr.refine`, `RefinementRealization`; `PropsProbes` |
| Generated surface matches runtime | TODO `core-static-and-boundaries` | EXISTS | `RegistryState.closure`; `ClosureProbes` |
| Leaves cannot reach compiler/retention/native internals | same | PARTIAL | `Adapter.lean` forbidden contributions (`AdapterProbes`), `ExportBoundaryProbe`; no import-level restriction on what a leaf module may import |
| Module classification, protected modules, indirect-import contracts | same | GAP | — |
| Checks derived from declarations (category, functor, transport, universal, reconstruction) | same | PARTIAL | laws as proof fields, `Action.Realizes`, `CertifiedImplementation`; trusted actions carry no proof and get no generated test |
| Diagnostics without string dispatch | same | PARTIAL | typed errors, but ids are strings (`"cat.x"`) |

### kernel-cat-complete

| obligation | sage-categories locator | Lean status | Lean locator / missing capability |
|---|---|---|---|
| Inheritance and placement hidden from leaf authors | TODO `kernel-cat-complete` | EXISTS | registry routes; `ImmediateProbes`, `ClosureProbes` |
| Constructions claim their laws (D26) | AGENTS.md; CC-LAWS | EXISTS | no registration evaluates a law |
| Exact-positive `ask()` refines the same object | TODO `kernel-cat-complete` | PARTIAL | `Decision`/`Decider`; no re-typing into the refinement |
| `Representations(F)` with unenumerated supplied Hom data | same | GAP | — |
| Co-Yoneda and weighted-limit maps | same | GAP | — |
| Comparison boundaries checked once at compile time | same | EXISTS | `ComparisonEntry` validation; `CohereProbes` |
| `Cat().Pullbacks().limit_functor()` on arbitrary cospan morphisms | same | GAP | — |
| Countable and nonenumerable indexed set (co)products with mediators | same | GAP | — |
| Preserved-colimit transport, relative-tensor descent, section descent | same | GAP | — |
| All of the above at one revision with independent review | same | GAP | follows from the rows above |

## Leaf inventory

What each `sage-categories` leaf declares through the Python kernel, the engines it calls, and the
Lean counterpart. Counts are approximate.

| leaf | declares through the Python kernel | engines | Lean counterpart |
|---|---|---|---|
| `sets/finite.py` | `SetsCategory`, `SetSubobjects`; Finite, Membership predicates; indexed products/coproducts, sequential colimits, quotients; ~29 methods | GAP (libgap), Sage, sympy, CAP | PARTIAL: `cat.sets`, `cat.subobjects_sets`, slices, `clf.sets.finite`, subset operations, cardinality; no indexed (co)products, colimits, quotients |
| `sets/cardinals.py` | `CardinalCategory` | — | EXISTS: `cat.cardinals`, `fun.sets.cardinality` |
| `sets/natural.py` | positive integers, sequential (thin) categories, natural order | sympy | GAP (only a value category) |
| `order/posets.py` | 9 categories (relations, posets, subposets, finite/ranked/graded/bounded/totally ordered), 9 predicates, 4 structure functors | Sage posets | GAP in registry (lean-categories `Orders.lean`; Mathlib `PartOrd`) |
| `algebra/abelian.py` | abelian groups, tensor, bilinear maps, relative tensor with mediator, coequalizers, indexed free coproducts | GAP/CAP, Sage `fg_pid` | PARTIAL: additive groups, groups, ring ports; no relative tensor |
| `algebra/commutative_rings.py` | ℤ, prime fields, polynomial and quotient rings, localizations, prime ideals, stalk maps | OSCAR (Julia), sympy | PARTIAL: rings, ideals, element points; no localization/quotient rows |
| `algebra/algebras*`, `free_associative`, `presented_algebras` | base-relative algebras, free and presented algebras, scalar change | Sage `free_algebra` | GAP in registry (lean-categories `FreeAlgebras.lean`) |
| `algebra/modules*`, `free_modules`, `indexed_modules`, `presented_modules` | free, indexed free, presented modules; bases, injections, projections, homs, presentation factor | Sage, GAP/CAP | best covered: module fibration, free/f.g./finite-rank modules, rank/annihilator/kernel/image, forms, lattices; no presented-module universal factor |
| `algebra/presented_groups.py` | group presentations | Sage `free_group` | PARTIAL: finite groups by table only |
| `algebra/adeles.py` | adele values, opens, presentations | sympy | GAP in registry (lean-categories adele files) |
| `algebra/local_fields.py` | ℚ, ℝ, p-adic presentations | sympy | GAP in registry |
| `geometry/spaces`, `topological_rings`, `ringed_spaces`, `locally_ringed_spaces` | 4 categories with morphism data | sympy | GAP in registry (Mathlib covers the mathematics) |
| `geometry/sheaves`, `stalks`, `affine_global_sections` | ring presheaves/sheaves, descent, stalks | — | GAP |
| `geometry/affine.py` | affine opens, affine schemes, Spec, structure sheaf | OSCAR | GAP (lean-categories `AlgebraicGeometry/*`) |
| `geometry/schemes.py` | scheme opens, schemes, finite affine gluing, ℙ¹ | OSCAR | GAP: only a value category `cat.schemes_over_q` |
| `geometry/cw.py` | ℂPⁿ, ℂP^∞ presentations | sympy | GAP |

Core-owned engines (`catlab`, `gap`, `fp_categories`, `category_limits`, `functor_categories`, …)
serve `cat/` and have no Lean bridge.
