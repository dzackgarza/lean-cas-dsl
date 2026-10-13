# Design assessment (`cc-design-assessment`, 2026-09-29)

Step 1 of "Current direction" in [computational-core-plan.md](computational-core-plan.md): the current
`lean-cas-dsl` (at `4a9e1fe`, with lean-categories `2794bef`) against each requirement of
[computational-core.md](computational-core.md) and its leaf contract (§5). Inputs: the code, and
[kernel-replacement-audit.md](kernel-replacement-audit.md) for what `sage-categories` learned the
system must supply.

## The shape of the gap

`lean-cas-dsl` is currently two systems joined at one seam.

- **`CasCatalogue`** is the semantic layer the spec asks for: typed `CategoryExpr`/`FunctorExpr`,
  registered functors whose actions are checked Lean terms, resolution by composing structural
  routes, comparison cells, classifiers, lifts, closure. Its leaf boundary, however, admits leaf
  authority the design forbids: realizers whose denotation functor a leaf supplies, deciders
  carrying a leaf's evidence, and trust levels on leaf answers. It covers a small mathematical universe (sets, subsets,
  magmas→groups/rings with ports, the module fibration, forms and lattices, subgroups) and almost
  none of the generic constructions (limits, adjunctions, cells as data, monoidal structure).
  Its only realizations of forms and lattices are Gram-matrix handles (`GramHandle`,
  `rz.lattice.int_gram`): a finite-free realization detail of one specimen leaf, which the notebook
  layer then exposes as the meaning of `BilinModules(ZZ)` / `Lattices(ZZ)`. That is out of scope for
  the system: a bilinear module is a module with a map out of `M ⊗ M`, finite or not.
- **`CasDsl`** is the older notebook system with the new resolver bolted underneath. Its values are
  presentations (`Obj`/`Value`) typed by presentation patterns (`TypingRule`, `Std.lean`); its
  executors are hand-written algorithms (`Native.lean`, ~1500 lines) and a Sage route table keyed
  by presentation patterns; the only bridge between a presentation and a semantic point is a
  hand-written `match` in `Semantic.lean:encode` naming each leaf's realizer.

The system the spec describes has one layer, not two. What must happen is that the notebook's
values *become* semantic points produced by registered constructors, its operations *become*
registered semantic operations, and its executors *become* opaque leaf computations registered
against those operations' declared types. Most of `CasDsl` as it stands is the thing the design replaces.

## Requirement by requirement

| requirement | realized | realized wrongly | missing |
|---|---|---|---|
| CC-TRUE / CC-REUSE (standard mathematics, search first) | FOUNDATIONS denotations for registered notions; Mathlib reuse in `lean-categories` | `Native.lean` hand-rolls exact arithmetic, set operations, linear algebra, residue reduction (`Eval.reduceMonic`) that engines or Mathlib own | search records for most CasDsl operations |
| CC-CALC (typed calculus) | categories, constructors (slice, coslice, arrow, elements, subobjects, core, functor category), functors, composition, refinements, family applications | natural transformations exist as syntax (`NatTransExpr`) with no registry row, no inverses, no consumer | products, pullbacks, (co)limits with their data, adjunctions, equivalences, `Op`, comma categories, monoidal structure and actions — as terms the resolver composes |
| CC-FIB (fibrations, not families) | `fib.modules`, `fib.modules_ext`, `fib.bilin_forms` with checked evidence; fibre equivalences | lattice and form *families* still carry the notebook (`cat.lattice` at `(ℤ, ℤ)`); twelve `axiom` parameter quotations in `Realization.lean` | fibres of refinements as registered expressions; general pseudofunctor → Grothendieck constructor |
| CC-ACTION (a functor is its two actions) | composition of functor rows along routes | `RealizedAction` with a leaf's `Realizes` proof: the leaf's proof decides what its step means; many functor rows have no executable step at all, so their composite cannot run | executing a functor's step as a registered operation with a declared type, which a leaf computes and nothing believes |
| CC-TRANSPORT (`x.f ↦ f(F(x))`) | `resolveMethod`, `composeRouteFrom`, `realizedCall`; the notebook calls through it | when no Lean action exists the DSL passes the *presentation* along the route unchanged ("trusted identity presentation") | — |
| CC-UNIFORM (inclusions are functors) | classifier forgets and structural functors are one edge kind | — | — |
| CC-IMMEDIATE (leaf declares only immediate images) | shortcut functors and below-level methods rejected by definitional equality (`ImmediateProbes`) | the rule is enforced on registry rows, but CasDsl's typing rules, route table and `encode` let the DSL layer attach categories and executors directly to presentations, bypassing it | — |
| CC-SEP (semantic object / presentation form / fact / implementation) | the semantic object as a point of a registered category | `Realizer`/`Denotation` supplied by a leaf, `Decision` with a leaf's evidence, `Trust` statuses on leaf answers: each lets a leaf decide meaning or standing; CasDsl types values by presentation pattern (`TypingRule`): a presentation decides a category, the counterexample the spec names | presentation forms declared upstream with what they denote; implementations as opaque computations between them |
| CC-CARRIER | `U` is a registered functor; presentations stay distinct | isomorphisms between presentations are asserted by leaves (`handleIso`) | comparisons between presentations as mathematics of the catalogue |
| CC-MEMO | `Memo.lean:memoApply` | — | not used by the resolver or the notebook |
| CC-RESOLVE (composite resolution, provenance, ambiguity) | all routes enumerated; ambiguity is an error listing routes; provenance retained | — | — |
| CC-COHERE (coherence is data) | comparisons validated as isomorphisms between exact composites | the resolver takes the *first* route of an identified class and never applies the comparison to data; `comparisonBetween?` takes the first matching comparison | executable comparison components; comparisons derived from constructions |
| CC-PROP (properties live in Lean) | classifiers, `PropertyEntry` | deciders registered against classifiers carry a leaf's evidence | property computations registered against classifiers as opaque computations; refinement of an object only on a proof in `lean-categories` or by the kernel; `assume`; classifier intersection and containment |
| CC-DECIDE | three-valued decision result | notebook equality is `Native.valueEq`, a heuristic outside the classifier machinery (it answered `false` for equal maps until `7446650`) | category-owned equality deciders for every category the notebook compares in |
| CC-UNIV (generic constructions above backends) | subgroups as `Subobjects(Grp)` with inclusion; hostile handle decoded; kernel functor with `(K, ι)` | — | limits, colimits, quotients, images and kernels in general, with complete universal data, as registered constructions |
| CC-ADAPTER (a leaf is a registration) | `register_leaf`, ten forbidden kinds (`AdapterProbes`) | a leaf is a Lean module whose permitted kinds carry functors, proofs and evidence; no real leaf uses the contract: `CasCatalogue/Leaves/*` registers 94 functor rows directly through `normalized_registry`, and CasDsl registers executors in `Std.lean` | a registration of exactly (operation id, input form, implementation), shipping no Lean |
| CC-DECODE | `BackendResult` decode requiring the inclusion | the decoder is the leaf's (`KernelDecode.lean`, a `backendOperation` row's `decoder`), so a leaf decides how its own answer is read; the actual Sage bridge (`Backends/Sage.lean`, `backends/sage_adapter.py`) decodes into CasDsl `Value`s, not semantic results | decode for every backend operation into its semantic result type |
| CC-ROUTE (capabilities against semantic operations) | fused implementations keyed by `method ∘ route`; `Route.realizes` | `Std.lean` still keys ~60 routes by method *name* and presentation pattern | all execution keyed by registered semantic operations |
| CC-LIFT | `MonoLift`, `returnsToSource`, `missingLift` | — | lifts other than monomorphisms (cartesian lifts, adjunction-induced, limit preservation) |
| CC-CLOSURE | `RegistryState.closure`, `#methods` | the notebook's method surface is the union of the registry and `Std.lean`'s declarations | notebook completion and docs from the closure only |
| CC-LAWS | no registration evaluates a law | — | — |
| Gate | — | `just build` does not compile the `CasCatalogue/*Probes.lean` acceptance files | probes in the gate |

## Leaf contract (§5)

A leaf is a registration (operation id, input form, opaque implementation), and nothing from it is
trusted. The code differs in two ways. The permitted `LeafContribution` kinds carry what a leaf
may never supply: denotation functors, proofs of its own actions, identifications, evidence and
statuses. And the forbidden list is enforced *only* for contributions passed through
`register_leaf`, which nothing outside `AdapterProbes` uses. In practice a leaf today can: invent a
category (`normalized_registry .category`), attach methods, declare structural functors, and —
through CasDsl — type presentations into categories and register executors by name.

## Consequence for step 3

The design nodes fall into three groups, in dependency order:

1. **One layer.** Notebook values are semantic points built by registered constructors;
   typing by presentation pattern, `Semantic.encode`, the `Std.lean` route table and the
   `Native.lean` executors are removed in favour of registered operations and opaque leaf
   computations against their declared types. Every leaf (the existing `CasCatalogue/Leaves/*`
   included) is such a registration and holds no authority. Probes enter the gate.
2. **The calculus.** Natural transformations as registered cells with inverses; comparisons applied
   to data; limits/colimits/adjunctions/equivalences/comma/`Op` as registered constructions with
   complete universal data; general fibrations; lifts beyond monomorphisms; same-object refinement;
   category-owned equality; memoization in the resolver; the registry axioms replaced by
   constructions.
3. **Real backends.** Sage and GAP adapters decoding into semantic results, exercised by a hostile
   leaf with the research repository's mistakes.
