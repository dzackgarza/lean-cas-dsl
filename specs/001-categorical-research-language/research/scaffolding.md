# Structural scaffolding of the categories of lean-categories `main` (443fba9)

Snapshot. Source: the export `main-snapshots/lean-categories` of lean-categories `main` at `443fba9` (2026-11-25). Compared with: `main-snapshots/lean-cas-dsl-leaf-contracts/api/declared-ports.json` (mathematics revision `3f8aedf`) and the section "Computational milestones" of `specs/001-categorical-research-language/plan.md` of lean-cas-dsl. The machine-readable form of this document is `scaffolding.json` in the same directory.

Path abbreviation: `S/` = `LeanCategories/Catalogue/Semantics/`. A line number of a row is the line of its `normalized_registry` command.

**Method.** No Lean was run. A script read every `normalized_registry` command of the source and followed the `def` chains of its identifiers and category expressions. Items marked **INFERENCE** are not read facts. The list is in [Inferences](#inferences).

## Result in short

| Quantity | Value |
| --- | --- |
| Registered categories (`.category` rows) | 100 |
| Categories that reach `cat.sets` (with `cat.sets`) | 49 |
| Categories that do not reach `cat.sets` | 51 |
| Edges: structural functor rows | 49 |
| Edges: classifier forgets | 13 |
| Edges: derived images under `Arr` and `Core` | 28 |
| Largest layer | 11 |
| Registry rows in `main` | 675 |
| Registry rows in the published catalogue | 608 |

- The layers of all 96 categories of the published catalogue are the same in `main`. The 4 new categories do not reach `cat.sets`.
- The layer table of plan.md has no wrong layer. It omits 7 categories of layers 1 to 7, and it does not say that half of the registered categories have no layer.
- `cat.rings` reaches `cat.groups`. The category list of "Leaves 0.2" in plan.md does not contain groups.
- `cat.modules_r` does not reach `cat.rings`. Modules and rings are independent above `cat.additive_groups`.
- One cycle contains `cat.sets`: `cat.sets` ⇄ `cat.subobjects_sets`.

## Criterion

### How lean-categories marks the facts

| Fact | Where |
| --- | --- |
| A functor row has the field `structural : Bool := false`. The doc comment: true only for a functor that sends an object to its *underlying* object (forgetful functor, inclusion, fibre inclusion). Construction functors and the projection of a fibration to its base are not structural. | `LeanCategories/Catalogue/Registry/Entry.lean:505-520` (field at 519) |
| A classifier row has `id`, `declaration`, `host : CategoryExpr`, `realization`. There is no separate row for its forget. | `Entry.lean:497-502` |
| A category row has `id`, `declaration`, `expression : CategoryExpr`, `realization`, `name`. | `Entry.lean:469-480` |
| A category expression is `atom`, `construct`, `familyApp`, `familyTotal`, `classifierTotal`, `refine` or `opaque`. | `LeanCategories/Catalogue/Syntax.lean:258-271` |
| One step of a structural route is `functor id`, `classifierForget id` or `constructMap constructor inner`. | `Entry.lean:43-49` |
| **The structural edges.** `SemanticState.structuralEdges` = the functor rows with `structural`, and, for each *category row* whose expression is `.classifierTotal c` with `c` registered, the edge `classifierTotal c → host(c)`. | `LeanCategories/Catalogue/Registry/Semantic.lean:1681-1693` |
| **Derived edges.** `SemanticState.edgesFrom`: at `k(A)`, for a unary constructor `k` with a registered action on functors, the edge `k(U) : k(A) → k(B)` for each structural edge `U : A → B`. | `Semantic.lean:1698-1714` |
| The constructors with an action on functors are `ctor.arrow` and `ctor.core`. | `S/ConstructorRegistration.lean:86-99` |
| A structural functor that is definitionally a composite of other structural edges is refused. A structural row is thus an immediate edge. | `Semantic.lean:1916-1927` (`validateImmediateFunctor`) |
| Expressions are compared by exact syntax (`CategoryExpr.syntacticEq`). | `Syntax.lean:334-352` |
| Rows enter the registry only through the command `normalized_registry`. | `Semantic.lean:3084-3106` |

### How the JSON catalogue encodes the same facts

| Fact | Where in `declared-ports.json` | Exporter |
| --- | --- | --- |
| `structural` of a functor | Only in `entries[*].registeredMetadata`, the `Repr` text of the row (`structural := true`). The rows of the key `functors` have no such field. | `tools/export_declared_ports.lean:103-115`, `161-181` |
| Expression of a category | `categories[*].expression` and `entries[*].registeredMetadata` | `tools/export_declared_ports.lean:116-120` |
| Host of a classifier | `entries[*].registeredMetadata` (`host := …`) | `tools/export_declared_ports.lean:103-115` |
| `edgeActions` | One row for the forget of *each* classifier row (26, of which 14 have no category row for their total) and 11 rows `constructorMap`. This is the address list of the kernel. It is not the list of structural edges (12 forgets and 27 derived images at that revision). | `tools/export_admission_addresses.lean:19-25`, `51-61` |

### The criterion used here

An **edge** is one of:

1. a functor row with `structural := true`, from its `source` to its `target`;
2. a classifier forget `classifierTotal c → host(c)`, when a category row has the expression `.classifierTotal c`;
3. a derived image `k(U) : k(A) → k(B)` of an edge `U`, for `k` = `ctor.arrow` or `ctor.core`.

A **node** is a category expression. Two nodes are equal when their expressions are equal. The **layer** of a category is the number of edges of the longest chain to `cat.sets`. The outgoing edges of `cat.sets` are cut for this computation. A category with no chain to `cat.sets` has no layer. `reaches` is computed with the same cut.

A category of the form `refine base c`, a constructed category, an opaque category and a fibre of a family get no edge from their expression. They have an edge only when a structural functor row exists.

## Layer table

| Layer | Categories |
| --- | --- |
| 0 | `cat.sets` |
| 1 | `cat.additive_monoids`, `cat.boolean_algebras`, `cat.countable_sets`, `cat.enumerated_sets`, `cat.finite_sets`, `cat.magmas`, `cat.partial_orders`, `cat.pointed_sets`, `cat.slice_sets`, `cat.subobjects_sets` |
| 2 | `cat.additive_commutative_monoids`, `cat.linear_orders`, `cat.semigroups`, `cat.subobjects_modules_r` |
| 3 | `cat.hausdorff_topological_commutative_monoids`, `cat.monoids` |
| 4 | `cat.commutative_monoids`, `cat.groups`, `cat.semirings` |
| 5 | `cat.additive_groups`, `cat.subobjects_groups` |
| 6 | `cat.modules_total`, `cat.rings` |
| 7 | `cat.commutative_rings`, `cat.division_rings`, `cat.module_points`, `cat.modules_r` |
| 8 | `cat.algebras`, `cat.based_module_indexed`, `cat.bil_wform`, `cat.coord`, `cat.fields`, `cat.finite_projective_lattice`, `cat.finitelygeneratedmodules`, `cat.finiterankmodules`, `cat.free_cover_indexed`, `cat.freemodules`, `cat.quad_module`, `cat.quad_wform`, `cat.quotients_modules_r`, `cat.torsion_free_modules` |
| 9 | `cat.bilin_module` |
| 10 | `cat.alternating_forms`, `cat.integral_lattice`, `cat.lattice`, `cat.subobjects_bilin_module` |
| 11 | `cat.coord_lattice`, `cat.fraction_field_perfect_finite_projective_lattice` |
| none | 51 categories, see [Categories that do not reach `cat.sets`](#categories-that-do-not-reach-catsets) |

Each category that reaches `cat.sets`, with its immediate targets:

| Layer | Category | Immediate edges |
| --- | --- | --- |
| 0 | `cat.sets` | `fun.sets.whole_subset` → `cat.subobjects_sets` |
| 1 | `cat.additive_monoids` | `fun.additive_monoids.underlying` → `cat.sets` |
| 1 | `cat.boolean_algebras` | `fun.boolean_algebras.forget` → `cat.sets` |
| 1 | `cat.countable_sets` | `forget[clf.sets.countable]` → `cat.sets` |
| 1 | `cat.enumerated_sets` | `forget[clf.sets.enumerated]` → `cat.sets` |
| 1 | `cat.finite_sets` | `forget[clf.sets.finite]` → `cat.sets` |
| 1 | `cat.magmas` | `forget[clf.sets.binary_operation]` → `cat.sets` |
| 1 | `cat.partial_orders` | `fun.partial_orders.forget` → `cat.sets` |
| 1 | `cat.pointed_sets` | `fun.pointed_sets.projection` → `cat.sets` |
| 1 | `cat.slice_sets` | `fun.slice_sets.forget` → `cat.sets` |
| 1 | `cat.subobjects_sets` | `fun.subobjects_sets.domain` → `cat.sets` |
| 2 | `cat.additive_commutative_monoids` | `fun.additive_commutative_monoids.additive_monoid` → `cat.additive_monoids` |
| 2 | `cat.linear_orders` | `fun.linear_orders.forget` → `cat.sets`; `fun.linear_orders.to_partial_orders` → `cat.partial_orders` |
| 2 | `cat.semigroups` | `forget[clf.magmas.associative]` → `cat.magmas` |
| 2 | `cat.subobjects_modules_r` | `fun.subobjects_modules.forget` → `cat.subobjects_sets` |
| 3 | `cat.hausdorff_topological_commutative_monoids` | `fun.hausdorff_topological_commutative_monoids.additive_commutative_monoid` → `cat.additive_commutative_monoids` |
| 3 | `cat.monoids` | `fun.monoids.semigroup` → `cat.semigroups` |
| 4 | `cat.commutative_monoids` | `fun.commutative_monoids.monoid` → `cat.monoids` |
| 4 | `cat.groups` | `fun.groups.monoid` → `cat.monoids` |
| 4 | `cat.semirings` | `fun.semirings.monoid` → `cat.monoids`; `fun.semirings.forget` → `cat.sets` |
| 5 | `cat.additive_groups` | `fun.additive_groups.additive_monoid` → `cat.additive_monoids`; `fun.additive_groups.to_groups` → `cat.groups` |
| 5 | `cat.subobjects_groups` | `fun.subobjects_groups.domain` → `cat.groups` |
| 6 | `cat.modules_total` | `fun.modules.additive_group` → `cat.additive_groups` |
| 6 | `cat.rings` | `fun.rings.additive_commutative_monoid` → `cat.additive_commutative_monoids`; `fun.rings.semiring` → `cat.semirings`; `fun.rings.multiplicative_monoid` → `cat.monoids`; `fun.rings.additive_group` → `cat.additive_groups` |
| 7 | `cat.commutative_rings` | `fun.commutative_rings.ring` → `cat.rings`; `fun.commutative_rings.multiplicative_commutative_monoid` → `cat.commutative_monoids` |
| 7 | `cat.division_rings` | `forget[clf.division]` → `cat.rings` |
| 7 | `cat.module_points` | `fun.module_points.projection` → `cat.modules_total` |
| 7 | `cat.modules_r` | `fun.modules.fibre_inclusion` → `cat.modules_total` |
| 8 | `cat.algebras` | `fun.algebras.forget` → `cat.commutative_rings` |
| 8 | `cat.based_module_indexed` | `fun.based_module.forget` → `cat.modules_r` |
| 8 | `cat.bil_wform` | `fun.bil_wform.carrier` → `cat.modules_r` |
| 8 | `cat.coord` | `fun.coord.forget` → `cat.modules_r` |
| 8 | `cat.fields` | `forget[clf.commutative_rings.field]` → `cat.commutative_rings` |
| 8 | `cat.finite_projective_lattice` | `fun.finite_projective_lattice.forget` → `cat.modules_r` |
| 8 | `cat.finitelygeneratedmodules` | `forget[clf.modules_finitelygenerated]` → `cat.modules_r` |
| 8 | `cat.finiterankmodules` | `forget[clf.modules_finiterank]` → `cat.modules_r` |
| 8 | `cat.free_cover_indexed` | `fun.free_cover.forget` → `cat.modules_r` |
| 8 | `cat.freemodules` | `forget[clf.modules_free]` → `cat.modules_r` |
| 8 | `cat.quad_module` | `fun.quad_module.forget` → `cat.modules_r` |
| 8 | `cat.quad_wform` | `fun.quad_wform.carrier` → `cat.modules_r` |
| 8 | `cat.quotients_modules_r` | `fun.quotients_modules.codomain` → `cat.modules_r` |
| 8 | `cat.torsion_free_modules` | `forget[clf.modules.torsion_free]` → `cat.modules_r` |
| 9 | `cat.bilin_module` | `fun.bilin_module.forget` → `cat.modules_r`; `fun.bilin_module.fixed_value` → `cat.bil_wform` |
| 10 | `cat.alternating_forms` | `forget[clf.bilin_module.alternating]` → `cat.bilin_module` |
| 10 | `cat.integral_lattice` | `fun.integral_lattice.forget_form` → `cat.bilin_module` |
| 10 | `cat.lattice` | `fun.lattice.forget_form` → `cat.bilin_module` |
| 10 | `cat.subobjects_bilin_module` | `fun.subobjects_bilin_module.domain` → `cat.bilin_module` |
| 11 | `cat.coord_lattice` | `fun.coord_lattice.to_coord` → `cat.coord`; `fun.coord_lattice.to_integral` → `cat.integral_lattice` |
| 11 | `cat.fraction_field_perfect_finite_projective_lattice` | `fun.fraction_field_perfect_finite_projective_lattice.forget` → `cat.integral_lattice` |

Remarks on the layers.

- `cat.subobjects_modules_r` has layer 2 and `cat.modules_r` has layer 7. `Sub(Mod_R)` reaches `Sub(Sets)` by the structural `fun.subobjects_modules.forget`. Its functor to `cat.modules_r`, `fun.subobjects_modules.domain`, is not structural (`S/Modules/Operations.lean:616`).
- `cat.modules_r` gets layer 7 from `cat.modules_total` → `cat.additive_groups`. It has a ring parameter, and it has no edge to `cat.rings`.
- `cat.semirings` and `cat.linear_orders` each have a direct edge to `cat.sets` and a longer chain. The layer is that of the longer chain.

## Cycles

| Cycle | Edges | Effect |
| --- | --- | --- |
| `cat.sets` ⇄ `cat.subobjects_sets` | `fun.sets.whole_subset` (`S/Foundation/Subsets.lean:178`), `fun.subobjects_sets.domain` (`S/Foundation/Subsets.lean:185`) | The outgoing edge of `cat.sets` is cut. `cat.subobjects_sets` has layer 1. |
| `cat.core_sets` ⇄ `cat.core_subobjects_sets` | `ctor.core(fun.sets.whole_subset)`, `ctor.core(fun.subobjects_sets.domain)` | Derived from the first cycle. Neither category reaches `cat.sets`. |
| `cat.arrows_sets` ⇄ `Arr(cat.subobjects_sets)` (no category row) | `ctor.arrow(fun.sets.whole_subset)`, `ctor.arrow(fun.subobjects_sets.domain)` | Derived from the first cycle. Neither node reaches `cat.sets`. |

There is no other cycle. The 49 categories that reach `cat.sets` form an acyclic graph after the cut (checked by `scaffolding_verify_layers.py`).

## Categories that do not reach `cat.sets`

51 categories. The columns "structural edges" and "other functors out" are read facts. The column "inferred layer" is an **INFERENCE**: it adds, as dependencies, the category arguments of a constructor, the base of a refinement and the host of its classifier, the targets of opaque ports, and the categories of the family parameters. A dash means that these inputs give no chain to `cat.sets` either.

**Images of `Arr` and `Core`: their edges stay among such images** (11)

| Category | Expression | Structural edges | Other functors out | Owned rows | Inferred layer |
| --- | --- | --- | --- | --- | --- |
| `cat.arrows_bilin_module` | `arrow(cat.bilin_module)` | `ctor.arrow(fun.bilin_module.forget)` → `cat.arrows_modules_r`; `ctor.arrow(fun.bilin_module.fixed_value)` → `arrow(cat.bil_wform)` | — | 2 lifts | 11 |
| `cat.arrows_groups` | `arrow(cat.groups)` | `ctor.arrow(fun.groups.monoid)` → `arrow(cat.monoids)` | `fun.arrows_groups.codomain` → `cat.groups`; `fun.arrows_groups.kernel` → `cat.subobjects_groups` | 1 method | 6 |
| `cat.arrows_modules_r` | `arrow(cat.modules_r)` | `ctor.arrow(fun.modules.fibre_inclusion)` → `arrow(cat.modules_total)` | `fun.arrows_modules.cokernel` → `cat.quotients_modules_r`; `fun.arrows_modules.image` → `cat.subobjects_modules_r`; `fun.arrows_modules.coimage` → `cat.quotients_modules_r`; `fun.arrows_modules.coimage_image_comparison` → `cat.arrows_modules_r`; `fun.arrows_modules.kernel` → `cat.subobjects_modules_r` | 6 methods | 9 |
| `cat.arrows_sets` | `arrow(cat.sets)` | `ctor.arrow(fun.sets.whole_subset)` → `arrow(cat.subobjects_sets)` | — | — | 2 |
| `cat.core_groups` | `core(cat.groups)` | `ctor.core(fun.groups.monoid)` → `core(cat.monoids)` | `fun.core_groups.automorphisms` → `cat.groups`; `fun.core_groups.endomorphisms` → `cat.monoids`; `fun.core_groups.centers` → `cat.subobjects_groups` | — | 6 |
| `cat.core_modules_r` | `core(cat.modules_r)` | `ctor.core(fun.modules.fibre_inclusion)` → `core(cat.modules_total)` | `fun.core_modules_r.automorphisms` → `cat.groups`; `fun.core_modules_r.endomorphisms` → `cat.monoids`; `fun.modules.annihilator` → `cat.ideals_r`; `fun.modules.rank` → `cat.cardinals` | — | 9 |
| `cat.core_pointed_sets` | `core(cat.pointed_sets)` | `ctor.core(fun.pointed_sets.projection)` → `cat.core_sets` | `fun.core_pointed_sets.stabilizer` → `cat.subobjects_groups` | — | 3 |
| `cat.core_sets` | `core(cat.sets)` | `ctor.core(fun.sets.whole_subset)` → `cat.core_subobjects_sets` | `fun.core_sets.automorphisms` → `cat.groups`; `fun.core_sets.endomorphisms` → `cat.monoids`; `fun.sets.cardinality` → `cat.cardinals`; `fun.core_sets.two_subsets` → `cat.sets` | 2 morphisms | 2 |
| `cat.core_subobjects_modules_r` | `core(cat.subobjects_modules_r)` | `ctor.core(fun.subobjects_modules.forget)` → `cat.core_subobjects_sets` | `fun.subobjects_modules.rank` → `cat.cardinals` | — | 9 |
| `cat.core_subobjects_sets` | `core(cat.subobjects_sets)` | `ctor.core(fun.subobjects_sets.domain)` → `cat.core_sets` | `fun.subsets.point_predicates` → `cat.sets`; `fun.subsets.subset_predicates` → `cat.sets`; `fun.subsets.contains` → `cat.subsets.point_predicates`; `fun.subsets.set_eq` → `cat.subsets.subset_predicates` | — | 2 |
| `cat.core_well_ordered_sets` | `core(cat.well_ordered_sets)` | `ctor.core(forget[clf.linear_orders.well_ordered])` → `core(cat.totally_ordered_sets)` | `fun.well_ordered_sets.order_type` → `cat.ordinals` | — | — |

**Other constructed categories with no structural functor row** (6)

| Category | Expression | Structural edges | Other functors out | Owned rows | Inferred layer |
| --- | --- | --- | --- | --- | --- |
| `cat.coslice_sets` | `coslice(cat.sets, X)` | — | — | — | 1 |
| `cat.endofunctors_sets` | `functor_category(cat.sets, cat.sets)` | — | — | — | 1 |
| `cat.schemes_over` | `slice(cat.schemes, X)` | — | — | — | — |
| `cat.sets.pair_diagrams` | `functor_category(cat.walking_pair, cat.sets)` | — | `fun.sets.pair_limit` → `cat.sets` | — | 1 |
| `cat.subsets.point_predicates` | `elements(cat.core_subobjects_sets, fun.subsets.point_predicates)` | — | — | — | 3 |
| `cat.subsets.subset_predicates` | `elements(cat.core_subobjects_sets, fun.subsets.subset_predicates)` | — | — | — | 3 |

**Refinements `refine base c`** (7)

| Category | Expression | Structural edges | Other functors out | Owned rows | Inferred layer |
| --- | --- | --- | --- | --- | --- |
| `cat.even_integral_lattices` | `refine(cat.integral_lattices, clf.bilin_forms.even)` | — | — | — | 10 |
| `cat.finite_free_lattices_over_rings` | `refine(cat.finite_projective_lattices_over_rings, clf.bilin_forms.free)` | — | — | — | — |
| `cat.finite_projective_lattices_over_rings` | `refine(cat.lattices_over_rings, clf.bilin_forms.finite)` | — | `fun.finite_projective_lattices.to_bil` → `cat.bilin_forms_over_rings` | — | — |
| `cat.integral_forms` | `refine(cat.commutative_rings, clf.bilin_forms.values)` | `fun.integral_forms.to_bil` → `cat.bilin_forms_over_rings` | — | — | 8 |
| `cat.integral_lattices` | `refine(cat.integral_forms, clf.bilin_forms.lattice)` | — | `fun.integral_lattices.to_bil` → `cat.bilin_forms_over_rings` | — | 9 |
| `cat.lattices_over_rings` | `refine(cat.bilin_forms_over_rings, clf.bilin_forms.lattice)` | — | `fun.lattices_over_rings.to_bil` → `cat.bilin_forms_over_rings` | — | — |
| `cat.unimodular_lattices_over_rings` | `refine(cat.lattices_over_rings, clf.bilin_forms.unimodular)` | — | — | — | — |

**Atoms with no chain** (17)

| Category | Expression | Structural edges | Other functors out | Owned rows | Inferred layer |
| --- | --- | --- | --- | --- | --- |
| `cat.additive_magmas` | `atom` | — | — | — | — |
| `cat.additive_semigroups` | `atom` | — | — | — | — |
| `cat.bilin_forms_over_rings` | `atom` | — | `fun.bilin_forms.values` → `cat.modules_over_rings_ext` | — | — |
| `cat.cardinalities` | `atom` | — | — | — | — |
| `cat.cardinals` | `atom` | `fun.cardinals.to_cardinalities` → `cat.cardinalities` | — | — | — |
| `cat.cusps` | `atom` | — | `fun.cusps.orbits` → `cat.sets` | 1 object, 1 morphism | — |
| `cat.definite_lattice` | `atom` | — | — | — | — |
| `cat.enumerated_monotone_sets` | `atom` | — | `fun.enumerated_monotone_sets.enumerated` → `cat.enumerated_sets`; `fun.enumerated_monotone_sets.well_ordered_sets` → `cat.well_ordered_sets` | — | — |
| `cat.ideals_r` | `atom` | — | — | — | — |
| `cat.indefinite_lattice` | `atom` | — | — | — | — |
| `cat.modules_over_rings_ext` | `atom` | — | `fun.modules_ext.ring` → `cat.commutative_rings` | — | — |
| `cat.ordinals` | `atom` | — | `fun.ordinals.card` → `cat.cardinalities` | 7 objects, 4 morphisms | — |
| `cat.partially_ordered_sets` | `atom` | — | `fun.sets.partially_ordered_to_sets` → `cat.sets` | — | — |
| `cat.quad_forms_over_rings` | `atom` | — | `fun.quad_forms.ring` → `cat.commutative_rings` | — | — |
| `cat.schemes` | `atom` | — | — | 1 object | — |
| `cat.totally_ordered_sets` | `atom` | — | `fun.sets.totally_ordered_to_sets` → `cat.sets` | — | — |
| `cat.walking_pair` | `atom` | — | — | — | — |

**Fibres of a family with no chain** (7)

| Category | Expression | Structural edges | Other functors out | Owned rows | Inferred layer |
| --- | --- | --- | --- | --- | --- |
| `cat.based_module` | `fam.based_module[R, n]` | `fun.based_module.to_free_cover` → `cat.free_cover` | `fun.coord.from_based_module` → `cat.coord` | — | 9 |
| `cat.coord_indexed` | `fam.coord_indexed[R, I]` | — | — | — | 8 |
| `cat.even_lattice` | `fam.even_lattice[R]` | — | — | — | 8 |
| `cat.finite_free_lattice` | `fam.finite_free_lattice[R, W]` | — | — | — | 8 |
| `cat.free_cover` | `fam.free_cover[R, n]` | — | — | — | 8 |
| `cat.schemes_over_ring` | `family.schemes_over_ring[R]` | — | — | 2 objects | 8 |
| `cat.unimodular_lattice` | `fam.unimodular_lattice[R, domain]` | — | — | — | 8 |

**Classifier total with a host that has no chain** (1)

| Category | Expression | Structural edges | Other functors out | Owned rows | Inferred layer |
| --- | --- | --- | --- | --- | --- |
| `cat.well_ordered_sets` | `total(clf.linear_orders.well_ordered)` | `forget[clf.linear_orders.well_ordered]` → `cat.totally_ordered_sets` | `fun.well_ordered_sets.linear_order` → `cat.totally_ordered_sets`; `fun.well_ordered_sets.sets` → `cat.sets` | — | — |

**Opaque categories (their ports are not edges)** (2)

| Category | Expression | Structural edges | Other functors out | Owned rows | Inferred layer |
| --- | --- | --- | --- | --- | --- |
| `cat.crystals` | `opaque` | — | — | — | 1 |
| `cat.magmaswithtwooperations` | `opaque` | — | — | — | 2 |

Classifier rows with no category row for their total (no forget edge exists for them): `clf.bilin_forms.values`, `clf.bilin_forms.lattice`, `clf.bilin_forms.finite`, `clf.bilin_forms.free`, `clf.bilin_forms.even`, `clf.bilin_forms.unimodular`, `clf.bilin_module.lattice`, `clf.magmas.commutative`, `clf.magmas.unital`, `clf.magmas.inverse`, `clf.magmas.additive`, `clf.magmas.multiplicative`, `clf.sets.graded`, `clf.magmaswithtwooperations.distributive`.

## Immediate edges

### Structural functor rows (49)

| Functor | Source | Target | Row |
| --- | --- | --- | --- |
| `fun.sets.whole_subset` | `cat.sets` | `cat.subobjects_sets` | `S/Foundation/Subsets.lean:178` |
| `fun.additive_monoids.underlying` | `cat.additive_monoids` | `cat.sets` | `S/Algebra/CatalogueRegistration.lean:174` |
| `fun.boolean_algebras.forget` | `cat.boolean_algebras` | `cat.sets` | `S/Foundation/PowerSets.lean:321` |
| `fun.partial_orders.forget` | `cat.partial_orders` | `cat.sets` | `S/Foundation/PowerSets.lean:333` |
| `fun.pointed_sets.projection` | `cat.pointed_sets` | `cat.sets` | `S/Algebra/Automorphisms.lean:507` |
| `fun.slice_sets.forget` | `cat.slice_sets` | `cat.sets` | `S/ConstructorRegistration.lean:153` |
| `fun.subobjects_sets.domain` | `cat.subobjects_sets` | `cat.sets` | `S/Foundation/Subsets.lean:185` |
| `fun.additive_commutative_monoids.additive_monoid` | `cat.additive_commutative_monoids` | `cat.additive_monoids` | `S/Algebra/CommutativeMonoids.lean:179` |
| `fun.linear_orders.forget` | `cat.linear_orders` | `cat.sets` | `S/Foundation/PowerSets.lean:327` |
| `fun.linear_orders.to_partial_orders` | `cat.linear_orders` | `cat.partial_orders` | `S/Foundation/PowerSets.lean:339` |
| `fun.subobjects_modules.forget` | `cat.subobjects_modules_r` | `cat.subobjects_sets` | `S/Modules/Operations.lean:610` |
| `fun.hausdorff_topological_commutative_monoids.additive_commutative_monoid` | `cat.hausdorff_topological_commutative_monoids` | `cat.additive_commutative_monoids` | `S/Algebra/Series.lean:449` |
| `fun.monoids.semigroup` | `cat.monoids` | `cat.semigroups` | `S/Algebra/Ports.lean:121` |
| `fun.commutative_monoids.monoid` | `cat.commutative_monoids` | `cat.monoids` | `S/Algebra/CommutativeMonoids.lean:172` |
| `fun.groups.monoid` | `cat.groups` | `cat.monoids` | `S/Algebra/Ports.lean:115` |
| `fun.semirings.forget` | `cat.semirings` | `cat.sets` | `S/Algebra/Semirings.lean:171` |
| `fun.semirings.monoid` | `cat.semirings` | `cat.monoids` | `S/Algebra/ComputationDerivations.lean:147` |
| `fun.additive_groups.additive_monoid` | `cat.additive_groups` | `cat.additive_monoids` | `S/Algebra/AdditiveOperations.lean:83` |
| `fun.additive_groups.to_groups` | `cat.additive_groups` | `cat.groups` | `S/Algebra/Ports.lean:109` |
| `fun.subobjects_groups.domain` | `cat.subobjects_groups` | `cat.groups` | `S/Algebra/Subgroups.lean:146` |
| `fun.modules.additive_group` | `cat.modules_total` | `cat.additive_groups` | `S/Modules/CatalogueRegistration.lean:581` |
| `fun.rings.additive_commutative_monoid` | `cat.rings` | `cat.additive_commutative_monoids` | `S/Algebra/CommutativeMonoids.lean:198` |
| `fun.rings.additive_group` | `cat.rings` | `cat.additive_groups` | `S/Algebra/Ports.lean:103` |
| `fun.rings.multiplicative_monoid` | `cat.rings` | `cat.monoids` | `S/Algebra/Ports.lean:97` |
| `fun.rings.semiring` | `cat.rings` | `cat.semirings` | `S/Algebra/ComputationDerivations.lean:138` |
| `fun.commutative_rings.multiplicative_commutative_monoid` | `cat.commutative_rings` | `cat.commutative_monoids` | `S/Algebra/CommutativeMonoids.lean:189` |
| `fun.commutative_rings.ring` | `cat.commutative_rings` | `cat.rings` | `S/Algebra/Algebras.lean:118` |
| `fun.module_points.projection` | `cat.module_points` | `cat.modules_total` | `S/ConstructorRegistration.lean:163` |
| `fun.modules.fibre_inclusion` | `cat.modules_r` | `cat.modules_total` | `S/Modules/CatalogueRegistration.lean:554` |
| `fun.algebras.forget` | `cat.algebras` | `cat.commutative_rings` | `S/Algebra/Algebras.lean:132` |
| `fun.based_module.forget` | `cat.based_module_indexed` | `cat.modules_r` | `S/Modules/CatalogueRegistration.lean:539` |
| `fun.bil_wform.carrier` | `cat.bil_wform` | `cat.modules_r` | `S/Modules/Bilinear/Valued/CatalogueRegistration.lean:203` |
| `fun.coord.forget` | `cat.coord` | `cat.modules_r` | `S/Modules/CatalogueRegistration.lean:522` |
| `fun.finite_projective_lattice.forget` | `cat.finite_projective_lattice` | `cat.modules_r` | `S/Lattices/Valued/CatalogueRegistration.lean:547` |
| `fun.free_cover.forget` | `cat.free_cover_indexed` | `cat.modules_r` | `S/Modules/CatalogueRegistration.lean:530` |
| `fun.quad_module.forget` | `cat.quad_module` | `cat.modules_r` | `S/Modules/Quadratic/Valued/CatalogueRegistration.lean:161` |
| `fun.quad_wform.carrier` | `cat.quad_wform` | `cat.modules_r` | `S/Modules/Quadratic/Valued/CatalogueRegistration.lean:194` |
| `fun.quotients_modules.codomain` | `cat.quotients_modules_r` | `cat.modules_r` | `S/Modules/Operations.lean:574` |
| `fun.bilin_module.fixed_value` | `cat.bilin_module` | `cat.bil_wform` | `S/Modules/Bilinear/Valued/Transport.lean:70` |
| `fun.bilin_module.forget` | `cat.bilin_module` | `cat.modules_r` | `S/Modules/Bilinear/Valued/CatalogueRegistration.lean:192` |
| `fun.integral_lattice.forget_form` | `cat.integral_lattice` | `cat.bilin_module` | `S/Lattices/Valued/CatalogueRegistration.lean:557` |
| `fun.lattice.forget_form` | `cat.lattice` | `cat.bilin_module` | `S/Lattices/Valued/CatalogueRegistration.lean:510` |
| `fun.subobjects_bilin_module.domain` | `cat.subobjects_bilin_module` | `cat.bilin_module` | `S/Modules/Bilinear/Valued/Kernels.lean:281` |
| `fun.coord_lattice.to_coord` | `cat.coord_lattice` | `cat.coord` | `S/Lattices/Valued/CatalogueRegistration.lean:566` |
| `fun.coord_lattice.to_integral` | `cat.coord_lattice` | `cat.integral_lattice` | `S/Lattices/Valued/CatalogueRegistration.lean:576` |
| `fun.fraction_field_perfect_finite_projective_lattice.forget` | `cat.fraction_field_perfect_finite_projective_lattice` | `cat.integral_lattice` | `S/Lattices/Valued/CatalogueRegistration.lean:586` |
| `fun.based_module.to_free_cover` | `cat.based_module` | `cat.free_cover` | `S/Modules/CatalogueRegistration.lean:506` |
| `fun.cardinals.to_cardinalities` | `cat.cardinals` | `cat.cardinalities` | `S/Foundation/Cardinality.lean:137` |
| `fun.integral_forms.to_bil` | `cat.integral_forms` | `cat.bilin_forms_over_rings` | `S/FibrationRegistration.lean:311` |

### Classifier forgets (13)

| Classifier | Source (the total) | Target (the host) | Classifier row | Category row of the total |
| --- | --- | --- | --- | --- |
| `clf.bilin_module.alternating` | `cat.alternating_forms` | `cat.bilin_module` | `S/Modules/Bilinear/Valued/Alternating.lean:60` | `S/Modules/Bilinear/Valued/Alternating.lean:65` |
| `clf.commutative_rings.field` | `cat.fields` | `cat.commutative_rings` | `S/Algebra/Fields.lean:88` | `S/Algebra/Fields.lean:93` |
| `clf.division` | `cat.division_rings` | `cat.rings` | `S/Exceptional/CatalogueRegistration.lean:127` | `S/Exceptional/CatalogueRegistration.lean:132` |
| `clf.linear_orders.well_ordered` | `cat.well_ordered_sets` | `cat.totally_ordered_sets` | `S/Foundation/WellOrderedSetsRegistration.lean:138` | `S/Foundation/WellOrderedSetsRegistration.lean:145` |
| `clf.magmas.associative` | `cat.semigroups` | `cat.magmas` | `S/Algebra/CatalogueRegistration.lean:102` | `S/Algebra/CatalogueRegistration.lean:138` |
| `clf.modules.torsion_free` | `cat.torsion_free_modules` | `cat.modules_r` | `S/Modules/TorsionFree.lean:53` | `S/Modules/TorsionFree.lean:59` |
| `clf.modules_finitelygenerated` | `cat.finitelygeneratedmodules` | `cat.modules_r` | `S/Modules/CatalogueRegistration.lean:439` | `S/Modules/CatalogueRegistration.lean:464` |
| `clf.modules_finiterank` | `cat.finiterankmodules` | `cat.modules_r` | `S/Modules/CatalogueRegistration.lean:444` | `S/Modules/CatalogueRegistration.lean:469` |
| `clf.modules_free` | `cat.freemodules` | `cat.modules_r` | `S/Modules/CatalogueRegistration.lean:434` | `S/Modules/CatalogueRegistration.lean:459` |
| `clf.sets.binary_operation` | `cat.magmas` | `cat.sets` | `S/Foundation/CatalogueRegistration.lean:121` | `S/Algebra/CatalogueRegistration.lean:133` |
| `clf.sets.countable` | `cat.countable_sets` | `cat.sets` | `S/Foundation/CatalogueRegistration.lean:127` | `S/Foundation/CatalogueRegistration.lean:139` |
| `clf.sets.enumerated` | `cat.enumerated_sets` | `cat.sets` | `S/Foundation/CatalogueRegistration.lean:133` | `S/Foundation/CatalogueRegistration.lean:145` |
| `clf.sets.finite` | `cat.finite_sets` | `cat.sets` | `S/Foundation/CatalogueRegistration.lean:109` | `S/Limits/Lifts.lean:53` |

### Derived images under `Arr` and `Core` (28)

These are computed, never registered. The list holds the images that a category row can reach.

| Edge | Source | Target |
| --- | --- | --- |
| `ctor.arrow(forget[clf.magmas.associative])` | `arrow(cat.semigroups)` | `arrow(cat.magmas)` |
| `ctor.arrow(forget[clf.sets.binary_operation])` | `arrow(cat.magmas)` | `cat.arrows_sets` |
| `ctor.arrow(fun.additive_groups.additive_monoid)` | `arrow(cat.additive_groups)` | `arrow(cat.additive_monoids)` |
| `ctor.arrow(fun.additive_groups.to_groups)` | `arrow(cat.additive_groups)` | `cat.arrows_groups` |
| `ctor.arrow(fun.additive_monoids.underlying)` | `arrow(cat.additive_monoids)` | `cat.arrows_sets` |
| `ctor.arrow(fun.bil_wform.carrier)` | `arrow(cat.bil_wform)` | `cat.arrows_modules_r` |
| `ctor.arrow(fun.bilin_module.fixed_value)` | `cat.arrows_bilin_module` | `arrow(cat.bil_wform)` |
| `ctor.arrow(fun.bilin_module.forget)` | `cat.arrows_bilin_module` | `cat.arrows_modules_r` |
| `ctor.arrow(fun.groups.monoid)` | `cat.arrows_groups` | `arrow(cat.monoids)` |
| `ctor.arrow(fun.modules.additive_group)` | `arrow(cat.modules_total)` | `arrow(cat.additive_groups)` |
| `ctor.arrow(fun.modules.fibre_inclusion)` | `cat.arrows_modules_r` | `arrow(cat.modules_total)` |
| `ctor.arrow(fun.monoids.semigroup)` | `arrow(cat.monoids)` | `arrow(cat.semigroups)` |
| `ctor.arrow(fun.sets.whole_subset)` | `cat.arrows_sets` | `arrow(cat.subobjects_sets)` |
| `ctor.arrow(fun.subobjects_sets.domain)` | `arrow(cat.subobjects_sets)` | `cat.arrows_sets` |
| `ctor.core(forget[clf.linear_orders.well_ordered])` | `cat.core_well_ordered_sets` | `core(cat.totally_ordered_sets)` |
| `ctor.core(forget[clf.magmas.associative])` | `core(cat.semigroups)` | `core(cat.magmas)` |
| `ctor.core(forget[clf.sets.binary_operation])` | `core(cat.magmas)` | `cat.core_sets` |
| `ctor.core(fun.additive_groups.additive_monoid)` | `core(cat.additive_groups)` | `core(cat.additive_monoids)` |
| `ctor.core(fun.additive_groups.to_groups)` | `core(cat.additive_groups)` | `cat.core_groups` |
| `ctor.core(fun.additive_monoids.underlying)` | `core(cat.additive_monoids)` | `cat.core_sets` |
| `ctor.core(fun.groups.monoid)` | `cat.core_groups` | `core(cat.monoids)` |
| `ctor.core(fun.modules.additive_group)` | `core(cat.modules_total)` | `core(cat.additive_groups)` |
| `ctor.core(fun.modules.fibre_inclusion)` | `cat.core_modules_r` | `core(cat.modules_total)` |
| `ctor.core(fun.monoids.semigroup)` | `core(cat.monoids)` | `core(cat.semigroups)` |
| `ctor.core(fun.pointed_sets.projection)` | `cat.core_pointed_sets` | `cat.core_sets` |
| `ctor.core(fun.sets.whole_subset)` | `cat.core_sets` | `cat.core_subobjects_sets` |
| `ctor.core(fun.subobjects_modules.forget)` | `cat.core_subobjects_modules_r` | `cat.core_subobjects_sets` |
| `ctor.core(fun.subobjects_sets.domain)` | `cat.core_subobjects_sets` | `cat.core_sets` |

## Registered categories (100)

"Cat. root" = the row is in the import closure of `LeanCategories.Catalogue`, the module that the exporter of the published catalogue imports. Parameters come from the expression (family schema, slice object, host of a classifier total). Binders are the explicit binders of the Lean declaration; a parameter that a `variable` command declares is not read.

| Layer | Category | Surface name | Expression | Parameters | Binders of the declaration | Row | Cat. root |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | `cat.sets` | Sets | `atom` | — | — | `S/Foundation/CatalogueRegistration.lean:103` | yes |
| 1 | `cat.additive_monoids` | — | `atom` | — | — | `S/Algebra/CatalogueRegistration.lean:163` | yes |
| 1 | `cat.boolean_algebras` | BooleanAlgebras | `atom` | — | — | `S/Foundation/PowerSets.lean:303` | yes |
| 1 | `cat.countable_sets` | CountableSets | `total(clf.sets.countable)` | — | — | `S/Foundation/CatalogueRegistration.lean:139` | yes |
| 1 | `cat.enumerated_sets` | EnumeratedSets | `total(clf.sets.enumerated)` | — | — | `S/Foundation/CatalogueRegistration.lean:145` | yes |
| 1 | `cat.finite_sets` | FiniteSets | `total(clf.sets.finite)` | — | — | `S/Limits/Lifts.lean:53` | yes |
| 1 | `cat.magmas` | — | `total(clf.sets.binary_operation)` | — | — | `S/Algebra/CatalogueRegistration.lean:133` | yes |
| 1 | `cat.partial_orders` | PartialOrders | `atom` | — | — | `S/Foundation/PowerSets.lean:315` | yes |
| 1 | `cat.pointed_sets` | — | `elements(cat.sets, fun.sets.identity)` | — | — | `S/Algebra/Automorphisms.lean:443` | yes |
| 1 | `cat.slice_sets` | — | `slice(cat.sets, X)` | X: object of `cat.sets` | `(X : Type u)` | `S/ConstructorRegistration.lean:126` | yes |
| 1 | `cat.subobjects_sets` | — | `subobjects(cat.sets)` | — | — | `S/ConstructorRegistration.lean:136` | yes |
| 2 | `cat.additive_commutative_monoids` | AdditiveCommutativeMonoids | `atom` | — | — | `S/Algebra/CommutativeMonoids.lean:165` | yes |
| 2 | `cat.linear_orders` | LinearOrders | `atom` | — | — | `S/Foundation/PowerSets.lean:309` | yes |
| 2 | `cat.semigroups` | — | `total(clf.magmas.associative)` | — | — | `S/Algebra/CatalogueRegistration.lean:138` | yes |
| 2 | `cat.subobjects_modules_r` | — | `subobjects(cat.modules_r)` | R: ring object | `(R : RingCat.{u})` | `S/Modules/Bilinear/Valued/Kernels.lean:266` | yes |
| 3 | `cat.hausdorff_topological_commutative_monoids` | HausdorffTopologicalMonoids | `atom` | — | — | `S/Algebra/Series.lean:443` | yes |
| 3 | `cat.monoids` | — | `atom` | — | — | `S/Algebra/CatalogueRegistration.lean:143` | yes |
| 4 | `cat.commutative_monoids` | CommutativeMonoids | `atom` | — | — | `S/Algebra/CommutativeMonoids.lean:159` | yes |
| 4 | `cat.groups` | Groups | `atom` | — | — | `S/Algebra/CatalogueRegistration.lean:148` | yes |
| 4 | `cat.semirings` | Semirings | `atom` | — | — | `S/Algebra/Semirings.lean:165` | yes |
| 5 | `cat.additive_groups` | — | `atom` | — | — | `S/Algebra/CatalogueRegistration.lean:168` | yes |
| 5 | `cat.subobjects_groups` | — | `subobjects(cat.groups)` | — | — | `S/Algebra/Subgroups.lean:136` | yes |
| 6 | `cat.modules_total` | — | `∫ fam.modules` | — | — | `S/Modules/CatalogueRegistration.lean:549` | yes |
| 6 | `cat.rings` | Rings | `atom` | — | — | `S/Exceptional/CatalogueRegistration.lean:117` | yes |
| 7 | `cat.commutative_rings` | CommutativeRings | `atom` | — | — | `S/Exceptional/CatalogueRegistration.lean:122` | yes |
| 7 | `cat.division_rings` | — | `total(clf.division)` | — | — | `S/Exceptional/CatalogueRegistration.lean:132` | yes |
| 7 | `cat.module_points` | — | `elements(cat.modules_total, fun.modules.underlying)` | — | — | `S/ConstructorRegistration.lean:141` | yes |
| 7 | `cat.modules_r` | Modules | `fam.modules[R]` | R: ring object | `(R : RingCat.{u})` | `S/Modules/CatalogueRegistration.lean:450` | yes |
| 8 | `cat.algebras` | Algebras | `coslice(cat.commutative_rings, X)` | X: object of `cat.commutative_rings` | `(K : Algebra.CommutativeRings.{u})` | `S/Algebra/Algebras.lean:126` | yes |
| 8 | `cat.based_module_indexed` | — | `fam.based_module_indexed[R, I]` | R: commutative ring object, I: index type | `(R : Type u) [CommRing R] (I : Type v)` | `S/Modules/CatalogueRegistration.lean:495` | yes |
| 8 | `cat.bil_wform` | BilWForm | `fam.bil_wform[R]` | R: commutative ring object | `(R : Type u) [CommRing R]` | `S/Modules/Bilinear/Valued/CatalogueRegistration.lean:186` | yes |
| 8 | `cat.coord` | — | `fam.coord[R, n]` | R: commutative ring object, n: natural number | `(R : Type u) [CommRing R] (n : Nat)` | `S/Modules/CatalogueRegistration.lean:485` | yes |
| 8 | `cat.fields` | Fields | `total(clf.commutative_rings.field)` | — | — | `S/Algebra/Fields.lean:93` | yes |
| 8 | `cat.finite_projective_lattice` | — | `fam.finite_projective_lattice[R, W]` | R: commutative ring object, W: module object over R | `(R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]` | `S/Lattices/Valued/CatalogueRegistration.lean:453` | yes |
| 8 | `cat.finitelygeneratedmodules` | — | `total(clf.modules_finitelygenerated)` | R: ring object | `(R : RingCat.{u})` | `S/Modules/CatalogueRegistration.lean:464` | yes |
| 8 | `cat.finiterankmodules` | — | `total(clf.modules_finiterank)` | R: ring object | `(R : RingCat.{u})` | `S/Modules/CatalogueRegistration.lean:469` | yes |
| 8 | `cat.free_cover_indexed` | — | `fam.free_cover_indexed[R, I]` | R: commutative ring object, I: index type | `(R : Type u) [CommRing R] (I : Type v)` | `S/Modules/CatalogueRegistration.lean:490` | yes |
| 8 | `cat.freemodules` | — | `total(clf.modules_free)` | R: ring object | `(R : RingCat.{u})` | `S/Modules/CatalogueRegistration.lean:459` | yes |
| 8 | `cat.quad_module` | — | `fam.quad_module[R, W]` | R: commutative ring object, W: module object over R | `(R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]` | `S/Modules/Quadratic/Valued/CatalogueRegistration.lean:148` | yes |
| 8 | `cat.quad_wform` | — | `fam.quad_wform[R]` | R: commutative ring object | `(R : Type u) [CommRing R]` | `S/Modules/Quadratic/Valued/CatalogueRegistration.lean:155` | yes |
| 8 | `cat.quotients_modules_r` | — | `atom` | — | `(R : RingCat.{u})` | `S/Modules/Operations.lean:560` | yes |
| 8 | `cat.torsion_free_modules` | — | `total(clf.modules.torsion_free)` | R: ring object | `(R : RingCat.{u})` | `S/Modules/TorsionFree.lean:59` | yes |
| 9 | `cat.bilin_module` | Bil | `fam.bilin_module[R, W]` | R: commutative ring object, W: module object over R | `(R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]` | `S/Modules/Bilinear/Valued/CatalogueRegistration.lean:179` | yes |
| 10 | `cat.alternating_forms` | AlternatingForms | `total(clf.bilin_module.alternating)` | R: commutative ring object, W: module object over R | `(R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]` | `S/Modules/Bilinear/Valued/Alternating.lean:65` | yes |
| 10 | `cat.integral_lattice` | — | `fam.integral_lattice[R]` | R: commutative ring object | `(R : Type u) [CommRing R]` | `S/Lattices/Valued/CatalogueRegistration.lean:485` | yes |
| 10 | `cat.lattice` | — | `fam.lattice[R, W]` | R: commutative ring object, W: module object over R | `(R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]` | `S/Lattices/Valued/CatalogueRegistration.lean:447` | yes |
| 10 | `cat.subobjects_bilin_module` | — | `subobjects(cat.bilin_module)` | R: commutative ring object, W: module object over R | `(R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]` | `S/Modules/Bilinear/Valued/Kernels.lean:276` | yes |
| 11 | `cat.coord_lattice` | — | `fam.coord_lattice[R, n]` | R: commutative ring object, n: natural number | `(R : Type u) [CommRing R] (n : Nat)` | `S/Lattices/Valued/CatalogueRegistration.lean:490` | yes |
| 11 | `cat.fraction_field_perfect_finite_projective_lattice` | — | `fam.fraction_field_perfect_finite_projective_lattice[R, domain]` | R: commutative ring object, domain: proof that R is a domain | `(R : Type u) [CommRing R] [IsDomain R]` | `S/Lattices/Valued/CatalogueRegistration.lean:495` | yes |
| — | `cat.additive_magmas` | — | `atom` | — | — | `S/Algebra/CatalogueRegistration.lean:153` | yes |
| — | `cat.additive_semigroups` | — | `atom` | — | — | `S/Algebra/CatalogueRegistration.lean:158` | yes |
| — | `cat.arrows_bilin_module` | — | `arrow(cat.bilin_module)` | R: commutative ring object, W: module object over R | `(R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]` | `S/Modules/Bilinear/Valued/Kernels.lean:271` | yes |
| — | `cat.arrows_groups` | — | `arrow(cat.groups)` | — | — | `S/Algebra/Subgroups.lean:141` | yes |
| — | `cat.arrows_modules_r` | — | `arrow(cat.modules_r)` | R: ring object | `(R : RingCat.{u})` | `S/Modules/Bilinear/Valued/Kernels.lean:261` | yes |
| — | `cat.arrows_sets` | — | `arrow(cat.sets)` | — | — | `S/ConstructorRegistration.lean:116` | yes |
| — | `cat.based_module` | — | `fam.based_module[R, n]` | R: commutative ring object, n: natural number | `(R : Type u) [CommRing R] (n : Nat)` | `S/Modules/CatalogueRegistration.lean:480` | yes |
| — | `cat.bilin_forms_over_rings` | — | `atom` | — | — | `S/FibrationRegistration.lean:254` | yes |
| — | `cat.cardinalities` | Cardinalities | `atom` | — | — | `S/Foundation/Cardinality.lean:132` | yes |
| — | `cat.cardinals` | Card | `atom` | — | — | `S/Foundation/Cardinality.lean:127` | yes |
| — | `cat.coord_indexed` | — | `fam.coord_indexed[R, I]` | R: commutative ring object, I: index type | `(R : Type u) [CommRing R] (I : Type v)` | `S/Modules/CatalogueRegistration.lean:500` | yes |
| — | `cat.core_groups` | — | `core(cat.groups)` | — | — | `S/Algebra/Automorphisms.lean:438` | yes |
| — | `cat.core_modules_r` | — | `core(cat.modules_r)` | R: ring object | `(R : RingCat.{u})` | `S/Modules/Rank.lean:69` | yes |
| — | `cat.core_pointed_sets` | — | `core(cat.pointed_sets)` | — | — | `S/Algebra/Automorphisms.lean:448` | yes |
| — | `cat.core_sets` | — | `core(cat.sets)` | — | — | `S/ConstructorRegistration.lean:121` | yes |
| — | `cat.core_subobjects_modules_r` | — | `core(cat.subobjects_modules_r)` | R: ring object | `(R : RingCat.{u})` | `S/Modules/Operations.lean:635` | yes |
| — | `cat.core_subobjects_sets` | — | `core(cat.subobjects_sets)` | — | — | `S/Foundation/Subsets.lean:151` | yes |
| — | `cat.core_well_ordered_sets` | — | `core(cat.well_ordered_sets)` | — | — | `S/Foundation/WellOrderedSetsRegistration.lean:192` | no |
| — | `cat.coslice_sets` | — | `coslice(cat.sets, X)` | X: object of `cat.sets` | `(X : Type u)` | `S/ConstructorRegistration.lean:131` | yes |
| — | `cat.crystals` | — | `opaque` | — | — | `S/Exceptional/CatalogueRegistration.lean:74` | yes |
| — | `cat.cusps` | Cusps | `atom` | — | `(R : Type u) [CommRing R]` | `LeanCategories/Lattices/Valued/Cusps.lean:400` | no |
| — | `cat.definite_lattice` | — | `atom` | — | — | `S/Lattices/Valued/CatalogueRegistration.lean:473` | yes |
| — | `cat.endofunctors_sets` | — | `functor_category(cat.sets, cat.sets)` | — | — | `S/ConstructorRegistration.lean:146` | yes |
| — | `cat.enumerated_monotone_sets` | EnumeratedMonotoneSets | `atom` | — | — | `S/Foundation/WellOrderedSetsRegistration.lean:151` | no |
| — | `cat.even_integral_lattices` | — | `refine(cat.integral_lattices, clf.bilin_forms.even)` | — | — | `S/LatticeRefinements.lean:311` | yes |
| — | `cat.even_lattice` | — | `fam.even_lattice[R]` | R: commutative ring object | `(R : Type u) [CommRing R]` | `S/Lattices/Valued/CatalogueRegistration.lean:467` | yes |
| — | `cat.finite_free_lattice` | — | `fam.finite_free_lattice[R, W]` | R: commutative ring object, W: module object over R | `(R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]` | `S/Lattices/Valued/CatalogueRegistration.lean:461` | yes |
| — | `cat.finite_free_lattices_over_rings` | — | `refine(cat.finite_projective_lattices_over_rings, clf.bilin_forms.free)` | — | — | `S/LatticeRefinements.lean:297` | yes |
| — | `cat.finite_projective_lattices_over_rings` | — | `refine(cat.lattices_over_rings, clf.bilin_forms.finite)` | — | — | `S/LatticeRefinements.lean:282` | yes |
| — | `cat.free_cover` | — | `fam.free_cover[R, n]` | R: commutative ring object, n: natural number | `(R : Type u) [CommRing R] (n : Nat)` | `S/Modules/CatalogueRegistration.lean:475` | yes |
| — | `cat.ideals_r` | — | `atom` | — | `(R : RingCat.{u})` | `S/Modules/Operations.lean:597` | yes |
| — | `cat.indefinite_lattice` | — | `atom` | — | — | `S/Lattices/Valued/CatalogueRegistration.lean:479` | yes |
| — | `cat.integral_forms` | — | `refine(cat.commutative_rings, clf.bilin_forms.values)` | — | — | `S/FibrationRegistration.lean:289` | yes |
| — | `cat.integral_lattices` | — | `refine(cat.integral_forms, clf.bilin_forms.lattice)` | — | — | `S/FibrationRegistration.lean:321` | yes |
| — | `cat.lattices_over_rings` | — | `refine(cat.bilin_forms_over_rings, clf.bilin_forms.lattice)` | — | — | `S/FibrationRegistration.lean:303` | yes |
| — | `cat.magmaswithtwooperations` | — | `opaque` | — | — | `S/Exceptional/CatalogueRegistration.lean:69` | yes |
| — | `cat.modules_over_rings_ext` | — | `atom` | — | — | `S/FibrationRegistration.lean:235` | yes |
| — | `cat.ordinals` | Ordinals | `atom` | — | — | `S/Foundation/Ordinals.lean:143` | yes |
| — | `cat.partially_ordered_sets` | PartiallyOrderedSets | `atom` | — | — | `S/Foundation/CatalogueRegistration.lean:152` | yes |
| — | `cat.quad_forms_over_rings` | — | `atom` | — | — | `S/QuadFibrationRegistration.lean:74` | yes |
| — | `cat.schemes` | Schemes | `atom` | — | — | `S/Algebra/Schemes.lean:99` | yes |
| — | `cat.schemes_over` | SchemesOver | `slice(cat.schemes, X)` | X: object of `cat.schemes` | `(S : schemesCategory.{u})` | `S/Algebra/Schemes.lean:105` | yes |
| — | `cat.schemes_over_ring` | Schemes/ | `family.schemes_over_ring[R]` | R: commutative ring object | `(K : CommRingCat.{u})` | `S/Algebra/Schemes.lean:117` | yes |
| — | `cat.sets.pair_diagrams` | — | `functor_category(cat.walking_pair, cat.sets)` | — | — | `S/Foundation/PairDiagrams.lean:104` | yes |
| — | `cat.subsets.point_predicates` | — | `elements(cat.core_subobjects_sets, fun.subsets.point_predicates)` | — | — | `S/Foundation/Subsets.lean:168` | yes |
| — | `cat.subsets.subset_predicates` | — | `elements(cat.core_subobjects_sets, fun.subsets.subset_predicates)` | — | — | `S/Foundation/Subsets.lean:173` | yes |
| — | `cat.totally_ordered_sets` | TotallyOrderedSets | `atom` | — | — | `S/Foundation/CatalogueRegistration.lean:158` | yes |
| — | `cat.unimodular_lattice` | — | `fam.unimodular_lattice[R, domain]` | R: commutative ring object, domain: proof that R is a domain | `(R : Type u) [CommRing R] [IsDomain R]` | `S/Lattices/Valued/CatalogueRegistration.lean:502` | yes |
| — | `cat.unimodular_lattices_over_rings` | — | `refine(cat.lattices_over_rings, clf.bilin_forms.unimodular)` | — | — | `S/LatticeRefinements.lean:304` | yes |
| — | `cat.walking_pair` | — | `atom` | — | — | `S/Foundation/PairDiagrams.lean:98` | yes |
| — | `cat.well_ordered_sets` | WellOrderedSets | `total(clf.linear_orders.well_ordered)` | — | — | `S/Foundation/WellOrderedSetsRegistration.lean:145` | no |

Each of the 20 category family rows has exactly one category row for a fibre.

## Differences

### `main` (443fba9) and the published catalogue (3f8aedf)

| Quantity | Published | `main`, all modules | `main`, import closure of `LeanCategories.Catalogue` |
| --- | --- | --- | --- |
| Registry rows | 608 | 675 | 611 |
| Category rows | 96 | 100 | 96 |
| Structural functor edges | 49 | 49 | 49 |
| Classifier forget edges | 12 | 13 | 12 |
| Derived edges | 27 | 28 | 27 |
| Categories that reach `cat.sets` | 49 | 49 | 49 |

- Rows that the catalogue has and `main` lacks: 0.
- Rows that `main` has and the catalogue lacks: 67. Of these, 43 are in `extension-ports.json` (same mathematics revision, with additional imports), and 24 are new after `3f8aedf`.
- On the 608 shared rows, 3323 fields were compared (identifiers, expressions, sources, targets, hosts, owners, `structural`). Differences: 0.
- Layers that change for a shared category: 0.
- A new export from `LeanCategories.Catalogue` at `443fba9` gives the same categories and the same edges as the published catalogue. It adds 3 rows: `fun.sets.power_set` (not structural), `cell.sets.finite_subsets.inclusion`, `lim.groups.product`.

Rows only in `main`, by kind:

| Kind | Count | Rows |
| --- | --- | --- |
| morphism | 24 | `mor.cusps.identity`, `mor.sets.automorphism_forward`, `mor.sets.automorphism_backward`, `mor.groups.automorphism_forward`, `mor.groups.automorphism_backward`, `mor.modules.automorphism_forward`, `mor.modules.automorphism_backward`, `mor.sets.automorphism_evaluation`, `mor.sets.automorphism_inverse_evaluation`, `mor.sets.cyclic_quotient_map`, `mor.groups.cyclic_quotient_aut_by_unit`, `mor.modules.rectangular_linear_map`, `mor.modules.row_linear_map`, `mor.sets.successor_power_series_terms`, `mor.core_sets.specified_iso`, `mor.core_sets.fin_rev`, `mor.sets.integer_square_bound_subset`, `mor.sets.integer_square_bound_admitted`, `mor.bilin_module.pulled_back_forward`, `mor.bilin_module.pulled_back_backward`, `mor.bilin_module.degenerate_plane_cone`, `mor.bilin_module.degenerate_plane_paired_cone`, `mor.bilin_module.degenerate_plane_map`, `mor.bilin_module.ordinary_kernel_inclusion` |
| object | 20 | `obj.cusps.canonical`, `obj.sets.cyclic_quotient`, `obj.groups.cyclic_quotient`, `obj.fields.prime_residues`, `obj.sets.rectangular_matrices`, `obj.linear_orders.fin_ordinary`, `obj.linear_orders.fin_reverse`, `obj.sets.integer_square_bound`, `obj.finite_sets.integer_square_bound`, `obj.enumerated_sets.ranked_fin`, `obj.enumerated_sets.ranked_countable`, `obj.enumerated_sets.naturals`, `obj.enumerated_sets.realized_positions`, `obj.sets.two_subsets`, `obj.modules_r.restricted_regular`, `obj.bilin_module.degenerate_plane`, `obj.bilin_module.degenerate_plane_target`, `obj.bilin_module.degenerate_plane_with_dot`, `obj.bilin_module.ordinary_kernel_restriction`, `obj.bilin_module.rational_diagonal_2_3` |
| functor | 8 | `fun.cusps.orbits`, `fun.sets.power_set`, `fun.core_sets.two_subsets`, `fun.well_ordered_sets.linear_order`, `fun.well_ordered_sets.sets`, `fun.enumerated_monotone_sets.enumerated`, `fun.enumerated_monotone_sets.well_ordered_sets`, `fun.well_ordered_sets.order_type` |
| category | 4 | `cat.cusps`, `cat.well_ordered_sets`, `cat.enumerated_monotone_sets`, `cat.core_well_ordered_sets` |
| operation | 4 | `op.enumerated_sets.ranked.rank`, `op.enumerated_sets.ranked.index_of`, `op.enumerated_sets.ranked.nth`, `op.enumerated_sets.ranked.le` |
| presentation | 2 | `cmp.groups.cyclic_quotient_residue`, `cmp.sets.fin_reversal` |
| cell | 1 | `cell.sets.finite_subsets.inclusion` |
| method | 1 | `meth.two_subsets` |
| classifier | 1 | `clf.linear_orders.well_ordered` |
| lift | 1 | `lift.bilin_module.change_value_restriction` |
| limit | 1 | `lim.groups.product` |

The rows of `main` that change the graph:

| Row | Fact | Where | In `LeanCategories.Catalogue` closure |
| --- | --- | --- | --- |
| category `cat.cusps` | expression `atom`; no layer | `LeanCategories/Lattices/Valued/Cusps.lean:400` | no |
| category `cat.well_ordered_sets` | expression `total(clf.linear_orders.well_ordered)`; no layer | `S/Foundation/WellOrderedSetsRegistration.lean:145` | no |
| category `cat.enumerated_monotone_sets` | expression `atom`; no layer | `S/Foundation/WellOrderedSetsRegistration.lean:151` | no |
| category `cat.core_well_ordered_sets` | expression `core(cat.well_ordered_sets)`; no layer | `S/Foundation/WellOrderedSetsRegistration.lean:192` | no |
| classifier `clf.linear_orders.well_ordered` | host `cat.totally_ordered_sets` | `S/Foundation/WellOrderedSetsRegistration.lean:138` | no |
| functor `fun.cusps.orbits` | `cat.cusps` → `cat.sets`; structural: no | `LeanCategories/Lattices/Valued/Cusps.lean:438` | no |
| functor `fun.sets.power_set` | `cat.sets` → `cat.sets`; structural: no | `S/Foundation/PowerSets.lean:357` | yes |
| functor `fun.core_sets.two_subsets` | `cat.core_sets` → `cat.sets`; structural: no | `S/Foundation/TwoSubsets.lean:124` | no |
| functor `fun.well_ordered_sets.linear_order` | `cat.well_ordered_sets` → `cat.totally_ordered_sets`; structural: no | `S/Foundation/WellOrderedSetsRegistration.lean:157` | no |
| functor `fun.well_ordered_sets.sets` | `cat.well_ordered_sets` → `cat.sets`; structural: no | `S/Foundation/WellOrderedSetsRegistration.lean:166` | no |
| functor `fun.enumerated_monotone_sets.enumerated` | `cat.enumerated_monotone_sets` → `cat.enumerated_sets`; structural: no | `S/Foundation/WellOrderedSetsRegistration.lean:174` | no |
| functor `fun.enumerated_monotone_sets.well_ordered_sets` | `cat.enumerated_monotone_sets` → `cat.well_ordered_sets`; structural: no | `S/Foundation/WellOrderedSetsRegistration.lean:183` | no |
| functor `fun.well_ordered_sets.order_type` | `cat.core_well_ordered_sets` → `cat.ordinals`; structural: no | `S/Foundation/WellOrderedSetsRegistration.lean:198` | no |

Edges only in `main`: `ctor.core(forget[clf.linear_orders.well_ordered])` (`cat.core_well_ordered_sets` → `core(cat.totally_ordered_sets)`); `forget[clf.linear_orders.well_ordered]` (`cat.well_ordered_sets` → `cat.totally_ordered_sets`). Edges only in the catalogue: none.

### `main` and the layer table of plan.md

| Item of plan.md | Finding in `main` |
| --- | --- |
| Layers 0 to 7 of the table (21 categories) | All 21 layers are the same. Differences: 0. (**INFERENCE**: the mapping of the English names of the table to category ids.) |
| Categories of layers 1 to 7 that the table omits | `cat.slice_sets` (1), `cat.subobjects_sets` (1), `cat.subobjects_modules_r` (2), `cat.hausdorff_topological_commutative_monoids` (3), `cat.subobjects_groups` (5), `cat.modules_total` (6), `cat.module_points` (7) |
| "8 and above: fields, algebras, bilinear and quadratic modules, lattices" | Layer 8: 14 categories. Layer 9: `cat.bilin_module`. Layer 10: 4. Layer 11: 2. See the layer table. |
| The table gives no count of categories without a layer | 51 of 100 categories of `main` (47 of 96 of the catalogue) do not reach `cat.sets`. They include `cat.integral_lattices`, `cat.even_integral_lattices`, `cat.unimodular_lattices_over_rings`, `cat.arrows_modules_r` (6 methods), `cat.ordinals` (7 objects), `cat.partially_ordered_sets`. |
| "Leaves 0.2": magmas, semigroups, monoids, semirings, additive monoids, additive commutative monoids, additive groups, rings | `cat.rings` reaches also `cat.groups`: `fun.rings.additive_group` ⋙ `fun.additive_groups.to_groups` (`S/Algebra/Ports.lean:103`, `109`). The list has no entry that `cat.rings` does not reach. |
| "`cat.rings` reaches `cat.monoids` by two structural routes" | There are 3: `fun.rings.semiring ⋙ fun.semirings.monoid`; `fun.rings.multiplicative_monoid`; `fun.rings.additive_group ⋙ fun.additive_groups.to_groups ⋙ fun.groups.monoid`. |
| "Multiplication is registered three times … No multiplication is registered at magmas" | Same in `main`: `op.monoids.mul`, `op.rings.mul`, `op.semirings.mul`. No operation row has the owner `cat.magmas` or `cat.semigroups`. |
| "`cat.partially_ordered_sets` and `cat.totally_ordered_sets` have no structural functor" | Same in `main`. New: `cat.well_ordered_sets` is the total of `clf.linear_orders.well_ordered`, whose host is `cat.totally_ordered_sets`. Its forget is an edge into a category with no layer. |
| "The layers were not compared with lean-categories `main`" | Compared here. `main` adds 1 classifier, 4 categories and 8 functors (none structural). No layer changes. |
| The cycle `cat.sets` ⇄ `cat.subobjects_sets` | Not in plan.md. It is in the catalogue and in `main`. |
| `obj.linear_orders.fin_ordinary`, `obj.linear_orders.fin_reverse` "of the extension catalogue" | Same in `main`: `S/Foundation/FiniteOrders.lean:81`, `88`, outside the import closure of `LeanCategories.Catalogue`. |
| The pinned revision `8c35703` | Not read. It is not in the snapshots. |

## Size of the public interface, by owner category

Owner: the field `category` of an operation, object, morphism, limit, literal, binder and inclusion row; the field `owner` of a method row; the receiver of a property row, else the host of its classifier; the field `over` of a numeral row; the source of the edge of a lift row; the `source` and the `target` of a functor row; the `host` of a classifier row; the `source` of a cell row.

| Layer | Category | Op. | Meth. | Prop. | Obj. | Obj. refining | Num. | Mor. | Lim. | Lifts | Lit. | Bind. | Incl. | Fun. out | of which struct. | Fun. in | Clf. hosted | Cells | Constr. into |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | `cat.sets` |  | 2 | 1 | 49 |  | 1 | 86 | 6 |  | 2 | 8 | 9 | 6 | 1 | 21 | 5 | 4 |  |
| 1 | `cat.additive_monoids` | 1 |  |  | 1 | 1 |  |  |  |  |  |  |  | 1 | 1 | 2 |  |  |  |
| 1 | `cat.boolean_algebras` | 5 |  |  | 1 | 1 |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 1 | `cat.countable_sets` |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 2 |  |  |  |
| 1 | `cat.enumerated_sets` | 4 |  |  | 4 |  |  |  |  |  |  |  |  | 1 |  | 1 |  |  |  |
| 1 | `cat.finite_sets` |  |  |  | 2 | 2 |  |  |  | 1 | 1 |  |  | 1 |  |  |  |  |  |
| 1 | `cat.magmas` |  |  | 1 |  |  |  |  |  |  |  |  |  |  |  |  | 5 |  |  |
| 1 | `cat.partial_orders` | 1 |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 | 1 |  |  |  |
| 1 | `cat.pointed_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 1 | `cat.slice_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 1 | `cat.subobjects_sets` |  | 2 |  |  |  |  |  |  |  |  |  |  | 1 | 1 | 2 |  |  |  |
| 2 | `cat.additive_commutative_monoids` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 | 2 |  |  |  |
| 2 | `cat.linear_orders` | 2 |  |  | 6 | 6 |  |  |  |  |  |  |  | 2 | 2 |  |  | 1 |  |
| 2 | `cat.semigroups` |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |
| 2 | `cat.subobjects_modules_r` |  | 3 |  | 1 |  |  |  |  |  |  |  |  | 3 | 1 | 2 |  |  |  |
| 3 | `cat.hausdorff_topological_commutative_monoids` |  |  |  | 1 | 1 |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 3 | `cat.monoids` | 2 | 1 |  |  |  |  |  |  |  |  |  |  | 2 | 1 | 7 |  |  | 1 |
| 4 | `cat.commutative_monoids` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 | 1 |  |  |  |
| 4 | `cat.groups` | 1 |  | 1 | 4 | 4 |  | 6 | 2 |  |  |  |  | 1 | 1 | 7 |  |  | 1 |
| 4 | `cat.semirings` | 3 |  |  | 1 | 1 | 1 |  |  |  |  |  |  | 2 | 2 | 1 |  | 1 |  |
| 5 | `cat.additive_groups` |  |  |  |  |  |  |  |  |  |  |  |  | 2 | 2 | 2 |  | 1 |  |
| 5 | `cat.subobjects_groups` |  | 1 |  | 5 |  |  |  |  |  |  |  |  | 2 | 1 | 3 |  |  | 1 |
| 6 | `cat.modules_total` |  |  |  |  |  |  |  |  |  |  |  |  | 3 | 1 | 2 |  | 1 |  |
| 6 | `cat.rings` | 4 |  |  | 9 | 9 | 1 |  |  |  |  |  |  | 4 | 4 | 2 | 1 | 3 |  |
| 7 | `cat.commutative_rings` |  |  |  | 10 | 10 |  | 4 |  |  |  |  |  | 3 | 2 | 3 | 1 | 1 |  |
| 7 | `cat.module_points` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 7 | `cat.modules_r` | 2 | 3 |  | 8 | 1 |  | 18 | 1 |  |  |  | 1 | 2 | 1 | 12 | 4 |  |  |
| 8 | `cat.algebras` |  |  |  | 8 | 2 |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 8 | `cat.based_module_indexed` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 8 | `cat.bil_wform` |  |  |  | 10 |  |  | 8 | 1 |  |  |  |  | 2 | 1 | 2 |  |  |  |
| 8 | `cat.coord` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 | 2 |  |  |  |
| 8 | `cat.fields` |  |  |  | 4 | 3 |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 8 | `cat.finite_projective_lattice` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 8 | `cat.free_cover_indexed` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| 8 | `cat.quad_module` |  |  |  |  |  |  |  |  |  |  |  |  | 2 | 1 | 1 |  |  |  |
| 8 | `cat.quad_wform` |  |  |  |  |  |  |  |  |  |  |  |  | 2 | 1 |  |  |  |  |
| 8 | `cat.quotients_modules_r` |  | 2 |  |  |  |  |  |  |  |  |  |  | 2 | 1 | 2 |  |  |  |
| 9 | `cat.bilin_module` |  |  | 2 | 7 |  |  | 7 |  |  |  |  |  | 4 | 2 | 5 | 2 | 1 |  |
| 10 | `cat.alternating_forms` |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| 10 | `cat.integral_lattice` |  |  |  | 1 |  |  |  |  |  |  |  |  | 1 | 1 | 2 |  |  |  |
| 10 | `cat.lattice` |  |  |  |  |  |  |  |  |  |  |  |  | 3 | 1 | 2 |  |  |  |
| 10 | `cat.subobjects_bilin_module` |  | 1 |  |  |  |  |  |  |  |  |  |  | 2 | 1 |  |  |  |  |
| 11 | `cat.coord_lattice` |  |  |  |  |  |  |  |  |  |  |  |  | 2 | 2 |  |  |  |  |
| 11 | `cat.fraction_field_perfect_finite_projective_lattice` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| — | `cat.arrows_bilin_module` |  |  |  |  |  |  |  |  | 2 |  |  |  |  |  | 1 |  |  |  |
| — | `cat.arrows_groups` |  | 1 |  |  |  |  |  |  |  |  |  |  | 2 |  | 1 |  |  |  |
| — | `cat.arrows_modules_r` |  | 6 |  |  |  |  |  |  |  |  |  |  | 5 |  | 3 |  | 1 |  |
| — | `cat.based_module` |  |  |  |  |  |  |  |  |  |  |  |  | 2 | 1 |  |  |  |  |
| — | `cat.bilin_forms_over_rings` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  | 4 | 5 |  |  |
| — | `cat.cardinalities` |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 2 |  |  |  |
| — | `cat.cardinals` |  |  |  |  |  |  |  |  |  | 1 |  |  | 1 | 1 | 3 |  |  |  |
| — | `cat.core_groups` |  |  |  |  |  |  |  |  |  |  |  |  | 3 |  |  |  | 1 |  |
| — | `cat.core_modules_r` |  |  |  |  |  |  |  |  |  |  |  |  | 4 |  |  |  | 1 |  |
| — | `cat.core_pointed_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  | 1 |  |
| — | `cat.core_sets` |  |  |  |  |  |  | 2 |  |  |  |  |  | 4 |  |  |  | 1 |  |
| — | `cat.core_subobjects_modules_r` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |
| — | `cat.core_subobjects_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 4 |  |  |  |  |  |
| — | `cat.core_well_ordered_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |
| — | `cat.cusps` |  |  |  | 1 |  |  | 1 |  |  |  |  |  | 1 |  |  |  |  |  |
| — | `cat.enumerated_monotone_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 2 |  |  |  |  |  |
| — | `cat.finite_projective_lattices_over_rings` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |
| — | `cat.free_cover` |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |
| — | `cat.ideals_r` |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |
| — | `cat.integral_forms` |  |  |  |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  |  |  |
| — | `cat.integral_lattices` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |
| — | `cat.lattices_over_rings` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |
| — | `cat.magmaswithtwooperations` |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |
| — | `cat.modules_over_rings_ext` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  | 2 | 1 |  |  |
| — | `cat.ordinals` |  |  |  | 7 |  |  | 4 |  |  |  |  |  | 1 |  | 1 |  |  |  |
| — | `cat.partially_ordered_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |
| — | `cat.quad_forms_over_rings` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |
| — | `cat.schemes` |  |  |  | 1 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| — | `cat.schemes_over_ring` |  |  |  | 2 |  |  |  |  |  |  |  |  |  |  |  |  |  |  |
| — | `cat.sets.pair_diagrams` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  | 1 |  |  |  |
| — | `cat.subsets.point_predicates` |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |
| — | `cat.subsets.subset_predicates` |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |
| — | `cat.totally_ordered_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  | 1 | 1 |  |  |
| — | `cat.well_ordered_sets` |  |  |  |  |  |  |  |  |  |  |  |  | 2 |  | 1 |  |  |  |
| — | `total(clf.magmas.unital)` (no category row) |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |
| | **Total** | **25** | **22** | **5** | **144** | **41** | **3** | **136** | **10** | **3** | **4** | **8** | **10** | **114** | **49** | **114** | **27** | **18** | **3** |

Categories with no row in this table own nothing and are the endpoint of no functor row.

The 25 operation rows:

| Owner | Operations |
| --- | --- |
| `cat.additive_monoids` | op.additive_monoids.add `+` |
| `cat.boolean_algebras` | op.boolean_algebras.diff `∖`, op.boolean_algebras.inter `∩`, op.boolean_algebras.subset `⊆`, op.boolean_algebras.symm_diff `△`, op.boolean_algebras.union `∪` |
| `cat.enumerated_sets` | op.enumerated_sets.ranked.index_of `indexOf`, op.enumerated_sets.ranked.le `≤`, op.enumerated_sets.ranked.nth `nth`, op.enumerated_sets.ranked.rank `rank` |
| `cat.groups` | op.groups.inverse `⁻¹` |
| `cat.linear_orders` | op.linear_orders.le `≤`, op.linear_orders.lt `<` |
| `cat.modules_r` | op.modules.scalar_action `•`, op.modules.zero `0` |
| `cat.monoids` | op.monoids.mul `·`, op.monoids.one `1` |
| `cat.partial_orders` | op.partial_orders.le `≤` |
| `cat.rings` | op.rings.add `+`, op.rings.mul `·`, op.rings.neg `-`, op.rings.pow `^` |
| `cat.semirings` | op.semirings.add `+`, op.semirings.mul `·`, op.semirings.pow `^` |

`cat.sets` owns 49 objects and 86 morphism families. Their rows are in these files (objects, morphisms and operations together):

| File | Rows owned by `cat.sets` |
| --- | --- |
| `S/Algebra/LinearAlgebra.lean` | 16 |
| `S/Algebra/Polynomials.lean` | 16 |
| `S/Algebra/Calculus.lean` | 13 |
| `S/Algebra/NumberSystems.lean` | 9 |
| `S/Algebra/Differentials.lean` | 8 |
| `S/Algebra/RealLimits.lean` | 8 |
| `S/Limits/Registration.lean` | 6 |
| `S/Algebra/PolynomialPresentations.lean` | 5 |
| `S/Algebra/Semirings.lean` | 5 |
| `S/Foundation/Objects.lean` | 5 |
| `S/Algebra/AutomorphismArrows.lean` | 4 |
| `S/Algebra/MvPolynomials.lean` | 4 |
| `S/Algebra/ShiftedDualNumbers.lean` | 4 |
| `S/Foundation/PowerSets.lean` | 4 |
| `S/Modules/Bilinear/Valued/Constructions.lean` | 4 |
| `S/Foundation/IntegerSquareBounds.lean` | 3 |
| `S/Algebra/CyclicQuotients.lean` | 2 |
| `S/Algebra/FiniteSums.lean` | 2 |
| `S/Algebra/Units.lean` | 2 |
| `S/Foundation/Terminals.lean` | 2 |
| `S/Algebra/FiniteGroups.lean` | 1 |
| `S/Algebra/GroupMaps.lean` | 1 |
| `S/Algebra/NamedRings.lean` | 1 |
| `S/Algebra/RectangularLinearAlgebra.lean` | 1 |
| `S/Algebra/Series.lean` | 1 |
| `S/Algebra/SuccessorSeries.lean` | 1 |
| `S/Foundation/FiniteSubsets.lean` | 1 |
| `S/Foundation/Maps.lean` | 1 |
| `S/Foundation/Morphisms.lean` | 1 |
| `S/Foundation/TwoSubsets.lean` | 1 |
| `S/Modules/LinearMaps.lean` | 1 |
| `S/Modules/Bilinear/Valued/CatalogueRegistration.lean` | 1 |
| `S/Modules/Bilinear/Valued/Kernels.lean` | 1 |

## Independent directions

Remove `cat.sets` from the 49 categories that reach it. The connected parts of the remaining graph have no edge between them:

| Direction | Categories | Roots (layer 1) | Largest layer | Members |
| --- | --- | --- | --- | --- |
| Algebra | 38 | `cat.additive_monoids`, `cat.magmas` | 11 | see below |
| Orders | 2 | `cat.partial_orders` | 2 | `cat.partial_orders` (1), `cat.linear_orders` (2) |
| Subobjects | 2 | `cat.subobjects_sets` | 2 | `cat.subobjects_sets` (1), `cat.subobjects_modules_r` (2) |
| Boolean algebras | 1 | `cat.boolean_algebras` | 1 | `cat.boolean_algebras` (1) |
| Countable sets | 1 | `cat.countable_sets` | 1 | `cat.countable_sets` (1) |
| Enumerated sets | 1 | `cat.enumerated_sets` | 1 | `cat.enumerated_sets` (1) |
| Finite sets | 1 | `cat.finite_sets` | 1 | `cat.finite_sets` (1) |
| Pointed sets | 1 | `cat.pointed_sets` | 1 | `cat.pointed_sets` (1) |
| Slices of sets | 1 | `cat.slice_sets` | 1 | `cat.slice_sets` (1) |

Inside the direction "Algebra" (38 categories):

| Part | Categories | Depends on |
| --- | --- | --- |
| Common base | `cat.additive_monoids`, `cat.magmas`, `cat.semigroups`, `cat.monoids`, `cat.groups`, `cat.additive_groups` | `cat.sets`. Two chains start at layer 1: `cat.magmas` → `cat.semigroups` → `cat.monoids` → `cat.groups`, and `cat.additive_monoids`. They join at `cat.additive_groups` (layer 5). |
| Ring branch | `cat.rings`, `cat.commutative_rings`, `cat.division_rings`, `cat.algebras`, `cat.fields` | The common base, and `cat.semirings`, `cat.additive_commutative_monoids` (for `cat.rings`), `cat.commutative_monoids` (for `cat.commutative_rings`). |
| Module branch | `cat.modules_total`, `cat.module_points`, `cat.modules_r`, `cat.based_module_indexed`, `cat.bil_wform`, `cat.coord`, `cat.finite_projective_lattice`, `cat.finitelygeneratedmodules`, `cat.finiterankmodules`, `cat.free_cover_indexed`, `cat.freemodules`, `cat.quad_module`, `cat.quad_wform`, `cat.quotients_modules_r`, `cat.torsion_free_modules`, `cat.bilin_module`, `cat.alternating_forms`, `cat.integral_lattice`, `cat.lattice`, `cat.subobjects_bilin_module`, `cat.coord_lattice`, `cat.fraction_field_perfect_finite_projective_lattice` | The common base only. |
| Other members | `cat.additive_commutative_monoids`, `cat.commutative_monoids`, `cat.hausdorff_topological_commutative_monoids`, `cat.semirings`, `cat.subobjects_groups` | `cat.semirings` and `cat.commutative_monoids` need `cat.monoids`. `cat.additive_commutative_monoids` needs `cat.additive_monoids`. `cat.hausdorff_topological_commutative_monoids` needs `cat.additive_commutative_monoids`. `cat.subobjects_groups` needs `cat.groups`. |

The ring branch and the module branch do not reach each other. No category of the module branch reaches `cat.rings`, `cat.semirings` or `cat.commutative_monoids`. Two categories are independent when neither is in the `reaches` list of the other; `scaffolding.json` has that list for each category.

The directions are independent for structural edges only. These functor rows are not structural and leave the set that their source reaches. Their source has a layer:

| Functor | Source (layer) | Target (layer) | Row |
| --- | --- | --- | --- |
| `fun.monoids.units` | `cat.monoids` (3) | `cat.groups` (4) | `S/Algebra/Units.lean:540` |
| `fun.subobjects_groups.inclusion` | `cat.subobjects_groups` (5) | `cat.arrows_groups` (none) | `S/Algebra/Subgroups.lean:153` |
| `fun.sets.pair_diagonal` | `cat.sets` (0) | `cat.sets.pair_diagrams` (none) | `S/Foundation/PairDiagrams.lean:110` |
| `fun.sets.enumerated_to_countable` | `cat.enumerated_sets` (1) | `cat.countable_sets` (1) | `S/Foundation/CatalogueRegistration.lean:180` |
| `fun.modules.projection` | `cat.modules_total` (6) | `cat.rings` (6) | `S/FibrationRegistration.lean:221` |
| `fun.quotients_modules.projection` | `cat.quotients_modules_r` (8) | `cat.arrows_modules_r` (none) | `S/Modules/Operations.lean:569` |
| `fun.subobjects_modules.inclusion` | `cat.subobjects_modules_r` (2) | `cat.arrows_modules_r` (none) | `S/Modules/Operations.lean:579` |
| `fun.subobjects_modules.domain` | `cat.subobjects_modules_r` (2) | `cat.modules_r` (7) | `S/Modules/Operations.lean:616` |
| `fun.subobjects_bilin_module.inclusion` | `cat.subobjects_bilin_module` (10) | `cat.arrows_bilin_module` (none) | `S/Modules/Bilinear/Valued/Kernels.lean:287` |
| `fun.modules_ext.regular_section` | `cat.commutative_rings` (7) | `cat.modules_over_rings_ext` (none) | `S/FibrationRegistration.lean:275` |
| `fun.sets.finite_to_countable` | `cat.finite_sets` (1) | `cat.countable_sets` (1) | `S/Foundation/CatalogueRegistration.lean:172` |

Example: the method `units` of `cat.monoids` (`meth.units`, `S/Algebra/Automorphisms.lean:434`) is the functor `fun.monoids.units` into `cat.groups`. The complete list, with the sources that have no layer, is the key `nonStructuralFunctorsLeavingTheDownSet` of `scaffolding.json`.

## Inferences

Each item is an **INFERENCE**. Everything else in this document was read from a source line or computed from read facts.

1. **The registry is reconstructed from text.** No Lean was run, so the registry state of `443fba9` was not printed by Lean. Check: for the 608 rows that the published catalogue shares with `main`, the reconstruction equals the `Repr` text that Lean exported, in 3323 of 3323 fields. The 67 rows only in `main` have no such check. Of these, the rows that can change the graph (1 classifier, 4 categories, 8 functors) were read by hand.
2. **Each `normalized_registry` command of `main` is accepted by Lean.** `main` was not built here. One command is known to be refused and is left out: `mor.probe.field_divide` (`S/TotalityProbes.lean:111-117`, an expected error under `#guard_msgs`).
3. **The import closure of `LeanCategories.Catalogue`** was computed from the `import` lines of the modules. `LeanCategories.All` imports every module that has a row. The package root `LeanCategories.lean` imports `LeanCategories.Catalogue`, not `LeanCategories.All`.
4. **Owner of `num.sets.fin`.** The row has `over := none`. The owner `cat.sets` is read from the identifier. Its declaration is `finPoint (n k : ℕ) (h : k < n) : fin 1 ⟶ fin n` (`S/Foundation/Morphisms.lean:30`).
5. **Rows at a family with other parameter variables** (`fam.modules[S]`, `fam.bilin_module[R, W']`, …) are counted at the one category row of that family.
6. **The mapping of the English names of the plan table to category ids** (for example "modules over a ring" = `cat.modules_r`).
7. **The inferred layer** of the categories that do not reach `cat.sets`, and the key `inferredInputs` of `scaffolding.json`. Constructor arguments, refinement bases and opaque ports are not structural edges in lean-categories.
8. **The category of a family parameter** (ring object → `cat.rings`, commutative ring object → `cat.commutative_rings`, module object → `cat.modules_r`, index type → `cat.sets`), used only for the inferred layer. The parameter kinds are read from `LeanCategories/Catalogue/Syntax.lean:54-80`.
9. **The meaning of `edgeActions` in the JSON catalogue.** The exporter takes it from the admission interface of the kernel (`state.imageEdges`). The kernel source is not in the snapshots and was not read.
10. **"Registered category" means a `.category` row.** The 20 family rows, the 27 classifier rows and the 2 opaque rows are not counted as categories. Each family and each opaque category has a category row.

## Edges checked by hand against the source

| Edge | Read at | Result |
| --- | --- | --- |
| `fun.rings.additive_group`: `cat.rings` → `cat.additive_groups` | `S/Algebra/Ports.lean:103-108`; id at `:44`; `Rings` at `S/Algebra/Catalogue/Rings.lean:30` | `structural := true` |
| `fun.additive_groups.to_groups`: `cat.additive_groups` → `cat.groups` | `S/Algebra/Ports.lean:109-114`; id at `:45` | `structural := true` |
| `fun.monoids.semigroup`: `cat.monoids` → `cat.semigroups` | `S/Algebra/Ports.lean:121-126`; `Semigroups := .classifierTotal ClassifierId.magmasAssociative` at `S/Algebra/Catalogue/Magmas.lean:34` | `structural := true` |
| `fun.semirings.monoid`: `cat.semirings` → `cat.monoids` | `S/Algebra/ComputationDerivations.lean:147-154` | `structural := true` |
| forget of `clf.magmas.associative`: `cat.semigroups` → `cat.magmas` | classifier row `S/Algebra/CatalogueRegistration.lean:102-106` (host `Magmas`); category row `:138` | edge by the rule of `Semantic.lean:1685-1692` |
| forget of `clf.sets.binary_operation`: `cat.magmas` → `cat.sets` | classifier row `S/Foundation/CatalogueRegistration.lean:121-125` (host `Foundation.Sets`); category row `S/Algebra/CatalogueRegistration.lean:133`; `Magmas` at `S/Algebra/Catalogue/Magmas.lean:25` | edge |
| forget of `clf.commutative_rings.field`: `cat.fields` → `cat.commutative_rings` | `S/Algebra/Fields.lean:88-92`, `93-96`; `Fields` at `:46` | edge |
| forget of `clf.linear_orders.well_ordered`: `cat.well_ordered_sets` → `cat.totally_ordered_sets` | `S/Foundation/WellOrderedSetsRegistration.lean:138-143`, `145-149`; ids and expression at `S/Foundation/WellOrderedSets.lean:36`, `41`, `61` | edge; new in `main` |
| `fun.modules.fibre_inclusion`: `cat.modules_r` → `cat.modules_total` | `S/Modules/CatalogueRegistration.lean:554-563`; expressions at `S/Modules/Expressions.lean:13-21` | `structural := true` |
| `fun.modules.additive_group`: `cat.modules_total` → `cat.additive_groups` | `S/Modules/CatalogueRegistration.lean:581-587` | `structural := true` |
| `fun.modules.underlying`: `cat.modules_total` → `cat.sets` | `S/Modules/CatalogueRegistration.lean:571-579` | `structural := false`, with the comment "not a duplicate structural edge" |
| `fun.bilin_module.forget`: `cat.bilin_module` → `cat.modules_r` | `S/Modules/Bilinear/Valued/CatalogueRegistration.lean:192-201` | `structural := true` |
| `fun.linear_orders.to_partial_orders`: `cat.linear_orders` → `cat.partial_orders` | `S/Foundation/PowerSets.lean:339-344`; expressions at `:82-83` | `structural := true` |
| `fun.sets.whole_subset`: `cat.sets` → `cat.subobjects_sets` | `S/Foundation/Subsets.lean:178-184` | `structural := true` |
| `fun.subobjects_sets.domain`: `cat.subobjects_sets` → `cat.sets` | `S/Foundation/Subsets.lean:185-191` | `structural := true` |
| `fun.subobjects_modules.domain`: `cat.subobjects_modules_r` → `cat.modules_r` | `S/Modules/Operations.lean:616-621` | no `structural` field: not an edge |
| `fun.lattices_over_rings.to_bil`: `cat.lattices_over_rings` → `cat.bilin_forms_over_rings` | `S/LatticeRefinements.lean:250-255` | no `structural` field: not an edge |
| `fun.integral_forms.to_bil`: `cat.integral_forms` → `cat.bilin_forms_over_rings` | `S/FibrationRegistration.lean:311-320` | `structural := true` |
| The 8 functor rows only in `main` | `LeanCategories/Lattices/Valued/Cusps.lean:438-442`; `S/Foundation/PowerSets.lean:357-361`; `S/Foundation/TwoSubsets.lean:124-128`; `S/Foundation/WellOrderedSetsRegistration.lean:157-204` | none has a `structural` field: no new functor edge |
| The 4 category rows only in `main` | `LeanCategories/Lattices/Valued/Cusps.lean:400-404` (`CuspsExpr := .atom` at `:393`); `S/Foundation/WellOrderedSetsRegistration.lean:145-155`, `192-196`; expressions at `S/Foundation/WellOrderedSets.lean:61-66` | one classifier total, two atoms, one `Core` |

## Files and reproduction

| File | Content |
| --- | --- |
| `scaffolding.json` | Categories (id, name, expression, layer, reaches, immediate, parameters, counts, file), edges, cycles, directions, differences, criterion, revision. |
| `scaffolding_verify_layers.py` | Recomputes the layers, the reach sets and the immediate lists from the edge list of `scaffolding.json`. It shares no code with the other scripts. Result at the time of writing: PASS. |
| `scaffolding-scripts/extract_rows.py` | Reads the Lean source: each `normalized_registry` command, each `def`, each `import`. |
| `scaffolding-scripts/build_registry.py` | Resolves the identifiers and expressions of each row; second mode: reads the `Repr` text of a published catalogue. |
| `scaffolding-scripts/scaffold.py` | Graph, layers, reach sets, cycles, counts, directions. |
| `scaffolding-scripts/compare.py` | Differences with the published catalogue and with the plan table. |
| `scaffolding-scripts/assemble.py`, `render_md.py` | Write `scaffolding.json` and this document. |
| `scaffolding-work/` | Intermediate files of the scripts. |

```sh
S=scaffolding-scripts; W=scaffolding-work; SNAP=../main-snapshots
python3 -I $S/extract_rows.py $SNAP/lean-categories $W/raw_rows.json
python3 -I $S/build_registry.py $W/raw_rows.json $W/main_registry.json
python3 -I $S/build_registry.py --published $SNAP/lean-cas-dsl-leaf-contracts/api/declared-ports.json $W/published_registry.json
python3 -I $S/build_registry.py --published $SNAP/lean-cas-dsl-leaf-contracts/api/extension-ports.json $W/extension_registry.json
python3 -I $S/scaffold.py $W/main_registry.json $W/main_all.json --scope all --revision 443fba9
python3 -I $S/scaffold.py $W/main_registry.json $W/main_catalogue.json --scope catalogue --revision 443fba9
python3 -I $S/scaffold.py $W/published_registry.json $W/published_scaffold.json --scope all --revision 3f8aedf
python3 -I $S/compare.py $W/main_registry.json $W/published_registry.json $W/extension_registry.json $W/main_all.json $W/main_catalogue.json $W/published_scaffold.json $W/differences.json
python3 -I $S/assemble.py $W/main_all.json $W/differences.json scaffolding.json
python3 -I scaffolding_verify_layers.py scaffolding.json
python3 -I $S/render_md.py scaffolding.json $W/main_registry.json scaffolding.md
```
