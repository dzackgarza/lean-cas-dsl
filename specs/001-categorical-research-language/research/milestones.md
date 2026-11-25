# Computational milestones: categories, statements and registrations (snapshot of 2026-11-25)

This record is the computation behind the section "Computational milestones" of `plan.md`. It reads fixed revisions and is not kept current. `milestones.json` holds the same data.

| Input | Revision |
| --- | --- |
| Structural scaffolding (`scaffolding.json`) | lean-categories `443fba9` |
| Routes of the 287 workload statements (`workload-routes.json`) | catalogue `3f8aedf`, workload files of `main` `45910a5` and of the kernel branch `fc7fdf8` |
| Routes of the 18 statements of `tests/acceptance/b0-required-positives.cas.proposed` and `b0-formed-positives.cas.proposed` | the text matcher of `workload-routes.json`, corrected by hand for 8 statements (table below) |
| Registrations (`existing-leaves.json`) | lean-cas-dsl-leaves `8b181d7` |

## Method

1. **Prerequisites.** A category needs the categories that its structural functors and classifier forgets reach (`scaffolding.json`, edges of the kinds "structural functor" and "classifier forget"; the cut edge `fun.sets.whole_subset` is left out). A category with no structural chain to `cat.sets` also needs the categories that it is built from (`inferredInputs` of `scaffolding.json`: constructor arguments, the base and the classifier host of a refinement, the parameter categories of a family fibre). The changes of the upstream tasks that come before the milestones are applied: T131 (lean-categories#193: structural `fun.additive_monoids.semigroup`, `fun.additive_semigroups.magma`, `fun.additive_magmas.sets`, `fun.semirings.additive_commutative_monoid`), T133 (lean-categories#195: `cat.preorders` below `cat.partial_orders`; join and meet semilattices, order lattices and bounded order lattices above it; `cat.boolean_algebras` above bounded order lattices; `cat.partially_ordered_sets` and `cat.totally_ordered_sets` deleted; well-ordered sets hosted at `cat.linear_orders`), and the structural functors of the scaffolding gaps of the lean-categories plan.

2. **Groups of categories.** Each milestone holds the prerequisite closure of its seed categories, less the categories of the milestones before it in the list of seeds.

3. **Order.** A milestone comes after each milestone that holds a prerequisite of one of its categories, and after each milestone that holds a category on the route of every statement that uses one of its categories. The milestones with a V1 statement come first, then the milestones with a full-B0 statement, then the milestones with no workload statement. Ties go to the smaller depth (the longest prerequisite chain of a category of the milestone), then to the name.

4. **Statements.** A statement belongs to the first milestone whose categories, with those of the milestones before it, contain every category on its route. A typing judgement (question kind `settled`, 19 statements) holds by elaboration and belongs to no milestone. V1 statements are the 134 extension statements and the 15 K1 identifiers that #24 keeps as required computational assertions; the other statements are full B0 (#19).

5. **Registrations.** A registration moves into the first milestone that has a statement whose rows name its operation and its input form; else a statement that names its operation; else the first milestone that holds every category of its operation and input form. A milestone is never earlier than the one that holds the categories of the registration.

## Milestones

| Task | Milestone | Part | After | Categories | V1 statements | Full-B0 statements | Registrations |
| --- | --- | --- | --- | --- | ---: | ---: | ---: |
| T200 | Sets | M2 | — | `cat.cardinalities`, `cat.cardinals`, `cat.core_sets`, `cat.sets` | 23 | 0 | 30 |
| T201 | Finite sets | M2 | T200 | `cat.finite_sets` | 3 | 0 | 2 |
| T202 | Orders | M2 | T200 | `cat.linear_orders`, `cat.partial_orders`, `cat.preorders` | 4 | 0 | 0 |
| T203 | Rings | M2 | T200 | `cat.additive_commutative_monoids`, `cat.additive_groups`, `cat.additive_magmas`, `cat.additive_monoids`, `cat.additive_semigroups`, `cat.groups`, `cat.magmas`, `cat.monoids`, `cat.rings`, `cat.semigroups`, `cat.semirings` | 15 | 0 | 25 |
| T204 | Group automorphisms | M2 | T200, T203 | `cat.core_groups` | 13 | 0 | 0 |
| T205 | Commutative rings | M2 | T200, T203 | `cat.commutative_monoids`, `cat.commutative_rings` | 18 | 0 | 18 |
| T206 | Topological monoids | M2 | T200, T203, T205 | `cat.hausdorff_topological_commutative_monoids` | 5 | 0 | 0 |
| T207 | Modules | M2 | T200, T203, T205 | `cat.modules_r`, `cat.modules_total` | 10 | 0 | 3 |
| T208 | Bilinear forms | M2 | T200, T203, T205, T207 | `cat.bil_wform` | 3 | 0 | 10 |
| T209 | Fields | M2 | T200, T203, T205 | `cat.fields` | 13 | 0 | 1 |
| T210 | Module rank | M2 | T200, T203, T205, T207 | `cat.core_modules_r` | 1 | 0 | 5 |
| T211 | Module kernels | M2 | T200, T203, T205, T207 | `cat.arrows_modules_r`, `cat.core_subobjects_modules_r`, `cat.subobjects_modules_r`, `cat.subobjects_sets` | 2 | 0 | 0 |
| T212 | Formed modules | M2 | T200, T203, T205, T207, T208 | `cat.arrows_bilin_module`, `cat.bilin_module` | 39 | 0 | 4 |
| T213 | Full B0 in the V1 categories | M4 | T200–T212 | none of its own | 0 | 123 | 0 |
| T214 | Group kernels | M4 | T200, T203 | `cat.arrows_groups`, `cat.subobjects_groups` | 0 | 4 | 13 |
| T215 | Boolean algebras | M4 | T200, T202, T203 | `cat.boolean_algebras`, `cat.bounded_order_lattices`, `cat.join_semilattices`, `cat.meet_semilattices`, `cat.order_lattices` | 0 | 9 | 0 |
| T216 | Integral lattices | M4 | T200, T203, T205, T207, T210, T212 | `cat.integral_lattice` | 0 | 1 | 4 |
| T217 | Set constructions | M4 | T200, T211 | `cat.arrows_sets`, `cat.core_pointed_sets`, `cat.core_subobjects_sets`, `cat.coslice_sets`, `cat.countable_sets`, `cat.crystals`, `cat.endofunctors_sets`, `cat.enumerated_sets`, `cat.pointed_sets`, `cat.sets.pair_diagrams`, `cat.slice_sets`, `cat.subsets.point_predicates`, `cat.subsets.subset_predicates`, `cat.walking_pair` | 0 | 0 | 0 |
| T218 | Well orders | M4 | T202, T217 | `cat.core_well_ordered_sets`, `cat.enumerated_monotone_sets`, `cat.ordinals`, `cat.well_ordered_sets` | 0 | 0 | 0 |
| T219 | Algebraic structures | M4 | T203 | `cat.division_rings`, `cat.magmaswithtwooperations` | 0 | 0 | 0 |
| T220 | Algebras | M4 | T205 | `cat.algebras` | 0 | 0 | 0 |
| T221 | Schemes | M4 | T200, T205 | `cat.schemes`, `cat.schemes_over`, `cat.schemes_over_ring` | 0 | 0 | 0 |
| T222 | Module constructions | M4 | T200, T205, T207, T211 | `cat.based_module`, `cat.based_module_indexed`, `cat.coord`, `cat.coord_indexed`, `cat.finite_projective_lattice`, `cat.finitelygeneratedmodules`, `cat.finiterankmodules`, `cat.free_cover`, `cat.free_cover_indexed`, `cat.freemodules`, `cat.ideals_r`, `cat.module_points`, `cat.quotients_modules_r`, `cat.torsion_free_modules` | 0 | 0 | 0 |
| T223 | Forms over rings | M4 | T205, T207 | `cat.bilin_forms_over_rings`, `cat.cusps`, `cat.even_integral_lattices`, `cat.finite_free_lattices_over_rings`, `cat.finite_projective_lattices_over_rings`, `cat.integral_forms`, `cat.integral_lattices`, `cat.lattices_over_rings`, `cat.modules_over_rings_ext`, `cat.quad_forms_over_rings`, `cat.unimodular_lattices_over_rings` | 0 | 0 | 0 |
| T224 | Lattices and quadratic modules | M4 | T205, T207, T212, T216, T222 | `cat.alternating_forms`, `cat.coord_lattice`, `cat.definite_lattice`, `cat.even_lattice`, `cat.finite_free_lattice`, `cat.fraction_field_perfect_finite_projective_lattice`, `cat.indefinite_lattice`, `cat.lattice`, `cat.quad_module`, `cat.quad_wform`, `cat.subobjects_bilin_module`, `cat.unimodular_lattice` | 0 | 0 | 0 |

The full-B0 statements of the V1 milestones are listed under T213.

## Statements of each milestone

### T200 — Sets

V1: `sets.card.z4_cubed`, `sets.card.z7`, `sets.card.z5_empty_power`, `sets.card.integers`, `sets.card.fin2_times_z3`, `sets.finite.integers`, `sets.finite.fin2_times_z3`, `sets.implemented.card_fin`, `sets.card.fin2_sqcup_fin3`, `sets.eq.rev_rev`, `sets.limit.pullback.card`, `rx:addition.rx02.actual_forward`, `rx:addition.rx02.actual_backward`, `rx:addition.rx02.nonidentity_input`, `rx:addition.rx02.core_map_composition`, `rx:addition.rx02.core_identity_action`, `rx:addition.rx02.full_inverse_action`, `rx:addition.rx02.whole_direct_image`, `rx:complete.rx02.cardinality`, `rx:complete.rx02.singleton_excluded`, `rx:complete.rx04.finite_classifier`, `rx:complete.rx04.ambient_not_finite`, `rx:complete.rx04.admission_retains_subset`.

Full B0 (attained under T213): `sets.card.naturals`, `sets.card.square`, `sets.finite.fin2_sqcup_fin3`, `sets.apply.rev`, `sets.apply.rev_rev`.

Registrations: `meth.cardinality` (sage) ×6, `meth.cardinality` (gap) ×2, `prop.is_finite` (sage) ×8, `prop.is_finite` (gap) ×2, `meth.cardinality` (sage-power-set), `colim.sets.coproduct` (sage-set-limits), `lim.sets.pullback` (sage-set-limits), `mor.sets.fin_rev` (sage-fin-rev), `meth.cardinality` (gap-groups), `prop.is_finite` (gap-groups), `meth.cardinality` (sage-presentations) ×2, `prop.is_finite` (sage-presentations) ×2, `meth.cardinality` (sage-set-limits), `mor.sets.equality` (sage-symbolic).

### T201 — Finite sets

V1: `finite_sets.limit.pullback.card`, `rx:complete.rx04.cardinality`, `rx:complete.rx04.forgotten_refinement_cardinality`.

Full B0 (attained under T213): `finite_sets.card.three`.

Registrations: `meth.cardinality` (sage), `prop.is_finite` (sage).

### T202 — Orders

V1: `rx:complete.rx01.ordinary_cardinality`, `rx:complete.rx01.reverse_cardinality`, `rx:complete.rx01.ordinary_relation`, `rx:complete.rx01.reverse_relation`.

### T203 — Rings

V1: `rx:addition.rx03.actual_inverse_arrow`, `rx:addition.rx03.arrow_inverse_left`, `rx:addition.rx03.arrow_inverse_right`, `rx:addition.rx03.complete_double_coordinates`, `rx:addition.rx03.complete_triple_coordinates`, `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.double_class_one`, `rx:addition.rx03.double_class_three`, `rx:addition.rx03.triple_class_two`, `rx:complete.rx03.presentation_left_inverse`, `rx:complete.rx03.presentation_right_inverse`, `rx:complete.rx03.inverse`, `rx:complete.rx04.exact_predicate`, `rx:complete.rx04.exact_members`.

Full B0 (attained under T213): `calculus.limit_sinc`, `calculus.limit_infinity`, `calculus.integral_square`, `calculus.integral_sine`, `composed.composition`, `ellipses.naturals`, `ellipses.evens`, `ellipses.multiples`, `ellipses.even_square`, `ellipses.odd_square`, `ellipses.squares_even`, `ellipses.prime`, `ellipses.not_prime`, `factorization.prime_factors`, `factorization.multiplicity_two`, `factorization.multiplicity_three`, `factorization.multiplicity_seven`, `factorization.approximation`, `finite_sets.card`, `finite_sets.card_product`, `finite_sets.card_power_set`, `finite_sets.member`, `finite_sets.not_member`, `comprehension.elements`, `comprehension.card`, `comprehension.even_member`, `comprehension.odd_not_member`, `comprehension.even_card`, `comprehension.image_apply`, `comprehension.image_method`, `fractions.halves`, `fractions.cancel`, `fractions.lowest_terms`, `fractions.modulus`, `functions.extensional`, `functions.at_zero`, `functions.at_three`, `functions.even`, `numbers.integers.sum`, `numbers.zmod5.sum`, `numbers.zmod5.product`, `numbers.zmod5.negation`, `numbers.zmod5.difference`, `numbers.zmod7.distributive`, `numbers.zmod7.value`, `numbers.rationals.sum`, `numbers.gcd`, `numbers.complex.re`, `numbers.complex.im`, `numbers.complex.bar`, `numbers.complex.norm`, `numbers.complex.abs`, `units.rationals.three_inverse`, `refinement.finite_product_card`, `groups.abelian.cyclic_three`, `groups.abelian.symmetric_three`.

Registrations: `meth.cardinality` (gap-groups) ×4, `prop.is_finite` (gap-groups) ×4, `prop.is_abelian` (gap-groups) ×3, `prop.is_commutative` (gap-groups) ×3, `meth.cardinality` (gap), `prop.is_finite` (gap), `mor.sets.complex_re` (sage-symbolic), `mor.sets.complex_im` (sage-symbolic), `mor.sets.complex_bar` (sage-symbolic), `mor.sets.complex_abs` (sage-symbolic), `mor.sets.real_sqrt` (sage-symbolic), `mor.sets.nat_prime_factors` (sage-symbolic), `bind.sets.integral` (sage-symbolic), `bind.sets.limit` (sage-symbolic), `bind.sets.limit_at_infinity` (sage-symbolic).

### T204 — Group automorphisms

V1: `rx:addition.rx03.complete_conjugation`, `rx:addition.rx03.complete_inverse_conjugation`, `rx:addition.rx03.conjugated_double_action`, `rx:addition.rx03.conjugated_triple_action`, `rx:complete.rx03.cardinality`, `rx:complete.rx03.aut_map_left_inverse`, `rx:complete.rx03.aut_map_right_inverse`, `rx:complete.rx03.inverse_product`, `rx:complete.rx03.product_inverse`, `rx:complete.rx03.fourth_power`, `rx:complete.rx03.second_power_nonidentity`, `rx:complete.rx03.conjugation_retains_inverse`, `rx:complete.rx03.conjugated_value_reuse`.

### T205 — Commutative rings

V1: `rx:complete.rx07.generator_forward`, `rx:complete.rx07.generator_backward`, `rx:complete.rx07.generator_nonidentity`, `rx:complete.rx07.left_inverse`, `rx:complete.rx07.right_inverse`, `rx:complete.rx07.coefficients_forward`, `rx:complete.rx07.coefficients_backward`, `rx:complete.rx07.successive_value`, `rx:complete.rx07.successive_square`, `rx:complete.rx07.successive_back`, `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_square_map`, `rx:complete.rx07.full_backward_map`, `rx:complete.rx07.full_map_inverse`, `rx:complete.rx07.map_sample_forward`, `rx:complete.rx07.map_sample_square`, `rx:complete.rx07.map_sample_backward`, `rx:complete.rx09.full_family`.

Full B0 (attained under T213): `composed.root_count`, `composed.root_one`, `composed.root_sum`, `composed.root_product`, `composed.charpoly`, `composed.det`, `composed.trace`, `differentials.degree`, `differentials.at_two`, `differentials.differential`, `differentials.derivative`, `integration.primitives`, `integration.differential`, `integration.derivative`, `integration.at_zero`, `factorization.over_complexes`, `inverses.value`, `inverses.solve`, `inverses.left`, `inverses.right`, `inverses.det`, `matrices.product`, `matrices.juxtaposition`, `matrices.application`, `matrices.det`, `matrices.rank`, `matrices.kernel`, `matrices.trace`, `matrices.charpoly`, `polynomials.degree`, `polynomials.root`, `polynomials.factors`, `polynomials.degree_over_rationals`, `polynomials.at_sqrt2`, `polynomials.at_minus_sqrt2`, `polynomials.no_rational_roots`, `series.coefficient_two`, `series.coefficient_three`, `series.coefficient_zero`, `series.coefficient_four`, `several_variables.dimension`, `several_variables.total_degree`, `several_variables.plane`, `presentations.f9.forward_generator`, `presentations.f9.inverse_generator`, `presentations.f9.forward_constant`, `presentations.f9.inverse_constant`.

Registrations: `meth.cardinality` (sage-presentations) ×2, `prop.is_finite` (sage-presentations) ×2, `cmp.f9.translation` (sage-presentations) ×2, `mor.sets.f9_x_constants` (sage-presentations) ×2, `mor.sets.f9_y_constants` (sage-presentations) ×2, `mor.sets.polynomial_degree` (sage-symbolic), `mor.sets.polynomial_derivative` (sage-symbolic), `mor.sets.polynomial_differential` (sage-symbolic), `mor.sets.polynomial_map` (sage-symbolic), `mor.sets.polynomial_factors` (sage-symbolic), `mor.sets.polynomial_roots` (sage-symbolic), `mor.sets.companion_matrix` (sage-symbolic), `mor.sets.mv_total_degree` (sage-symbolic).

### T206 — Topological monoids

V1: `rx:complete.rx09.full_coefficients`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_five`.

### T207 — Modules

V1: `rx:complete.rx06.restricted_cardinality`, `rx:complete.rx06.named_restricted_cardinality`, `rx:complete.rx06.cartesian_whole_carrier`, `rx:complete.rx06.action_two_three`, `rx:complete.rx06.action_five_one`, `rx:complete.rx06.action_negative_one_two`, `rx:complete.rx06.whole_reindexed_map`, `rx:complete.rx06.reindexed_map_sample`, `rx:complete.rx06.whole_scalar_action`, `rx:complete.rx10.fixed_question`.

Registrations: `lim.sets.product` (sage-set-limits), `meth.cardinality` (sage-modules) ×2.

### T208 — Bilinear forms

V1: `lattices.discriminant.a1`, `lattices.discriminant.a2`, `lattices.discriminant.a3`.

Full B0 (attained under T213): `lattices.card.a2`, `lattices.card.a0`, `formed.card.hyperbolic_variable`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`.

Registrations: `colim.bil_w_form.cokernel` (sage-discriminant), `meth.cardinality` (sage-discriminant), `meth.cardinality` (sage-modules) ×2, `prop.is_abelian` (gap-groups) ×3, `prop.is_commutative` (gap-groups) ×3.

### T209 — Fields

V1: `rx:complete.rx05.inherited_cardinality`, `rx:complete.rx05.multiplicative_cardinality`, `rx:complete.rx05.additive_cardinality`, `rx:complete.rx05.complete_component`, `rx:complete.rx05.complete_inverse_component`, `rx:complete.rx05.component_left_inverse`, `rx:complete.rx05.component_right_inverse`, `rx:complete.rx05.addition`, `rx:complete.rx05.multiplication`, `rx:complete.rx05.operations_distinct`, `rx:complete.rx05.whole_map_naturality`, `rx:complete.rx05.multiplicative_map_sample`, `rx:complete.rx05.additive_map_sample`.

Full B0 (attained under T213): `subspaces.dim`, `subspaces.member`, `subspaces.not_member`, `subspaces.kernel`.

Registrations: `mor.sets.span` (sage-symbolic).

### T210 — Module rank

V1: `rx:complete.rx06.original_dimension`.

Full B0 (attained under T213): `lattices.rank.a1`, `lattices.rank.a2`, `lattices.rank.a3`.

Registrations: `meth.rank` (sage-modules) ×5.

### T211 — Module kernels

V1: `rx:complete.rx08.kernel_dimension`, `rx:complete.rx08.kernel_zero_composite`.

### T212 — Formed modules

V1: `rx:complete.lift.formed_arrow_action`, `rx:complete.lift.whole_formed_equation`, `rx:complete.lift.first_inverse_on_carrier`, `rx:complete.lift.first_inverse_on_scalar`, `rx:complete.lift.first_defining_map`, `rx:complete.lift.first_backward_action`, `rx:complete.lift.first_nonidentity_coordinate`, `rx:complete.lift.first_full_pairing`, `rx:complete.lift.first_whole_factorization`, `rx:complete.lift.first_factor_comparison`, `rx:complete.lift.first_factor_sample_one`, `rx:complete.lift.first_factor_sample_two`, `rx:complete.lift.actual_second_inclusion`, `rx:complete.lift.composed_forward`, `rx:complete.lift.composed_backward`, `rx:complete.lift.final_inverse_on_carrier`, `rx:complete.lift.final_inverse_on_scalar`, `rx:complete.lift.final_defining_map`, `rx:complete.lift.final_backward_action`, `rx:complete.lift.final_full_pairing`, `rx:complete.lift.final_pairing_sample`, `rx:complete.lift.final_nonzero_inclusion`, `rx:complete.lift.final_whole_factorization`, `rx:complete.lift.final_factor_comparison`, `rx:complete.lift.final_factor_sample_one`, `rx:complete.lift.final_factor_sample_two`, `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.cone_comparison_inverse_right`, `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_defining_equation`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.unique_second_factor`, `rx:complete.rx08.full_projection`, `rx:complete.rx08.restriction_zero_composite`, `rx:complete.rx08.full_coordinate_inclusion`, `rx:complete.rx08.full_restricted_pairing`, `rx:complete.rx08.restricted_pairing_one`.

Full B0 (attained under T213): `formed.card.hyperbolic_fixed`, `formed.card.zero_rank_zero`.

Registrations: `lift.bilin_module.restrict#obj` (sage-bilinear-lift), `lift.bilin_module.restrict#hom` (sage-bilinear-lift), `lift.bilin_module.restrict#forward` (sage-bilinear-lift), `lift.bilin_module.restrict#backward` (sage-bilinear-lift).

### T214 — Group kernels

Full B0: `groups.kernel.sign_card`, `groups.kernel.trivial_card`, `groups.kernel.identity_card`, `groups.alternating.three_card`.

Registrations: `meth.cardinality` (gap-groups) ×3, `prop.is_finite` (gap-groups) ×3, `prop.is_abelian` (gap-groups) ×2, `prop.is_commutative` (gap-groups) ×3, `meth.group_arrow_kernel` (gap-groups), `fun.arrows_groups.kernel` (gap-groups).

### T215 — Boolean algebras

Full B0: `integration.normalized_count`, `integration.normalized`, `finite_sets.union`, `finite_sets.intersection`, `finite_sets.difference`, `finite_sets.symmetric_difference`, `finite_sets.subset_union`, `finite_sets.intersection_subset`, `polynomials.irrational_roots`.

### T216 — Integral lattices

Full B0: `lattices.rank.e8`.

Registrations: `meth.rank` (sage-modules), `meth.cardinality` (sage-modules), `prop.is_abelian` (gap-groups), `prop.is_commutative` (gap-groups).

### T217 — Set constructions

No statement of the workloads has its route in these categories.

### T218 — Well orders

No statement of the workloads has its route in these categories.

### T219 — Algebraic structures

No statement of the workloads has its route in these categories.

### T220 — Algebras

No statement of the workloads has its route in these categories.

### T221 — Schemes

No statement of the workloads has its route in these categories.

### T222 — Module constructions

No statement of the workloads has its route in these categories.

### T223 — Forms over rings

No statement of the workloads has its route in these categories.

### T224 — Lattices and quadratic modules

No statement of the workloads has its route in these categories.

## Routes of the full-B0 files corrected by hand

| Statement | Categories | Reason |
| --- | --- | --- |
| `units.rationals.three_inverse` | `cat.sets`, `cat.magmas`, `cat.semigroups`, `cat.monoids`, `cat.groups`, `cat.rings` | `ℚˣ` is the image of ℚ under `fun.monoids.units` (monoids to groups); the inverse is `op.groups.inverse`; the matcher did not read `ℚˣ`. |
| `groups.kernel.sign_card` | `cat.arrows_groups`, `cat.subobjects_groups`, `cat.groups`, `cat.monoids`, `cat.semigroups`, `cat.magmas`, `cat.sets`, `cat.core_sets`, `cat.cardinals` | `ker()` of a group map is `meth.group_arrow_kernel` (`cat.arrows_groups` to `cat.subobjects_groups`); `|·|` is `fun.sets.cardinality` (`cat.core_sets` to `cat.cardinals`); the matcher did not read the numeral. |
| `groups.kernel.trivial_card` | `cat.arrows_groups`, `cat.subobjects_groups`, `cat.groups`, `cat.monoids`, `cat.semigroups`, `cat.magmas`, `cat.sets`, `cat.core_sets`, `cat.cardinals` | `ker()` of a group map is `meth.group_arrow_kernel` (`cat.arrows_groups` to `cat.subobjects_groups`); `|·|` is `fun.sets.cardinality` (`cat.core_sets` to `cat.cardinals`); the matcher did not read the numeral. |
| `groups.kernel.identity_card` | `cat.arrows_groups`, `cat.subobjects_groups`, `cat.groups`, `cat.monoids`, `cat.semigroups`, `cat.magmas`, `cat.sets`, `cat.core_sets`, `cat.cardinals` | `ker()` of a group map is `meth.group_arrow_kernel` (`cat.arrows_groups` to `cat.subobjects_groups`); `|·|` is `fun.sets.cardinality` (`cat.core_sets` to `cat.cardinals`); the matcher did not read the numeral. |
| `presentations.f9.forward_generator` | `cat.commutative_rings`, `cat.rings`, `cat.monoids`, `cat.semigroups`, `cat.magmas`, `cat.sets` | `F9translation` is `cmp.f9.translation` between `obj.commutative_rings.f9_x` and `obj.commutative_rings.f9_y`, as in RX-07; the matcher did not read the name. |
| `presentations.f9.inverse_generator` | `cat.commutative_rings`, `cat.rings`, `cat.monoids`, `cat.semigroups`, `cat.magmas`, `cat.sets` | `F9translation` is `cmp.f9.translation` between `obj.commutative_rings.f9_x` and `obj.commutative_rings.f9_y`, as in RX-07; the matcher did not read the name. |
| `presentations.f9.forward_constant` | `cat.commutative_rings`, `cat.rings`, `cat.monoids`, `cat.semigroups`, `cat.magmas`, `cat.sets` | `F9translation` is `cmp.f9.translation` between `obj.commutative_rings.f9_x` and `obj.commutative_rings.f9_y`, as in RX-07; the matcher did not read the name. |
| `presentations.f9.inverse_constant` | `cat.commutative_rings`, `cat.rings`, `cat.monoids`, `cat.semigroups`, `cat.magmas`, `cat.sets` | `F9translation` is `cmp.f9.translation` between `obj.commutative_rings.f9_x` and `obj.commutative_rings.f9_y`, as in RX-07; the matcher did not read the name. |

## Probe of countable sets in Sage

Run on 2026-11-25 in the container `sage-research` with `/sage/.venv/bin/python3` (Sage 11.0.beta5): `X.cardinality()`, `X in EnumeratedSets()`, `X in InfiniteEnumeratedSets()` and `X.category()`.

| Set | `cardinality()` | In `EnumeratedSets` | In `InfiniteEnumeratedSets` | Category (first part) |
| --- | --- | --- | --- | --- |
| `ZZ` | `+Infinity` | yes | yes | euclidean domains, noetherian rings, infinite enumerated sets, metric spaces |
| `NN` | `+Infinity` | yes | yes | facade infinite enumerated commutative semirings |
| `QQ` | `+Infinity` | no | no | number fields, quotient fields, metric spaces |
| `ImageSet(lambda n: 2*n, NN, is_injective=True)` | `+Infinity` | yes | yes | infinite enumerated subobjects of sets |
| `cartesian_product([ZZ, ZZ])` | `+Infinity` | no | no | Cartesian products of commutative rings, of metric spaces, of enumerated sets |
| `FreeModule(ZZ, 2)` | `+Infinity` | no | no | finite dimensional modules with basis over ℤ |
| `IntegralLattice("A2")` | `+Infinity` | not run | no | finite dimensional modules with basis over ℤ, subobjects of sets |
| `FreeModule(ZZ, 0)` | `1` | not run | no | finite enumerated finite dimensional modules with basis |
