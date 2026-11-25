# Category scope: the rows that the computations need, by category and version (snapshot of 2026-11-25)

This record works back from each computation to the categories, operations, constructors, functors and properties that must exist to compute it. It gives one entry for each category that a computation needs, in structural order, with the catalogue rows of the category, the statements that need each row, the version in which the row is first needed, the existing registrations and the recommended engine. It is the data for a roadmap with one specification and versioned milestones for each category implementation. It reads fixed revisions and is not kept current.

## Inputs and regeneration

| Input | Content used |
| --- | --- |
| `workload-routes.json` | the 287 permanent and extension statements: rows, route categories, rules (`why`), question kind |
| `milestones.json` | the kernel V1 statements (134 extension statements and 15 K1 identifiers), the milestone of each category, the order of the milestones |
| `scaffolding.json` | layers, inferred layers and inputs of the categories; structural functors and classifier forgets; non-structural functors |
| `existing-leaves.json` | the 115 registrations of lean-cas-dsl-leaves |
| `spike-inventory.json` | the spike computations and their statements, the proposed statements with their rows and routes, the rows of the 18 K3 and K14 statements, the missing catalogue rows |
| `engine-survey.md` | the table "Recommendation summary" |

`category_scope.py` in this directory reads these inputs and writes `category-scope.json`: run `uv run category_scope.py` here. It uses the Python standard library only. The tables of this document come from `category-scope.json`.

## Rules

**Versions of a statement.**

| Version | Statements |
| --- | --- |
| V1 | a workload statement that carries a computation of `spike-inventory.md`; a statement that the inventory proposes for a spike computation; a kernel V1 statement of `milestones.json` (the 134 extension statements and the 15 K1 identifiers of #24) |
| V2 | every other statement of #19 (K1 to K14): the other permanent statements and the 18 statements of the K3 and K14 files |
| V3 | the classified Sage coverage of #20, #21 and #23. No such statement exists yet; when tasks T140 to T147 produce the classified statements, a row joins the V3 of its category by the same rules |

A typing judgement (question kind `settled`, or a proposed statement that the matcher reads as a judgement) computes nothing and gives no version. A statement of a spike ceiling has no version.

**Rows of a statement.** Its catalogue rows, and the structural functors and classifier forgets of `scaffolding.json` whose two ends are on its route (the edge `fun.sets.whole_subset` is cut, as in the layers). A structural functor between two route categories is listed also where the carrier route of the statement does not pass through it.

**Version of a row.** The first version of a computed statement that needs it.

**Home category of a row.** The latest category, in the structural order, among the catalogue owners of the row and the categories of its declared parameters. A functor has its two ends as owners. A structural functor or classifier forget of a route belongs to its source. Reason: a row can be implemented only when every category that it is declared over or parameterized by is implemented, and the implementation of the last of them supplies it. For example `mor.sets.matrix_det` is owned by `cat.sets` with the parameter `K : CommRingCat`, so its home is `cat.commutative_rings`. In the same way `milestones.md` moves the registration of `mor.sets.companion_matrix` to the milestone T205 of the commutative rings.

**Structural order.** The order of the milestones of `milestones.json`, which applies the layers of `scaffolding.json` and the rule of `plan.md` for the categories with no chain to `cat.sets`; then the layer, or for a category with no chain the inferred layer with inputs; then the identifier. In the tables a layer in parentheses is an inferred layer; "root" is a category with no inputs, which enters with the first milestone that needs it; "—" is a category with no layer and no inferred inputs at this revision (`cat.ideals_r`, which `plan.md` places in T222 after the upstream tasks T118 and T227).

**Registrations.** A registration of `existing-leaves.json` belongs to the latest of the home category of its operation, the category of its operation and the category of its input.

**Engine.** The family of the category in the table "Recommendation summary" of `engine-survey.md`. A calculus row (limits, integrals, Taylor expansions, the real functions) also names the family Calculus. `cat.schemes_over_ring` has no family in the survey.

## Counts

| Quantity | Count |
| --- | ---: |
| Computed V1 statements | 337 |
| Computed V2 statements | 40 |
| Typing judgements (no computation) | 22 |
| Statements of spike ceilings (no version) | 21 |
| Categories with an entry | 38 |
| V1 rows | 243 |
| V2 rows | 25 |

| Version | Class of statement | Computed statements |
| --- | --- | ---: |
| V1 | extension workload statement | 134 |
| V1 | permanent workload statement | 112 |
| V1 | proposed statement | 91 |
| V2 | full-B0 file statement | 18 |
| V2 | permanent workload statement | 22 |

## Summary

| Category | Layer | Milestone | V1 rows | V2 rows | Statements | Engine (survey primary) |
| --- | ---: | --- | ---: | ---: | ---: | --- |
| `cat.cardinals` | root | T200 Sets | 1 | 0 | 58 | Cardinals: Sage `Integer` for finite |
| `cat.sets` | 0 | T200 Sets | 72 | 0 | 373 | Calculus: SymPy; Sets: Sage |
| `cat.core_sets` | (2) | T200 Sets | 6 | 0 | 57 | Sets: Sage |
| `cat.finite_sets` | 1 | T201 Finite sets | 3 | 2 | 5 | Finite, countable, enumerated sets: Sage |
| `cat.linear_orders` | 2 | T202 Orders | 9 | 0 | 13 | Order structures: Sage posets |
| `cat.additive_monoids` | 1 | T203 Rings | 4 | 0 | 13 | Magmas, semigroups, monoids: GAP (with Semigroups) through `libgap` |
| `cat.magmas` | 1 | T203 Rings | 3 | 0 | 305 | Magmas, semigroups, monoids: GAP (with Semigroups) through `libgap` |
| `cat.additive_commutative_monoids` | 2 | T203 Rings | 1 | 0 | 5 | Magmas, semigroups, monoids: GAP (with Semigroups) through `libgap` |
| `cat.semigroups` | 2 | T203 Rings | 2 | 0 | 305 | Magmas, semigroups, monoids: GAP (with Semigroups) through `libgap` |
| `cat.monoids` | 3 | T203 Rings | 7 | 0 | 305 | Magmas, semigroups, monoids: GAP (with Semigroups) through `libgap` |
| `cat.groups` | 4 | T203 Rings | 10 | 8 | 95 | Groups: GAP through Sage |
| `cat.semirings` | 4 | T203 Rings | 7 | 0 | 41 | Semirings: Sage |
| `cat.additive_groups` | 5 | T203 Rings | 2 | 0 | 64 | Groups: GAP through Sage |
| `cat.rings` | 6 | T203 Rings | 16 | 0 | 304 | Rings, commutative rings: Sage |
| `cat.core_groups` | (6) | T204 Group automorphisms | 0 | 0 | 13 | Groups: GAP through Sage |
| `cat.commutative_rings` | 7 | T205 Commutative rings | 44 | 2 | 198 | Rings, commutative rings: Sage |
| `cat.hausdorff_topological_commutative_monoids` | 3 | T206 Topological monoids | 4 | 0 | 5 | Polynomial rings: Sage |
| `cat.modules_total` | 6 | T207 Modules | 3 | 0 | 64 | Modules: Sage |
| `cat.modules_r` | 7 | T207 Modules | 8 | 1 | 73 | Modules: Sage |
| `cat.bil_wform` | 8 | T208 Bilinear forms | 3 | 3 | 11 | Bilinear and quadratic modules: Sage |
| `cat.fields` | 8 | T209 Fields | 5 | 0 | 27 | Fields: Sage |
| `cat.core_modules_r` | (9) | T210 Module rank | 1 | 2 | 6 | Modules: Sage |
| `cat.subobjects_sets` | 1 | T211 Module kernels | 1 | 0 | 1 | Sets: Sage |
| `cat.subobjects_modules_r` | 2 | T211 Module kernels | 0 | 0 | 6 | Modules: Sage |
| `cat.arrows_modules_r` | (9) | T211 Module kernels | 3 | 0 | 6 | Modules: Sage |
| `cat.core_subobjects_modules_r` | (9) | T211 Module kernels | 1 | 0 | 1 | Modules: Sage |
| `cat.bilin_module` | 9 | T212 Formed modules | 15 | 1 | 42 | Bilinear and quadratic modules: Sage |
| `cat.arrows_bilin_module` | (11) | T212 Formed modules | 2 | 0 | 29 | Bilinear and quadratic modules: Sage |
| `cat.subobjects_groups` | 5 | T214 Group kernels | 0 | 2 | 4 | Groups: GAP through Sage |
| `cat.arrows_groups` | (6) | T214 Group kernels | 0 | 2 | 3 | Groups: GAP through Sage |
| `cat.boolean_algebras` | 1 | T215 Boolean algebras | 7 | 0 | 14 | Boolean algebras, power sets: Sage |
| `cat.integral_lattice` | 10 | T216 Integral lattices | 0 | 2 | 1 | Lattices (quadratic forms): Sage |
| `cat.enumerated_sets` | 1 | T217 Set constructions | 1 | 0 | 2 | Finite, countable, enumerated sets: Sage |
| `cat.core_subobjects_sets` | (2) | T217 Set constructions | 0 | 0 | 1 | Sets: Sage |
| `cat.subsets.subset_predicates` | (3) | T217 Set constructions | 1 | 0 | 1 | Sets: Sage |
| `cat.algebras` | 8 | T220 Algebras | 0 | 0 | 0 | Algebras: Sage |
| `cat.schemes_over_ring` | (8) | T221 Schemes | 0 | 0 | 0 | not in the survey |
| `cat.ideals_r` | — | T222 Module constructions | 1 | 0 | 1 | Modules: Sage |
| **Total: 38 categories** | | | **243** | **25** | | |

## Catalogue rows that a computation needs and the catalogue lacks

Each row is an upstream input of lean-categories. The proposed statements and inventory rows are those of `spike-inventory.md`; an X row is a spike ceiling.

| Missing row | Needed for | Description | Needed by (proposed statement: inventory row) |
| --- | --- | --- | --- |
| `missing.real_approximation` | V1 | A rational approximation of a real number within a positive rational tolerance: for $x \in \mathbb{R}$ and $\varepsilon \in \mathbb{Q}_{>0}$, a chosen $a \in \mathbb{Q}$ with $|x - a| < \varepsilon$ (a choice-bearing operation; the chosen decimal is retained with the exact source and both tolerances). | N17.1: N17, X03.1: X03 |
| `missing.ufd_factorization` | V1 | The factorization of a nonzero element of a unique factorization domain into a unit and irreducible factors with multiplicities, for $\mathbb{Z}$ (the catalogue has it for $\mathbb{N}^{+}$ through `mor.sets.nat_prime_factors` and `mor.sets.nat_multiplicity`, and for $R[x]$ through `mor.sets.polynomial_factorization`). | N06.1: N06 |
| `missing.ufd_prime` | V1 | Primality of an element of a commutative ring ($x$ prime when $(x)$ is a nonzero prime ideal), for $\mathbb{Z}$, so that $-7$ is prime and $0$, $1$ are not (the catalogue has `mor.sets.nat_is_prime` on $\mathbb{N}$ only). | N29.1: N29 |
| `missing.complex_sqrt` | V1 | A chosen square root in $\mathbb{C}$ of a negative rational, $\sqrt{-4} = 2i$ (the catalogue has `mor.sets.real_sqrt` on $\mathbb{R}$ only). | N18.3: N18 |
| `missing.cardinal_power` | V1 | Exponentiation of cardinals, $2^{\kappa}$ (Mathlib `Cardinal.power`), so that $|\mathcal{P}(A)| = 2^{|A|}$ can be stated (the catalogue has the cardinal literals `lit.cardinals` and no operation on `cat.cardinals`). | F08.1: F08, X06.1: X06 |
| `missing.denumerable_enumeration` | V1 | The enumeration $\mathbb{N} \to X$ of a denumerable set in the adopted `Denumerable.ofNat` order ($\mathbb{Z}$: $0, -1, 1, -2, 2, \ldots$; $\mathbb{Q}$: $0, -1, -1/2, 1, 1/2, \ldots$) and its evaluation $X[k]$; objects of `cat.enumerated_sets` for $\mathbb{N}$, $\mathbb{Z}$, $\mathbb{Q}$ and the progressions (the category and its classifier exist; no object or morphism row does). | N25.1: N25, N25.2: N25 |
| `missing.root_multiset` | V1 | The multiset of roots of a nonzero polynomial over a domain, with multiplicity (Mathlib `Polynomial.roots`); `mor.sets.polynomial_roots` gives the finite root set $R[x] \setminus \{0\} \to \mathcal{P}_{\mathrm{fin}}(R)$. | P13.1: P13 |
| `missing.derivative_linear` | V1 | The derivation $d/dx : \mathbb{Q}[x] \to \mathbb{Q}[x]$ as a morphism of $\mathbb{Q}$-modules, so that its kernel is a subobject (`mor.sets.polynomial_derivative` is a map of sets). | I01.1: I01 |
| `missing.series_truncation` | V1 | The truncation $R[[t]] \to R[[t]]/(t^{n})$ (the quotient by $(t^{n})$, an $R$-algebra map) with its display $\sum_{k<n} a_k t^k + O(t^{n})$. | L07.2: L07, L09.2: L09, E10.1: E10 |
| `missing.linear_map_from_formula` | V1 | A linear map $\mathbb{Q}^{n} \to \mathbb{Q}^{m}$ given by a formula $(x_1, \ldots, x_n) \mapsto (\ldots)$ linear in its binders, as a morphism of `cat.modules_r` with its kernel and image (`mor.modules.row_linear_map` and `mor.modules.matrix_linear_map` take a matrix). | W04.1: W04, W08.1: W08, W09.1: W09, W09.2: W09, W09.3: W09 |
| `missing.module_annihilator_value` | V1 | Objects of `cat.ideals_r` (the principal ideal $(4) \subseteq \mathbb{Z}$) so that `meth.annihilator` has a value to compare with; `cat.ideals_r` has no object row. | R01.1: R01 |
| `missing.cyclic_module_object` | V1 | The ℤ-module $\mathbb{Z}/4$ as an object of `cat.modules_r` (written `ℤ/4 in Modules(ℤ)`); the module rows are `obj.modules.regular`, `obj.modules.vectors` and the restricted regular module. | R01.1: R01, R02.1: R02, R03.1: R03 |
| `missing.power_series_inclusion` | V1 | The inclusion $\mathbb{Q}[[t]] \subseteq \mathbb{R}[[t]]$ induced by $\mathbb{Q} \subseteq \mathbb{R}$ (the catalogue inclusions are those of the number systems). | Q02.1: Q02 |
| `missing.real_arctan` | ceiling only | The real function $\arctan$ (the catalogue functions are `mor.sets.real_sin`, `real_cos`, `real_exp`, `real_sqrt`, `real_pi`). | X17.1: X17 |
| `missing.polynomial_gcd` | ceiling only | The gcd of two polynomials over a UFD (`mor.sets.gcd` is the gcd of integers). | X11.1: X11 |
| `missing.polynomial_irreducible` | ceiling only | Irreducibility of a nonzero polynomial over a domain (a prime element of $R[x]$). | X10.1: X10 |
| `missing.uncountable_cardinal` | ceiling only | The cardinal $2^{\aleph_0}$ of $\mathbb{R}$ (no statement of the workloads needs an uncountable cardinal; the plan records it). | X06.1: X06 |
| `missing.matrix_inverse_domain` | V1 | Membership in the unit group $\mathrm{Mat}_n(K)^{\times}$ as a decided predicate (the workloads read $M$ in $\mathrm{Mat}_2(\mathbb{Q})^{\times}$ as an ascription). | M11.1: M11 |

## Categories

### `cat.cardinals` (Card)

Layer root; built from —; milestone T200 Sets (M2); 58 computed statements on routes through it (42 V1, 16 V2).

Engine family **Cardinals**: primary Sage `Integer` for finite; fallback None for infinite.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `lit.cardinals` | operation | V1 | cardinals | — | `F08.1`, `F08.2`, `I04.1`, `N26.1`, `N26.2`, `P13.1` and 35 more | `finite_sets.card.three`, `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `groups.alternating.three_card`, `groups.kernel.identity_card` and 10 more |

Existing registrations: none.

### `cat.sets` (Sets)

Layer 0; built from —; milestone T200 Sets (M2); 373 computed statements on routes through it (336 V1, 37 V2).

Engine family **Calculus**: primary SymPy; fallback Sage symbolic ring to Maxima, FriCAS, Giac; mpmath.

Engine family **Sets**: primary Sage; fallback SymPy sets; Catlab or CAP for general limits and colimits.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.sets` | category | V1 | sets | — | `rx:addition.rx02.core_identity_action`, `rx:addition.rx02.full_inverse_action`, `rx:addition.rx02.nonidentity_input`, `rx:addition.rx02.whole_direct_image`, `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple` and 32 more | — |
| `clf.sets.binary_operation` | classifier | V1 | sets | — | `rx:complete.lift.whole_formed_equation`, `rx:complete.rx05.additive_cardinality`, `rx:complete.rx05.additive_map_sample`, `rx:complete.rx05.complete_component`, `rx:complete.rx05.complete_inverse_component`, `rx:complete.rx05.component_left_inverse` and 4 more | — |
| `clf.sets.enumerated` | classifier | V1 | sets | — | `N25.1`, `N25.2` | — |
| `clf.sets.finite` | classifier | V1 | sets | — | `finite_sets.limit.pullback.card`, `rx:complete.rx04.cardinality`, `rx:complete.rx04.forgotten_refinement_cardinality`, `sets.finite.fin2_times_z3`, `sets.finite.integers` | `finite_sets.card.three`, `sets.finite.fin2_sqcup_fin3` |
| `cmp.sets.fin_reversal` | comparison (presentation or cell) | V1 | sets | — | `rx:addition.rx02.actual_backward`, `rx:addition.rx02.actual_forward`, `rx:addition.rx02.nonidentity_input`, `rx:addition.rx02.whole_direct_image` | — |
| `cmp.sets.singleton_terminal` | comparison (presentation or cell) | V1 | sets | — | `I06.1` | — |
| `obj.sets.complexes` | object constructor | V1 | sets | — | `K03.1`, `K04.1`, `K05.1`, `N18.3`, `N20.2`, `N21.1` and 21 more | — |
| `obj.sets.continuous_maps` | object constructor | V1 | sets | — | `calculus.integral_sine`, `calculus.integral_square` | — |
| `obj.sets.convergent_maps_at_infinity` | object constructor | V1 | sets | — | `L03.1` | — |
| `obj.sets.cyclic_quotient` | object constructor | V1 | sets | — | `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.double_class_one`, `rx:addition.rx03.double_class_three`, `rx:addition.rx03.triple_class_two` | — |
| `obj.sets.f9_x` | object constructor | V1 | sets | — | `rx:complete.rx07.coefficients_backward`, `rx:complete.rx07.coefficients_forward`, `rx:complete.rx07.full_backward_map`, `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_map_inverse`, `rx:complete.rx07.full_square_map` and 3 more | `presentations.f9.forward_generator`, `presentations.f9.inverse_generator` |
| `obj.sets.f9_y` | object constructor | V1 | sets | — | `rx:complete.rx07.coefficients_backward`, `rx:complete.rx07.coefficients_forward`, `rx:complete.rx07.full_backward_map`, `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_square_map`, `rx:complete.rx07.map_sample_backward` and 1 more | `presentations.f9.forward_generator`, `presentations.f9.inverse_generator` |
| `obj.sets.fin` | object constructor | V1 | sets | — | `N18.3`, `N20.2`, `rx:addition.rx02.actual_backward`, `rx:addition.rx02.actual_forward`, `rx:addition.rx02.core_identity_action`, `rx:addition.rx02.core_map_composition` and 13 more | `refinement.finite_product_card`, `sets.card.square`, `sets.finite.fin2_sqcup_fin3` |
| `obj.sets.finite_subsets` | object constructor | V1 | sets | — | `P10.1`, `P12.1`, `P12.2`, `P13.1`, `P14.1`, `P14.2` and 12 more | — |
| `obj.sets.integer_square_bound` | object constructor | V1 | sets | — | `rx:complete.rx04.cardinality`, `rx:complete.rx04.finite_classifier`, `rx:complete.rx04.forgotten_refinement_cardinality` | — |
| `obj.sets.integers` | object constructor | V1 | sets | — | `C04.1`, `C04.2`, `C05.1`, `E10.1`, `F08.1`, `F13.1` and 66 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic` |
| `obj.sets.integers_mod` | object constructor | V1 | sets | — | `numbers.zmod5.sum`, `rx:complete.rx06.cartesian_whole_carrier`, `rx:complete.rx07.full_backward_map`, `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_map_inverse`, `rx:complete.rx07.full_square_map` and 5 more | `numbers.zmod5.difference`, `numbers.zmod5.product`, `numbers.zmod7.distributive`, `numbers.zmod7.value`, `sets.card.square` |
| `obj.sets.integers_mod_power` | object constructor | V1 | sets | — | `sets.card.z4_cubed`, `sets.card.z5_empty_power`, `sets.card.z7` | — |
| `obj.sets.naturals` | object constructor | V1 | sets | — | `C12.1`, `C13.1`, `C14.1`, `E10.1`, `F15.1`, `H06.1` and 33 more | `lattices.rank.e8`, `several_variables.plane` |
| `obj.sets.positive_naturals` | object constructor | V1 | sets | — | `factorization.multiplicity_seven`, `factorization.multiplicity_three`, `factorization.multiplicity_two`, `factorization.prime_factors` | — |
| `obj.sets.power_set` | object constructor | V1 | sets | — | `F08.1`, `F08.2`, `F13.1`, `F14.1`, `I06.1`, `I10.1` and 36 more | — |
| `obj.sets.primes` | object constructor | V1 | sets | — | `factorization.multiplicity_seven`, `factorization.multiplicity_three`, `factorization.multiplicity_two`, `factorization.prime_factors` | — |
| `obj.sets.rationals` | object constructor | V1 | sets | — | `C15.1`, `I01.1`, `I03.1`, `I04.1`, `I06.1`, `I09.1` and 111 more | `fractions.cancel`, `fractions.halves`, `fractions.lowest_terms`, `inverses.det`, `numbers.rationals.sum`, `several_variables.plane` and 2 more |
| `obj.sets.reals` | object constructor | V1 | sets | — | `H05.1`, `L03.1`, `L07.1`, `L07.2`, `L09.1`, `L09.2` and 24 more | — |
| `obj.sets.smooth_maps` | object constructor | V1 | sets | — | `L07.1`, `L07.2`, `L09.1`, `L09.2` | — |
| `obj.sets.truth_values` | object constructor | V1 | sets | — | `N29.1`, `N29.2`, `rx:complete.rx02.singleton_excluded`, `rx:complete.rx03.second_power_nonidentity`, `rx:complete.rx04.ambient_not_finite`, `rx:complete.rx05.operations_distinct` and 1 more | `groups.abelian.symmetric_three` |
| `obj.sets.vectors` | object constructor | V1 | sets | — | `M12.1`, `M12.2`, `W04.1`, `W05.1`, `W05.2`, `W06.1` and 33 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic` |
| `bind.sets.finite_product` | operation | V1 | sets | — | `F16.2`, `K04.1`, `P15.3`, `composed.root_product` | — |
| `bind.sets.finite_sum` | operation | V1 | sets | — | `F16.1`, `F16.3`, `K03.1`, `M12.2`, `composed.root_sum` | — |
| `bind.sets.integral` (Calculus) | operation | V1 | sets | — | `calculus.integral_sine`, `calculus.integral_square` | — |
| `bind.sets.limit` (Calculus) | operation | V1 | sets | — | `calculus.limit_sinc` | — |
| `bind.sets.limit_at_infinity` (Calculus) | operation | V1 | sets | — | `calculus.limit_infinity` | — |
| `bind.sets.power_series_sum` | operation | V1 | sets | — | `E10.1`, `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.full_coefficients` | — |
| `colim.sets.coproduct` | operation | V1 | sets | — | `sets.card.fin2_sqcup_fin3` | `sets.finite.fin2_sqcup_fin3` |
| `graph.sets` | operation | V1 | sets | — | `sets.limit.pullback.card` | — |
| `incl.sets.integers_rationals` | operation | V1 | sets | — | `N22.1`, `N27.1`, `Q01.2`, `matrices.det` | — |
| `incl.sets.naturals_degrees` | operation | V1 | sets | — | `differentials.degree`, `polynomials.degree`, `polynomials.degree_over_rationals` | — |
| `incl.sets.naturals_integers` | operation | V1 | sets | — | `E10.1`, `series.coefficient_four`, `series.coefficient_three`, `series.coefficient_two`, `series.coefficient_zero` | — |
| `incl.sets.naturals_krull_dimensions` | operation | V1 | sets | — | `several_variables.dimension` | `several_variables.plane` |
| `incl.sets.rationals_reals` | operation | V1 | sets | — | `N20.1`, `N27.1`, `Q01.1`, `Q01.2`, `Q02.1`, `calculus.integral_square` | — |
| `incl.sets.reals_complexes` | operation | V1 | sets | — | `N20.2`, `N21.1`, `N21.2`, `N27.1`, `Q01.1`, `Q01.2` and 1 more | — |
| `lim.sets.product` | operation | V1 | sets | — | `I03.1`, `K03.1`, `K04.1`, `K05.1`, `M12.1`, `M12.2` and 113 more | `fractions.cancel`, `fractions.halves`, `fractions.lowest_terms`, `inverses.det`, `numbers.rationals.sum`, `numbers.zmod5.difference` and 6 more |
| `lim.sets.pullback` | operation | V1 | sets | — | `finite_sets.limit.pullback.card`, `sets.limit.pullback.card` | — |
| `lit.sets.finite_subsets` | operation | V1 | sets | — | `C05.1`, `C12.1`, `C13.1`, `C14.1`, `C15.1`, `F08.1` and 50 more | — |
| `mor.sets.complex_abs` | operation | V1 | sets | — | `N17.1`, `N21.2`, `factorization.approximation`, `fractions.modulus`, `numbers.complex.abs` | — |
| `mor.sets.complex_bar` | operation | V1 | sets | — | `numbers.complex.bar`, `numbers.complex.norm` | — |
| `mor.sets.complex_i` | operation | V1 | sets | — | `N18.3`, `N20.2`, `fractions.modulus`, `numbers.complex.abs`, `numbers.complex.bar`, `numbers.complex.im` and 2 more | — |
| `mor.sets.complex_im` | operation | V1 | sets | — | `N21.1`, `numbers.complex.im` | — |
| `mor.sets.complex_re` | operation | V1 | sets | — | `numbers.complex.re` | — |
| `mor.sets.cyclic_quotient_map` | operation | V1 | sets | — | `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.double_class_one`, `rx:addition.rx03.double_class_three`, `rx:addition.rx03.triple_class_two` | — |
| `mor.sets.direct_image` | operation | V1 | sets | — | `C12.1`, `C13.1` | — |
| `mor.sets.equality` | operation | V1 | sets | — | `C05.1`, `C12.1`, `C13.1`, `C15.1`, `E10.1`, `F08.1` and 190 more | `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `groups.abelian.symmetric_three`, `presentations.f9.forward_constant`, `presentations.f9.forward_generator`, `presentations.f9.inverse_constant` and 2 more |
| `mor.sets.f9_x_constants` | operation | V1 | sets | — | `rx:complete.rx07.coefficients_backward`, `rx:complete.rx07.coefficients_forward`, `rx:complete.rx07.full_backward_map`, `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_map_inverse`, `rx:complete.rx07.full_square_map` and 3 more | `presentations.f9.forward_constant`, `presentations.f9.inverse_constant` |
| `mor.sets.f9_y_constants` | operation | V1 | sets | — | `rx:complete.rx07.coefficients_backward`, `rx:complete.rx07.coefficients_forward`, `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_square_map` | `presentations.f9.forward_constant`, `presentations.f9.inverse_constant` |
| `mor.sets.fin_rev` | operation | V1 | sets | — | `rx:addition.rx02.actual_backward`, `rx:addition.rx02.actual_forward`, `sets.eq.rev_rev` | `sets.apply.rev`, `sets.apply.rev_rev` |
| `mor.sets.gcd` | operation | V1 | sets | — | `N04.1`, `numbers.gcd` | — |
| `mor.sets.infinity` | operation | V1 | sets | — | `calculus.limit_infinity` | — |
| `mor.sets.integer_square_bound_admitted` | operation | V1 | sets | — | `rx:complete.rx04.admission_retains_subset`, `rx:complete.rx04.cardinality`, `rx:complete.rx04.forgotten_refinement_cardinality` | — |
| `mor.sets.integer_square_bound_subset` | operation | V1 | sets | — | `rx:complete.rx04.admission_retains_subset`, `rx:complete.rx04.cardinality`, `rx:complete.rx04.exact_members`, `rx:complete.rx04.exact_predicate`, `rx:complete.rx04.forgotten_refinement_cardinality` | — |
| `mor.sets.nat_is_prime` | operation | V1 | sets | — | `N29.2`, `ellipses.not_prime`, `ellipses.prime` | — |
| `mor.sets.nat_multiplicity` | operation | V1 | sets | — | `factorization.multiplicity_seven`, `factorization.multiplicity_three`, `factorization.multiplicity_two` | — |
| `mor.sets.nat_prime_factors` | operation | V1 | sets | — | `factorization.prime_factors` | — |
| `mor.sets.real_exp` (Calculus) | operation | V1 | sets | — | `L07.1`, `L07.2` | — |
| `mor.sets.real_pi` | operation | V1 | sets | — | `calculus.integral_sine` | — |
| `mor.sets.real_sin` (Calculus) | operation | V1 | sets | — | `L03.1`, `L09.1`, `L09.2`, `calculus.integral_sine`, `calculus.limit_sinc` | — |
| `mor.sets.real_sqrt` | operation | V1 | sets | — | `K05.1`, `N17.1`, `N18.1`, `N18.2`, `N19.1`, `N19.2` and 13 more | — |
| `mor.sets.taylor_expansion` (Calculus) | operation | V1 | sets | — | `L07.1`, `L07.2`, `L09.1`, `L09.2` | — |
| `mor.sets.tuple_cons` | operation | V1 | sets | — | `M12.1`, `M12.2`, `W08.1`, `W09.1`, `inverses.left`, `inverses.right` and 14 more | — |
| `mor.sets.tuple_empty` | operation | V1 | sets | — | `M12.1`, `M12.2`, `W08.1`, `W09.1`, `inverses.left`, `inverses.right` and 14 more | — |
| `num.sets.fin` | operation | V1 | sets | — | `finite_sets.limit.pullback.card`, `numbers.zmod5.sum`, `rx:addition.rx02.nonidentity_input`, `rx:complete.rx01.ordinary_relation`, `rx:complete.rx01.reverse_relation`, `rx:complete.rx02.singleton_excluded` and 1 more | `numbers.zmod5.difference`, `numbers.zmod5.negation`, `numbers.zmod5.product`, `numbers.zmod7.distributive`, `numbers.zmod7.value`, `sets.apply.rev` and 1 more |
| `pow.sets` | operation | V1 | sets | — | `C04.1`, `C04.2`, `C05.1`, `C12.1`, `C13.1`, `C14.1` and 54 more | — |
| `prop.is_finite` | property | V1 | sets | — | `rx:complete.rx04.ambient_not_finite`, `rx:complete.rx04.finite_classifier` | — |

Existing registrations (32): `bind.sets.integral` on `cat.sets` (sage-symbolic); `bind.sets.limit` on `cat.sets` (sage-symbolic); `bind.sets.limit_at_infinity` on `cat.sets` (sage-symbolic); `colim.sets.coproduct` on `cat.sets` (sage-set-limits); `lim.sets.product` on `cat.sets` (sage-set-limits); `lim.sets.pullback` on `cat.sets` (sage-set-limits); `mor.sets.complex_abs` on `obj.sets.complexes` (sage-symbolic); `mor.sets.complex_bar` on `obj.sets.complexes` (sage-symbolic); `mor.sets.complex_im` on `obj.sets.complexes` (sage-symbolic); `mor.sets.complex_re` on `obj.sets.complexes` (sage-symbolic); `mor.sets.equality` on `mor.sets.equality` (sage-symbolic); `mor.sets.f9_x_constants` on `mor.sets.f9_x_constants` (sage-presentations); `mor.sets.f9_x_constants` on `obj.sets.integers_mod` (sage-presentations); `mor.sets.f9_y_constants` on `mor.sets.f9_y_constants` (sage-presentations); `mor.sets.f9_y_constants` on `obj.sets.integers_mod` (sage-presentations); `mor.sets.fin_rev` on `mor.sets.fin_rev` (sage-fin-rev); `mor.sets.nat_prime_factors` on `obj.sets.positive_naturals` (sage-symbolic); `mor.sets.real_sqrt` on `obj.sets.reals` (sage-symbolic); `prop.is_finite` on `obj.sets.complexes` (sage); `prop.is_finite` on `obj.sets.f9_x` (sage-presentations); `prop.is_finite` on `obj.sets.f9_y` (sage-presentations); `prop.is_finite` on `obj.sets.fin` (sage); `prop.is_finite` on `obj.sets.integers` (sage); `prop.is_finite` on `obj.sets.integers_mod` (gap); `prop.is_finite` on `obj.sets.integers_mod_power` (gap); `prop.is_finite` on `obj.sets.naturals` (sage); `prop.is_finite` on `obj.sets.permutations` (gap-groups); `prop.is_finite` on `obj.sets.positive_naturals` (sage); `prop.is_finite` on `obj.sets.primes` (sage); `prop.is_finite` on `obj.sets.rationals` (sage); `prop.is_finite` on `obj.sets.reals` (sage); `prop.is_finite` on `obj.sets.units` (gap-groups).

### `cat.core_sets`

Layer (2); built from `cat.sets`; milestone T200 Sets (M2); 57 computed statements on routes through it (45 V1, 12 V2).

Engine family **Sets**: primary Sage; fallback SymPy sets; Catlab or CAP for general limits and colimits.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.core_sets.two_subsets` | functor (object and morphism actions) | V1 | core_sets, sets | — | `rx:addition.rx02.core_identity_action`, `rx:addition.rx02.core_map_composition`, `rx:addition.rx02.full_inverse_action`, `rx:addition.rx02.whole_direct_image`, `rx:complete.rx02.cardinality` | — |
| `fun.sets.cardinality` | functor (object and morphism actions) | V1 | cardinals, core_sets | — | `F08.1`, `F08.2`, `I04.1`, `N26.1`, `N26.2`, `P13.1` and 28 more | `finite_sets.card.three`, `groups.kernel.identity_card`, `groups.kernel.sign_card`, `groups.kernel.trivial_card`, `lattices.card.a0`, `lattices.card.a2` and 1 more |
| `obj.sets.two_subsets` | object constructor | V1 | core_sets, sets | — | `rx:addition.rx02.core_identity_action`, `rx:addition.rx02.full_inverse_action`, `rx:addition.rx02.whole_direct_image`, `rx:complete.rx02.singleton_excluded` | — |
| `meth.cardinality` | operation | V1 | cardinals, core_sets, sets | — | `rx:complete.rx01.ordinary_cardinality`, `rx:complete.rx01.reverse_cardinality`, `rx:complete.rx02.cardinality`, `rx:complete.rx03.cardinality`, `rx:complete.rx04.cardinality`, `rx:complete.rx04.forgotten_refinement_cardinality` and 5 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `groups.alternating.three_card`, `refinement.finite_product_card` |
| `meth.two_subsets` | operation | V1 | core_sets, sets | — | `rx:complete.rx02.cardinality` | — |
| `mor.core_sets.fin_rev` | operation | V1 | core_sets | — | `rx:addition.rx02.core_identity_action`, `rx:addition.rx02.core_map_composition`, `rx:addition.rx02.full_inverse_action`, `rx:addition.rx02.whole_direct_image` | — |

Existing registrations (14): `meth.cardinality` on `cat.sets` (sage-set-limits); `meth.cardinality` on `obj.sets.f9_x` (sage-presentations); `meth.cardinality` on `obj.sets.f9_y` (sage-presentations); `meth.cardinality` on `obj.sets.fin` (sage); `meth.cardinality` on `obj.sets.integers` (sage); `meth.cardinality` on `obj.sets.integers_mod` (gap); `meth.cardinality` on `obj.sets.integers_mod_power` (gap); `meth.cardinality` on `obj.sets.naturals` (sage); `meth.cardinality` on `obj.sets.permutations` (gap-groups); `meth.cardinality` on `obj.sets.positive_naturals` (sage); `meth.cardinality` on `obj.sets.power_set` (sage-power-set); `meth.cardinality` on `obj.sets.primes` (sage); `meth.cardinality` on `obj.sets.rationals` (sage); `meth.cardinality` on `obj.sets.units` (gap-groups).

### `cat.finite_sets` (FiniteSets)

Layer 1; built from —; milestone T201 Finite sets (M2); 5 computed statements on routes through it (3 V1, 2 V2).

Engine family **Finite, countable, enumerated sets**: primary Sage; fallback SymPy.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.finite_sets` | category | V2 | finite_sets | — | — | `refinement.finite_product_card` |
| `forget[clf.sets.finite]` | classifier forget (object and morphism actions) | V1 | finite_sets, sets | — | `finite_sets.limit.pullback.card`, `rx:complete.rx04.cardinality`, `rx:complete.rx04.forgotten_refinement_cardinality` | `finite_sets.card.three`, `refinement.finite_product_card` |
| `obj.finite_sets.fin` | object constructor | V2 | finite_sets | — | — | `finite_sets.card.three` |
| `obj.finite_sets.integer_square_bound` | object constructor | V1 | finite_sets | — | `rx:complete.rx04.cardinality`, `rx:complete.rx04.forgotten_refinement_cardinality` | — |
| `graph.finite_sets` | operation | V1 | finite_sets | — | `finite_sets.limit.pullback.card` | — |

Existing registrations (2): `meth.cardinality` on `obj.finite_sets.fin` (sage); `prop.is_finite` on `obj.finite_sets.fin` (sage).

### `cat.linear_orders` (LinearOrders)

Layer 2; built from —; milestone T202 Orders (M2); 13 computed statements on routes through it (13 V1, 0 V2).

Engine family **Order structures**: primary Sage posets; fallback GAP Digraphs; Macaulay2 `Posets`.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.linear_orders` | category | V1 | linear_orders | — | `rx:complete.rx01.ordinary_relation`, `rx:complete.rx01.reverse_relation` | — |
| `fun.linear_orders.forget` | functor (object and morphism actions) | V1 | linear_orders, sets | — | `C04.1`, `C04.2`, `C05.1`, `C12.1`, `N17.1`, `comprehension.card` and 7 more | — |
| `obj.linear_orders.fin_ordinary` | object constructor | V1 | linear_orders | — | `rx:complete.rx01.ordinary_cardinality`, `rx:complete.rx01.ordinary_relation`, `rx:complete.rx01.reverse_cardinality`, `rx:complete.rx01.reverse_relation` | — |
| `obj.linear_orders.fin_reverse` | object constructor | V1 | linear_orders | — | `rx:complete.rx01.ordinary_cardinality`, `rx:complete.rx01.ordinary_relation`, `rx:complete.rx01.reverse_cardinality`, `rx:complete.rx01.reverse_relation` | — |
| `obj.linear_orders.integers` | object constructor | V1 | linear_orders | — | `C04.1`, `C04.2`, `C05.1`, `comprehension.card`, `comprehension.elements`, `rx:complete.rx04.exact_predicate` | — |
| `obj.linear_orders.naturals` | object constructor | V1 | linear_orders | — | `C12.1` | — |
| `obj.linear_orders.reals` | object constructor | V1 | linear_orders | — | `N17.1`, `factorization.approximation` | — |
| `op.linear_orders.le` | operation | V1 | linear_orders | linear_orders | `C04.1`, `C04.2`, `C12.1`, `comprehension.card`, `comprehension.elements`, `rx:complete.rx01.ordinary_relation` and 2 more | — |
| `op.linear_orders.lt` | operation | V1 | linear_orders | linear_orders | `C05.1`, `C12.1`, `N17.1`, `factorization.approximation` | — |

Existing registrations: none.

### `cat.additive_monoids`

Layer 1; built from —; milestone T203 Rings (M2); 13 computed statements on routes through it (13 V1, 0 V2).

Engine family **Magmas, semigroups, monoids**: primary GAP (with Semigroups) through `libgap`; fallback Sage `sage.monoids`; `libsemigroups_pybind11`.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.additive_monoids.underlying` | functor (object and morphism actions) | V1 | additive_monoids, sets | — | `M12.1`, `M12.2`, `W07.1`, `W07.2`, `W09.2`, `matrices.kernel` and 7 more | — |
| `obj.additive_monoids.vectors` | object constructor | V1 | additive_monoids | additive_monoids | `M12.1`, `M12.2` | — |
| `mor.sets.vectors_zero` | operation | V1 | sets | additive_monoids | `W07.1`, `W07.2`, `W09.2`, `matrices.kernel` | — |
| `op.additive_monoids.add` | operation | V1 | additive_monoids | additive_monoids | `M12.1` | — |

Existing registrations: none.

### `cat.magmas`

Layer 1; built from —; milestone T203 Rings (M2); 305 computed statements on routes through it (275 V1, 30 V2).

Engine family **Magmas, semigroups, monoids**: primary GAP (with Semigroups) through `libgap`; fallback Sage `sage.monoids`; `libsemigroups_pybind11`.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.magmas` | category | V1 | magmas | — | `rx:complete.lift.whole_formed_equation` | — |
| `clf.magmas.associative` | classifier | V1 | magmas | — | `rx:complete.lift.whole_formed_equation`, `rx:complete.rx05.additive_cardinality`, `rx:complete.rx05.additive_map_sample`, `rx:complete.rx05.complete_component`, `rx:complete.rx05.complete_inverse_component`, `rx:complete.rx05.component_left_inverse` and 4 more | — |
| `forget[clf.sets.binary_operation]` | classifier forget (object and morphism actions) | V1 | magmas, sets | — | `C04.1`, `C04.2`, `C05.1`, `C15.1`, `E10.1`, `F08.1` and 269 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `fractions.cancel` and 24 more |

Existing registrations: none.

### `cat.additive_commutative_monoids` (AdditiveCommutativeMonoids)

Layer 2; built from —; milestone T203 Rings (M2); 5 computed statements on routes through it (5 V1, 0 V2).

Engine family **Magmas, semigroups, monoids**: primary GAP (with Semigroups) through `libgap`; fallback Sage `sage.monoids`; `libsemigroups_pybind11`.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.additive_commutative_monoids.additive_monoid` | functor (object and morphism actions) | V1 | additive_commutative_monoids, additive_monoids | — | `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.full_coefficients` | — |

Existing registrations: none.

### `cat.semigroups`

Layer 2; built from —; milestone T203 Rings (M2); 305 computed statements on routes through it (275 V1, 30 V2).

Engine family **Magmas, semigroups, monoids**: primary GAP (with Semigroups) through `libgap`; fallback Sage `sage.monoids`; `libsemigroups_pybind11`.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.semigroups` | category | V1 | semigroups | — | `rx:complete.lift.whole_formed_equation` | — |
| `forget[clf.magmas.associative]` | classifier forget (object and morphism actions) | V1 | magmas, semigroups | — | `C04.1`, `C04.2`, `C05.1`, `C15.1`, `E10.1`, `F08.1` and 269 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `fractions.cancel` and 24 more |

Existing registrations: none.

### `cat.monoids`

Layer 3; built from —; milestone T203 Rings (M2); 305 computed statements on routes through it (275 V1, 30 V2).

Engine family **Magmas, semigroups, monoids**: primary GAP (with Semigroups) through `libgap`; fallback Sage `sage.monoids`; `libsemigroups_pybind11`.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.monoids` | category | V1 | monoids | — | `rx:complete.lift.whole_formed_equation` | — |
| `fun.monoids.semigroup` | functor (object and morphism actions) | V1 | monoids, semigroups | — | `C04.1`, `C04.2`, `C05.1`, `C15.1`, `E10.1`, `F08.1` and 269 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `fractions.cancel` and 24 more |
| `obj.sets.units` | object constructor | V1 | monoids, sets | monoids | `M11.1`, `calculus.integral_square`, `factorization.approximation`, `integration.at_zero`, `integration.derivative`, `integration.differential` and 6 more | `fractions.cancel`, `fractions.halves`, `fractions.lowest_terms`, `inverses.det` |
| `mor.sets.divide` | operation | V1 | sets | monoids | `E10.1`, `I03.1`, `I06.1`, `I09.1`, `I10.1`, `K05.1` and 35 more | `fractions.cancel`, `fractions.halves`, `fractions.lowest_terms`, `inverses.det`, `units.rationals.three_inverse` |
| `mor.sets.monoid_power` | operation | V1 | sets | monoids | `rx:addition.rx03.complete_double_coordinates`, `rx:addition.rx03.complete_triple_coordinates`, `rx:addition.rx03.conjugated_double_action`, `rx:addition.rx03.conjugated_triple_action`, `rx:complete.rx03.conjugation_retains_inverse`, `rx:complete.rx03.fourth_power` and 8 more | — |
| `op.monoids.mul` | operation | V1 | monoids | monoids | `rx:complete.rx03.inverse_product`, `rx:complete.rx03.product_inverse`, `rx:complete.rx05.multiplication`, `rx:complete.rx05.operations_distinct`, `rx:complete.rx07.map_sample_backward`, `rx:complete.rx07.map_sample_square` and 2 more | — |
| `op.monoids.one` | operation | V1 | monoids | monoids | `rx:complete.rx03.fourth_power`, `rx:complete.rx03.inverse_product`, `rx:complete.rx03.product_inverse`, `rx:complete.rx03.second_power_nonidentity` | — |

Existing registrations: none.

### `cat.groups` (Groups)

Layer 4; built from —; milestone T203 Rings (M2); 95 computed statements on routes through it (82 V1, 13 V2).

Engine family **Groups**: primary GAP through Sage; fallback Oscar; SymPy.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.groups` | category | V1 | groups | — | `rx:addition.rx03.actual_inverse_arrow`, `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.arrow_inverse_left`, `rx:addition.rx03.arrow_inverse_right`, `rx:addition.rx03.complete_conjugation` and 20 more | `groups.abelian.cyclic_three`, `groups.abelian.symmetric_three` |
| `cmp.groups.cyclic_quotient_residue` | comparison (presentation or cell) | V1 | groups | — | `rx:addition.rx03.complete_conjugation`, `rx:addition.rx03.complete_double_coordinates`, `rx:addition.rx03.complete_inverse_conjugation`, `rx:addition.rx03.complete_triple_coordinates`, `rx:addition.rx03.conjugated_double_action`, `rx:addition.rx03.conjugated_triple_action` and 6 more | — |
| `con.automorphisms` | construction | V1 | groups | — | `rx:addition.rx03.complete_conjugation`, `rx:addition.rx03.complete_inverse_conjugation`, `rx:addition.rx03.conjugated_double_action`, `rx:addition.rx03.conjugated_triple_action`, `rx:complete.rx03.aut_map_left_inverse`, `rx:complete.rx03.aut_map_right_inverse` and 7 more | — |
| `fun.groups.monoid` | functor (object and morphism actions) | V1 | groups, monoids | — | `W04.1`, `W09.2`, `W09.3`, `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left` and 76 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `groups.abelian.cyclic_three` and 7 more |
| `fun.monoids.units` | functor (object and morphism actions) | V2 | groups, monoids | — | — | `units.rationals.three_inverse` |
| `obj.groups.cyclic` | object constructor | V1 | groups | — | `rx:addition.rx03.complete_conjugation`, `rx:addition.rx03.complete_double_coordinates`, `rx:addition.rx03.complete_inverse_conjugation`, `rx:addition.rx03.complete_triple_coordinates`, `rx:addition.rx03.conjugated_double_action`, `rx:addition.rx03.conjugated_triple_action` and 2 more | `groups.abelian.cyclic_three`, `groups.kernel.sign_card`, `groups.kernel.trivial_card` |
| `obj.groups.cyclic_quotient` | object constructor | V1 | groups | — | `rx:addition.rx03.actual_inverse_arrow`, `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.arrow_inverse_left`, `rx:addition.rx03.arrow_inverse_right`, `rx:addition.rx03.complete_conjugation` and 18 more | — |
| `obj.groups.symmetric` | object constructor | V2 | groups | — | — | `groups.abelian.symmetric_three`, `groups.kernel.identity_card`, `groups.kernel.sign_card`, `groups.kernel.trivial_card` |
| `obj.groups.units` | object constructor | V1 | groups, monoids | monoids | `rx:addition.rx03.actual_inverse_arrow`, `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.arrow_inverse_left`, `rx:addition.rx03.arrow_inverse_right`, `rx:addition.rx03.complete_conjugation` and 15 more | — |
| `meth.units` | operation | V2 | groups, monoids | — | — | `units.rationals.three_inverse` |
| `mor.groups.automorphism_backward` | operation | V1 | groups | groups | `rx:addition.rx03.actual_inverse_arrow`, `rx:addition.rx03.arrow_inverse_left`, `rx:addition.rx03.arrow_inverse_right`, `rx:addition.rx03.complete_inverse_conjugation`, `rx:addition.rx03.triple_class_two` | — |
| `mor.groups.automorphism_forward` | operation | V1 | groups | groups | `rx:addition.rx03.actual_inverse_arrow`, `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.arrow_inverse_left`, `rx:addition.rx03.arrow_inverse_right`, `rx:addition.rx03.complete_conjugation` and 6 more | — |
| `mor.groups.cyclic_quotient_aut_by_unit` | operation | V1 | groups | — | `rx:addition.rx03.actual_inverse_arrow`, `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.arrow_inverse_left`, `rx:addition.rx03.arrow_inverse_right`, `rx:addition.rx03.complete_conjugation` and 15 more | — |
| `mor.groups.identity` | operation | V2 | groups | groups | — | `groups.kernel.identity_card` |
| `mor.groups.sign` | operation | V2 | groups | — | — | `groups.kernel.sign_card` |
| `mor.groups.trivial` | operation | V2 | groups | groups | — | `groups.kernel.trivial_card` |
| `op.groups.inverse` | operation | V2 | groups | groups | — | `units.rationals.three_inverse` |
| `prop.is_abelian` | property | V2 | groups, magmas | — | — | `groups.abelian.cyclic_three`, `groups.abelian.symmetric_three` |

Existing registrations (12): `meth.cardinality` on `obj.groups.cyclic` (gap-groups); `meth.cardinality` on `obj.groups.symmetric` (gap-groups); `meth.cardinality` on `obj.groups.units` (gap-groups); `prop.is_abelian` on `obj.groups.cyclic` (gap-groups); `prop.is_abelian` on `obj.groups.symmetric` (gap-groups); `prop.is_abelian` on `obj.groups.units` (gap-groups); `prop.is_commutative` on `obj.groups.cyclic` (gap-groups); `prop.is_commutative` on `obj.groups.symmetric` (gap-groups); `prop.is_commutative` on `obj.groups.units` (gap-groups); `prop.is_finite` on `obj.groups.cyclic` (gap-groups); `prop.is_finite` on `obj.groups.symmetric` (gap-groups); `prop.is_finite` on `obj.groups.units` (gap-groups).

### `cat.semirings` (Semirings)

Layer 4; built from —; milestone T203 Rings (M2); 41 computed statements on routes through it (39 V1, 2 V2).

Engine family **Semirings**: primary Sage; fallback GAP Semigroups.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.semirings.forget` | functor (object and morphism actions) | V1 | semirings, sets | — | `C12.1`, `C13.1`, `C14.1`, `E10.1`, `F15.1`, `H06.1` and 33 more | `several_variables.plane`, `several_variables.total_degree` |
| `fun.semirings.monoid` | functor (object and morphism actions) | V1 | monoids, semirings | — | `E10.1`, `N25.1`, `N25.2`, `W07.1`, `differentials.degree`, `matrices.rank` and 10 more | `several_variables.plane`, `several_variables.total_degree` |
| `obj.semirings.naturals` | object constructor | V1 | semirings | — | `C12.1`, `C13.1`, `C14.1`, `E10.1`, `F15.1`, `H06.1` and 33 more | `several_variables.plane`, `several_variables.total_degree` |
| `num.semirings` | operation | V1 | semirings | semirings | `C12.1`, `C13.1`, `C14.1`, `E10.1`, `F15.1`, `H06.1` and 32 more | `several_variables.plane`, `several_variables.total_degree` |
| `op.semirings.add` | operation | V1 | semirings | semirings | `E10.1`, `ellipses.evens`, `ellipses.multiples`, `ellipses.naturals`, `ellipses.squares_even`, `rx:complete.rx09.full_coefficients` and 1 more | — |
| `op.semirings.mul` | operation | V1 | semirings | semirings | `C12.1`, `C14.1`, `E10.1`, `H06.1`, `comprehension.even_card`, `comprehension.even_member` and 10 more | — |
| `op.semirings.pow` | operation | V1 | semirings | semirings | `E10.1`, `ellipses.even_square`, `ellipses.odd_square`, `ellipses.squares_even`, `rx:complete.rx09.full_family`, `series.coefficient_four` and 3 more | — |

Existing registrations: none.

### `cat.additive_groups`

Layer 5; built from —; milestone T203 Rings (M2); 64 computed statements on routes through it (58 V1, 6 V2).

Engine family **Groups**: primary GAP through Sage; fallback Oscar; SymPy.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.additive_groups.additive_monoid` | functor (object and morphism actions) | V1 | additive_groups, additive_monoids | — | `W09.2`, `rx:complete.lift.formed_arrow_action`, `rx:complete.lift.whole_formed_equation` | — |
| `fun.additive_groups.to_groups` | functor (object and morphism actions) | V1 | additive_groups, groups | — | `W04.1`, `W09.2`, `W09.3`, `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left` and 50 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `lattices.rank.e8` |

Existing registrations: none.

### `cat.rings` (Rings)

Layer 6; built from —; milestone T203 Rings (M2); 304 computed statements on routes through it (275 V1, 29 V2).

Engine family **Rings, commutative rings**: primary Sage; fallback Oscar; Macaulay2.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.rings` | category | V1 | rings | — | `rx:addition.rx03.actual_inverse_arrow`, `rx:addition.rx03.all_integer_classes_double`, `rx:addition.rx03.all_integer_classes_triple`, `rx:addition.rx03.arrow_inverse_left`, `rx:addition.rx03.arrow_inverse_right`, `rx:addition.rx03.complete_conjugation` and 18 more | — |
| `cmp.rings.carrier` | comparison (presentation or cell) | V1 | rings, sets | — | `rx:complete.rx05.complete_component`, `rx:complete.rx05.complete_inverse_component`, `rx:complete.rx05.component_left_inverse`, `rx:complete.rx05.component_right_inverse`, `rx:complete.rx05.whole_map_naturality` | — |
| `fun.rings.additive_commutative_monoid` | functor (object and morphism actions) | V1 | additive_commutative_monoids, rings | — | `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.full_coefficients` | — |
| `fun.rings.additive_group` | functor (object and morphism actions) | V1 | additive_groups, rings | — | `W04.1`, `W09.2`, `W09.3`, `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left` and 52 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `lattices.rank.e8` |
| `fun.rings.multiplicative_monoid` | functor (object and morphism actions) | V1 | monoids, rings | — | `C04.1`, `C04.2`, `C05.1`, `C15.1`, `E10.1`, `F08.1` and 264 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `fractions.cancel` and 18 more |
| `fun.rings.semiring` | functor (object and morphism actions) | V1 | rings, semirings | — | `E10.1`, `N25.1`, `N25.2`, `W07.1`, `differentials.degree`, `matrices.rank` and 10 more | `several_variables.plane`, `several_variables.total_degree` |
| `obj.rings.complexes` | object constructor | V1 | rings | — | `K03.1`, `K04.1`, `K05.1`, `N18.3`, `N20.2`, `N21.1` and 20 more | — |
| `obj.rings.integers` | object constructor | V1 | rings | — | `C04.1`, `C04.2`, `C05.1`, `E10.1`, `F08.1`, `F13.1` and 57 more | `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic` |
| `obj.rings.integers_mod` | object constructor | V1 | rings | — | `F08.2`, `H07.1`, `H07.2`, `M13.1`, `N26.1`, `R01.1` and 24 more | `numbers.zmod5.difference`, `numbers.zmod5.negation`, `numbers.zmod5.product`, `numbers.zmod7.distributive`, `numbers.zmod7.value`, `refinement.finite_product_card` |
| `obj.rings.rationals` | object constructor | V1 | rings | — | `C15.1`, `I01.1`, `I03.1`, `I04.1`, `I06.1`, `I09.1` and 69 more | `fractions.cancel`, `fractions.halves`, `fractions.lowest_terms`, `inverses.det`, `numbers.rationals.sum`, `units.rationals.three_inverse` |
| `obj.rings.reals` | object constructor | V1 | rings | — | `H05.1`, `L07.1`, `L07.2`, `L09.1`, `L09.2`, `N17.1` and 25 more | — |
| `num.rings` | operation | V1 | rings | rings | `C04.1`, `C04.2`, `C05.1`, `C15.1`, `E10.1`, `F08.1` and 239 more | `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `fractions.cancel`, `fractions.halves`, `fractions.lowest_terms` and 8 more |
| `op.rings.add` | operation | V1 | rings | rings | `C05.1`, `C15.1`, `E10.1`, `H07.1`, `H07.2`, `I03.1` and 92 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `fractions.halves`, `numbers.rationals.sum` and 6 more |
| `op.rings.mul` | operation | V1 | rings | rings | `C15.1`, `E10.1`, `I03.1`, `I04.1`, `I06.1`, `I09.1` and 92 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `fractions.cancel`, `numbers.zmod5.product` and 3 more |
| `op.rings.neg` | operation | V1 | rings | rings | `C05.1`, `C15.1`, `K03.1`, `K04.1`, `K05.1`, `L09.1` and 85 more | `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `inverses.det`, `numbers.zmod5.difference`, `numbers.zmod5.negation`, `presentations.f9.inverse_generator` |
| `op.rings.pow` | operation | V1 | rings | rings | `C04.1`, `C04.2`, `C15.1`, `E10.1`, `F16.3`, `H05.1` and 69 more | `several_variables.total_degree` |

Existing registrations (2): `meth.cardinality` on `obj.rings.integers_mod` (gap); `prop.is_finite` on `obj.rings.integers_mod` (gap).

### `cat.core_groups`

Layer (6); built from `cat.groups`; milestone T204 Group automorphisms (M2); 13 computed statements on routes through it (13 V1, 0 V2).

Engine family **Groups**: primary GAP through Sage; fallback Oscar; SymPy.

No row has its home here: the category is on the routes through the rows of other categories.

Existing registrations: none.

### `cat.commutative_rings` (CommutativeRings)

Layer 7; built from —; milestone T205 Commutative rings (M2); 198 computed statements on routes through it (180 V1, 18 V2).

Engine family **Rings, commutative rings**: primary Sage; fallback Oscar; Macaulay2.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.commutative_rings` | category | V1 | commutative_rings | — | `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.separate_second_defining_equation`, `rx:addition.lift.unique_second_factor`, `rx:complete.lift.actual_second_inclusion` and 64 more | — |
| `clf.commutative_rings.field` | classifier | V1 | commutative_rings | — | `rx:complete.lift.formed_arrow_action`, `rx:complete.lift.whole_formed_equation`, `rx:complete.rx05.additive_cardinality`, `rx:complete.rx05.additive_map_sample`, `rx:complete.rx05.complete_component`, `rx:complete.rx05.complete_inverse_component` and 5 more | — |
| `cmp.f9.translation` | comparison (presentation or cell) | V1 | commutative_rings | — | `rx:complete.rx07.coefficients_backward`, `rx:complete.rx07.coefficients_forward`, `rx:complete.rx07.full_backward_map`, `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_map_inverse`, `rx:complete.rx07.full_square_map` and 11 more | `presentations.f9.forward_constant`, `presentations.f9.forward_generator`, `presentations.f9.inverse_constant`, `presentations.f9.inverse_generator` |
| `fun.commutative_rings.ring` | functor (object and morphism actions) | V1 | commutative_rings, rings | — | `C15.1`, `E10.1`, `I01.1`, `I03.1`, `I04.1`, `I06.1` and 172 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `inverses.det` and 12 more |
| `obj.commutative_rings.f9_x` | object constructor | V1 | commutative_rings | — | `rx:complete.rx07.full_backward_map`, `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_map_inverse`, `rx:complete.rx07.full_square_map`, `rx:complete.rx07.generator_backward`, `rx:complete.rx07.generator_forward` and 8 more | `presentations.f9.forward_constant`, `presentations.f9.forward_generator`, `presentations.f9.inverse_constant`, `presentations.f9.inverse_generator` |
| `obj.commutative_rings.f9_y` | object constructor | V1 | commutative_rings | — | `rx:complete.rx07.full_forward_map`, `rx:complete.rx07.full_square_map`, `rx:complete.rx07.generator_backward`, `rx:complete.rx07.generator_forward`, `rx:complete.rx07.generator_nonidentity`, `rx:complete.rx07.map_sample_forward` and 5 more | `presentations.f9.forward_constant`, `presentations.f9.forward_generator`, `presentations.f9.inverse_constant`, `presentations.f9.inverse_generator` |
| `obj.commutative_rings.integers` | object constructor | V1 | commutative_rings | — | `rx:complete.rx05.additive_map_sample`, `rx:complete.rx05.multiplicative_map_sample`, `rx:complete.rx05.whole_map_naturality`, `rx:complete.rx06.action_five_one`, `rx:complete.rx06.action_negative_one_two`, `rx:complete.rx06.action_two_three` and 13 more | — |
| `obj.commutative_rings.integers_mod` | object constructor | V1 | commutative_rings | — | `rx:complete.rx06.action_five_one`, `rx:complete.rx06.action_negative_one_two`, `rx:complete.rx06.action_two_three`, `rx:complete.rx06.cartesian_whole_carrier`, `rx:complete.rx06.named_restricted_cardinality`, `rx:complete.rx06.original_dimension` and 5 more | — |
| `obj.commutative_rings.rationals` | object constructor | V1 | commutative_rings | — | `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.separate_second_defining_equation`, `rx:addition.lift.unique_second_factor`, `rx:complete.lift.actual_second_inclusion` and 32 more | — |
| `obj.rings.matrices` | object constructor | V1 | rings | commutative_rings | `M11.1`, `M13.1`, `composed.det`, `composed.trace` | — |
| `obj.rings.mv_polynomials` | object constructor | V2 | rings | commutative_rings | — | `several_variables.total_degree` |
| `obj.rings.polynomials` | object constructor | V1 | rings | commutative_rings | `C15.1`, `I01.1`, `I03.1`, `I04.1`, `I06.1`, `I09.1` and 46 more | — |
| `obj.rings.power_series` | object constructor | V1 | rings | commutative_rings | `E10.1`, `L07.1`, `L07.2`, `L09.1`, `L09.2`, `Q02.1` and 1 more | — |
| `obj.sets.kaehler_polynomials` | object constructor | V1 | sets | commutative_rings | `I03.1`, `I04.1`, `I06.1`, `I09.1`, `I10.1`, `differentials.differential` and 4 more | — |
| `obj.sets.matrices` | object constructor | V1 | sets | commutative_rings | `M11.1`, `M13.1`, `N26.1`, `composed.charpoly`, `composed.det`, `composed.trace` and 7 more | `inverses.det` |
| `obj.sets.monics` | object constructor | V1 | sets | commutative_rings | `composed.charpoly`, `composed.det`, `composed.trace` | — |
| `obj.sets.mv_polynomials` | object constructor | V1 | sets | commutative_rings | `several_variables.dimension` | `several_variables.plane`, `several_variables.total_degree` |
| `obj.sets.nonzero_polynomials` | object constructor | V1 | sets | commutative_rings | `P10.1`, `P12.1`, `P12.2`, `P13.1`, `P14.1`, `P14.2` and 9 more | — |
| `obj.sets.polynomial_factorization_data` | object constructor | V1 | sets | commutative_rings | `P17.1` | — |
| `obj.sets.polynomials` | object constructor | V1 | sets | commutative_rings | `C15.1`, `I01.1`, `I03.1`, `I04.1`, `I06.1`, `I09.1` and 46 more | — |
| `obj.sets.power_series` | object constructor | V1 | sets | commutative_rings | `E10.1`, `L07.1`, `L07.2`, `L09.1`, `L09.2`, `Q02.1` and 10 more | — |
| `obj.sets.rectangular_matrices` | object constructor | V1 | sets | commutative_rings | `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.separate_second_defining_equation`, `rx:addition.lift.unique_second_factor`, `rx:complete.lift.final_factor_comparison` and 14 more | — |
| `mor.commutative_rings.integer_coefficients` | operation | V1 | commutative_rings | commutative_rings | `rx:complete.rx05.additive_map_sample`, `rx:complete.rx05.multiplicative_map_sample`, `rx:complete.rx05.whole_map_naturality`, `rx:complete.rx06.action_five_one`, `rx:complete.rx06.action_negative_one_two`, `rx:complete.rx06.action_two_three` and 7 more | — |
| `mor.sets.companion_matrix` | operation | V1 | sets | commutative_rings | `composed.charpoly`, `composed.det`, `composed.trace` | — |
| `mor.sets.kaehler_primitives` | operation | V1 | sets | commutative_rings | `I03.1`, `I04.1`, `I06.1`, `I09.1`, `I10.1`, `integration.normalized` and 2 more | — |
| `mor.sets.kaehler_scale` | operation | V1 | sets | commutative_rings | `I03.1`, `I04.1`, `I06.1`, `I09.1`, `I10.1`, `differentials.differential` and 4 more | — |
| `mor.sets.krull_dimension` | operation | V1 | sets | commutative_rings | `several_variables.dimension` | `several_variables.plane` |
| `mor.sets.matrix_charpoly` | operation | V1 | sets | commutative_rings | `composed.charpoly`, `matrices.charpoly` | — |
| `mor.sets.matrix_det` | operation | V1 | sets | commutative_rings | `composed.det`, `matrices.det` | `inverses.det` |
| `mor.sets.matrix_ker` | operation | V1 | sets | commutative_rings | `matrices.kernel`, `subspaces.kernel` | — |
| `mor.sets.matrix_rank` | operation | V1 | sets | commutative_rings | `matrices.rank` | — |
| `mor.sets.matrix_rows` | operation | V1 | sets | commutative_rings | `inverses.value`, `matrices.application`, `matrices.charpoly`, `matrices.det`, `matrices.juxtaposition`, `matrices.kernel` and 4 more | — |
| `mor.sets.matrix_trace` | operation | V1 | sets | commutative_rings | `M13.1`, `composed.trace`, `matrices.trace` | — |
| `mor.sets.mv_total_degree` | operation | V2 | sets | commutative_rings | — | `several_variables.total_degree` |
| `mor.sets.polynomial_degree` | operation | V1 | sets | commutative_rings | `differentials.degree`, `polynomials.degree`, `polynomials.degree_over_rationals` | — |
| `mor.sets.polynomial_derivative` | operation | V1 | sets | commutative_rings | `I01.1`, `differentials.derivative`, `integration.derivative` | — |
| `mor.sets.polynomial_differential` | operation | V1 | sets | commutative_rings | `I03.1`, `I04.1`, `I06.1`, `I09.1`, `I10.1`, `differentials.differential` and 4 more | — |
| `mor.sets.polynomial_factorization` | operation | V1 | sets | commutative_rings | `P17.1` | — |
| `mor.sets.polynomial_factorization_unit` | operation | V1 | sets | commutative_rings | `P17.1` | — |
| `mor.sets.polynomial_factors` | operation | V1 | sets | commutative_rings | `P10.1`, `P15.1`, `factorization.over_complexes`, `polynomials.factors` | — |
| `mor.sets.polynomial_map` | operation | V1 | sets | commutative_rings | `P10.1`, `P14.1`, `P15.3`, `P16.1`, `composed.root_product`, `composed.root_sum` and 3 more | — |
| `mor.sets.polynomial_own_evaluation` | operation | V1 | sets | commutative_rings | `C15.1`, `K03.1`, `K04.1`, `K05.1`, `P15.2` | — |
| `mor.sets.polynomial_roots` | operation | V1 | sets | commutative_rings | `P12.1`, `P12.2`, `P13.1`, `P14.1`, `P14.2`, `P15.3` and 4 more | — |
| `mor.sets.power_series_coefficient` | operation | V1 | sets | commutative_rings | `L07.1`, `L09.1`, `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero` and 5 more | — |
| `mor.sets.power_series_of_coefficients` | operation | V1 | sets | commutative_rings | `E10.1`, `series.coefficient_four`, `series.coefficient_three`, `series.coefficient_two`, `series.coefficient_zero` | — |
| `mor.sets.successor_power_series_terms` | operation | V1 | sets | commutative_rings | `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.full_coefficients`, `rx:complete.rx09.full_family` | — |

Existing registrations (14): `cmp.f9.translation` on `obj.commutative_rings.f9_x` (sage-presentations); `cmp.f9.translation` on `obj.commutative_rings.f9_y` (sage-presentations); `meth.cardinality` on `obj.commutative_rings.f9_x` (sage-presentations); `meth.cardinality` on `obj.commutative_rings.f9_y` (sage-presentations); `mor.sets.companion_matrix` on `obj.sets.monics` (sage-symbolic); `mor.sets.mv_total_degree` on `obj.sets.mv_polynomials` (sage-symbolic); `mor.sets.polynomial_degree` on `obj.sets.polynomials` (sage-symbolic); `mor.sets.polynomial_derivative` on `obj.sets.polynomials` (sage-symbolic); `mor.sets.polynomial_differential` on `obj.sets.polynomials` (sage-symbolic); `mor.sets.polynomial_factors` on `obj.sets.nonzero_polynomials` (sage-symbolic); `mor.sets.polynomial_map` on `obj.sets.polynomials` (sage-symbolic); `mor.sets.polynomial_roots` on `obj.sets.nonzero_polynomials` (sage-symbolic); `prop.is_finite` on `obj.commutative_rings.f9_x` (sage-presentations); `prop.is_finite` on `obj.commutative_rings.f9_y` (sage-presentations).

### `cat.hausdorff_topological_commutative_monoids` (HausdorffTopologicalMonoids)

Layer 3; built from —; milestone T206 Topological monoids (M2); 5 computed statements on routes through it (5 V1, 0 V2).

Engine family **Polynomial rings**: primary Sage; fallback python-flint; Oscar or Singular.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.hausdorff_topological_commutative_monoids` | category | V1 | hausdorff_topological_commutative_monoids | — | `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.full_coefficients` | — |
| `fun.hausdorff_topological_commutative_monoids.additive_commutative_monoid` | functor (object and morphism actions) | V1 | additive_commutative_monoids, hausdorff_topological_commutative_monoids | — | `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.full_coefficients` | — |
| `obj.hausdorff_topological_monoids.power_series` | object constructor | V1 | hausdorff_topological_commutative_monoids | commutative_rings | `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.full_coefficients` | — |
| `obj.sets.summable_families` | object constructor | V1 | sets | hausdorff_topological_commutative_monoids | `rx:complete.rx09.degree_five`, `rx:complete.rx09.degree_one`, `rx:complete.rx09.degree_three`, `rx:complete.rx09.degree_zero`, `rx:complete.rx09.full_coefficients` | — |

Existing registrations: none.

### `cat.modules_total`

Layer 6; built from —; milestone T207 Modules (M2); 64 computed statements on routes through it (56 V1, 8 V2).

Engine family **Modules**: primary Sage; fallback Oscar or Macaulay2 for modules over polynomial rings; CAP.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fib.modules` | fibration | V1 | modules_total, rings | — | `rx:complete.rx06.cartesian_whole_carrier` | — |
| `fun.modules.additive_group` | functor (object and morphism actions) | V1 | additive_groups, modules_total | — | `W04.1`, `W09.2`, `W09.3`, `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left` and 46 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `lattices.rank.e8` |
| `fun.modules.underlying` | functor (object and morphism actions) | V1 | modules_total, sets | — | `lattices.discriminant.a1`, `lattices.discriminant.a2`, `lattices.discriminant.a3`, `rx:complete.rx06.cartesian_whole_carrier`, `rx:complete.rx06.whole_scalar_action` | `lattices.card.a0`, `lattices.card.a2` |

Existing registrations: none.

### `cat.modules_r` (Modules)

Layer 7; built from `cat.rings`; milestone T207 Modules (M2); 73 computed statements on routes through it (62 V1, 11 V2).

Engine family **Modules**: primary Sage; fallback Oscar or Macaulay2 for modules over polynomial rings; CAP.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.modules_r` | category | V1 | modules_r | — | `R01.1`, `R02.1`, `R03.1` | — |
| `fun.modules.fibre_inclusion` | functor (object and morphism actions) | V1 | modules_r, modules_total | — | `W04.1`, `W09.2`, `W09.3`, `lattices.discriminant.a1`, `lattices.discriminant.a2`, `lattices.discriminant.a3` and 50 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `lattices.card.a0` and 2 more |
| `fun.modules.reindex` | functor (object and morphism actions) | V1 | modules_r | — | `rx:complete.rx06.action_five_one`, `rx:complete.rx06.action_negative_one_two`, `rx:complete.rx06.action_two_three`, `rx:complete.rx06.cartesian_whole_carrier`, `rx:complete.rx06.reindexed_map_sample`, `rx:complete.rx06.restricted_cardinality` and 3 more | — |
| `obj.modules.regular` | object constructor | V1 | modules_r | rings | `W04.1`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.separate_second_defining_equation`, `rx:addition.lift.unique_second_factor` and 43 more | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic` |
| `obj.modules.vectors` | object constructor | V1 | modules_r | rings | `W04.1`, `W09.2`, `W09.3`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison` and 17 more | — |
| `obj.modules_r.restricted_regular` | object constructor | V1 | modules_r | rings | `rx:complete.rx06.named_restricted_cardinality` | — |
| `obj.sets.bilinear_maps` | object constructor | V2 | sets | commutative_rings, modules_r | — | `formed.card.hyperbolic_fixed`, `formed.card.hyperbolic_variable`, `formed.card.zero_rank_zero`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic` |
| `mor.modules.row_linear_map` | operation | V1 | modules_r | commutative_rings | `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.separate_second_defining_equation`, `rx:addition.lift.unique_second_factor`, `rx:complete.lift.final_factor_comparison` and 14 more | — |
| `op.modules.scalar_action` | operation | V1 | modules_r | modules_r, rings | `rx:complete.rx06.action_five_one`, `rx:complete.rx06.action_negative_one_two`, `rx:complete.rx06.action_two_three`, `rx:complete.rx06.reindexed_map_sample`, `rx:complete.rx06.whole_reindexed_map`, `rx:complete.rx06.whole_scalar_action` and 1 more | — |

Existing registrations (2): `meth.cardinality` on `obj.modules.regular` (sage-modules); `meth.cardinality` on `obj.modules.vectors` (sage-modules).

### `cat.bil_wform` (BilWForm)

Layer 8; built from `cat.commutative_rings`; milestone T208 Bilinear forms (M2); 11 computed statements on routes through it (3 V1, 8 V2).

Engine family **Bilinear and quadratic modules**: primary Sage; fallback Hecke through Oscar.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.bil_wform.carrier` | functor (object and morphism actions) | V1 | bil_wform, modules_r | — | `lattices.discriminant.a1`, `lattices.discriminant.a2`, `lattices.discriminant.a3` | `formed.card.hyperbolic_variable`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic`, `lattices.card.a0`, `lattices.card.a2`, `lattices.rank.a1` and 2 more |
| `obj.bil_wform.formed` | object constructor | V2 | bil_wform | commutative_rings, modules_r | — | `formed.card.hyperbolic_variable`, `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic` |
| `obj.bil_wform.root_lattice_a` | object constructor | V2 | bil_wform | — | — | `lattices.card.a0`, `lattices.card.a2`, `lattices.rank.a1`, `lattices.rank.a2`, `lattices.rank.a3` |
| `colim.bil_w_form.cokernel` | operation | V1 | bil_wform | bil_wform, commutative_rings | `lattices.discriminant.a1`, `lattices.discriminant.a2`, `lattices.discriminant.a3` | — |
| `mor.bil_wform.root_lattice_a_to_dual` | operation | V1 | bil_wform | — | `lattices.discriminant.a1`, `lattices.discriminant.a2`, `lattices.discriminant.a3` | — |
| `mor.sets.formed_pairing` | operation | V2 | sets | bil_wform, commutative_rings | — | `formed.pairing.hyperbolic`, `formed.pairing.scaled_hyperbolic` |

Existing registrations (10): `colim.bil_w_form.cokernel` on `cat.bil_wform` (sage-discriminant); `meth.cardinality` on `obj.bil_wform.root_lattice_a` (sage-modules); `meth.cardinality` on `obj.bil_wform.root_lattice_a_discriminant` (sage-discriminant); `meth.cardinality` on `obj.bil_wform.root_lattice_a_dual` (sage-modules); `prop.is_abelian` on `obj.bil_wform.root_lattice_a` (gap-groups); `prop.is_abelian` on `obj.bil_wform.root_lattice_a_discriminant` (gap-groups); `prop.is_abelian` on `obj.bil_wform.root_lattice_a_dual` (gap-groups); `prop.is_commutative` on `obj.bil_wform.root_lattice_a` (gap-groups); `prop.is_commutative` on `obj.bil_wform.root_lattice_a_discriminant` (gap-groups); `prop.is_commutative` on `obj.bil_wform.root_lattice_a_dual` (gap-groups).

### `cat.fields` (Fields)

Layer 8; built from —; milestone T209 Fields (M2); 27 computed statements on routes through it (27 V1, 0 V2).

Engine family **Fields**: primary Sage; fallback Oscar (Nemo, Hecke); python-flint.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `forget[clf.commutative_rings.field]` | classifier forget (object and morphism actions) | V1 | commutative_rings, fields | — | `W04.1`, `W05.1`, `W05.2`, `W06.1`, `W06.2`, `W07.1` and 21 more | — |
| `obj.fields.prime_residues` | object constructor | V1 | fields | — | `rx:complete.rx05.addition`, `rx:complete.rx05.additive_cardinality`, `rx:complete.rx05.additive_map_sample`, `rx:complete.rx05.complete_component`, `rx:complete.rx05.complete_inverse_component`, `rx:complete.rx05.component_left_inverse` and 7 more | — |
| `obj.fields.rationals` | object constructor | V1 | fields | — | `rx:complete.lift.formed_arrow_action`, `rx:complete.lift.whole_formed_equation` | — |
| `mor.sets.span` | operation | V1 | sets | fields | `W04.1`, `W05.1`, `W05.2`, `W06.1`, `W06.2`, `W07.1` and 6 more | — |
| `mor.sets.span_dim` | operation | V1 | sets | fields | `W07.1`, `subspaces.dim` | — |

Existing registrations (1): `mor.sets.span` on `obj.sets.power_set` (sage-symbolic).

### `cat.core_modules_r`

Layer (9); built from `cat.modules_r`; milestone T210 Module rank (M2); 6 computed statements on routes through it (2 V1, 4 V2).

Engine family **Modules**: primary Sage; fallback Oscar or Macaulay2 for modules over polynomial rings; CAP.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.modules.rank` | functor (object and morphism actions) | V2 | cardinals, core_modules_r | — | — | `lattices.rank.a1`, `lattices.rank.a2`, `lattices.rank.a3` |
| `meth.dim` | operation | V1 | cardinals, core_modules_r, modules_r | — | `rx:complete.rx06.original_dimension` | — |
| `meth.rank` | operation | V2 | cardinals, core_modules_r, modules_r | — | — | `lattices.rank.e8` |

Existing registrations (5): `meth.rank` on `obj.bil_wform.root_lattice_a` (sage-modules); `meth.rank` on `obj.bil_wform.root_lattice_a_discriminant` (sage-modules); `meth.rank` on `obj.bil_wform.root_lattice_a_dual` (sage-modules); `meth.rank` on `obj.modules.regular` (sage-modules); `meth.rank` on `obj.modules.vectors` (sage-modules).

### `cat.subobjects_sets`

Layer 1; built from `cat.sets`; milestone T211 Module kernels (M2); 1 computed statements on routes through it (1 V1, 0 V2).

Engine family **Sets**: primary Sage; fallback SymPy sets; Catlab or CAP for general limits and colimits.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.subobjects_sets.domain` | functor (object and morphism actions) | V1 | sets, subobjects_sets | — | `R03.1` | — |

Existing registrations: none.

### `cat.subobjects_modules_r`

Layer 2; built from `cat.modules_r`; milestone T211 Module kernels (M2); 6 computed statements on routes through it (6 V1, 0 V2).

Engine family **Modules**: primary Sage; fallback Oscar or Macaulay2 for modules over polynomial rings; CAP.

No row has its home here: the category is on the routes through the rows of other categories.

Existing registrations: none.

### `cat.arrows_modules_r`

Layer (9); built from `cat.modules_r`; milestone T211 Module kernels (M2); 6 computed statements on routes through it (6 V1, 0 V2).

Engine family **Modules**: primary Sage; fallback Oscar or Macaulay2 for modules over polynomial rings; CAP.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `meth.arrow_im` | operation | V1 | arrows_modules_r, subobjects_modules_r | — | `W09.3` | — |
| `meth.arrow_ker` | operation | V1 | arrows_modules_r, subobjects_modules_r | — | `W04.1`, `W09.2`, `rx:complete.rx08.kernel_dimension`, `rx:complete.rx08.kernel_zero_composite` | — |
| `meth.kernel` | operation | V1 | arrows_modules_r, subobjects_modules_r | — | `I01.1` | — |

Existing registrations: none.

### `cat.core_subobjects_modules_r`

Layer (9); built from `cat.subobjects_modules_r`; milestone T211 Module kernels (M2); 1 computed statements on routes through it (1 V1, 0 V2).

Engine family **Modules**: primary Sage; fallback Oscar or Macaulay2 for modules over polynomial rings; CAP.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `meth.subobject_dim` | operation | V1 | cardinals, core_subobjects_modules_r, subobjects_modules_r | — | `rx:complete.rx08.kernel_dimension` | — |

Existing registrations: none.

### `cat.bilin_module` (Bil)

Layer 9; built from `cat.commutative_rings`, `cat.modules_r`; milestone T212 Formed modules (M2); 42 computed statements on routes through it (39 V1, 3 V2).

Engine family **Bilinear and quadratic modules**: primary Sage; fallback Hecke through Oscar.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `cat.bilin_module` | category | V1 | bilin_module | — | `rx:complete.lift.whole_formed_equation` | — |
| `fun.bilin_module.change_value` | functor (object and morphism actions) | V1 | bilin_module | — | `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison`, `rx:complete.lift.final_backward_action` and 6 more | — |
| `fun.bilin_module.forget` | functor (object and morphism actions) | V1 | bilin_module, modules_r | — | `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.cone_comparison_inverse_right`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison` and 33 more | `formed.card.hyperbolic_fixed`, `formed.card.zero_rank_zero`, `lattices.rank.e8` |
| `obj.bilin_module.bilinear_form` | object constructor | V2 | bilin_module | commutative_rings, modules_r | — | `formed.card.hyperbolic_fixed`, `formed.card.zero_rank_zero` |
| `obj.bilin_module.degenerate_plane` | object constructor | V1 | bilin_module | — | `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.cone_comparison_inverse_right`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison` and 28 more | — |
| `obj.bilin_module.degenerate_plane_target` | object constructor | V1 | bilin_module | — | `rx:complete.lift.formed_arrow_action`, `rx:complete.lift.whole_formed_equation` | — |
| `obj.bilin_module.degenerate_plane_with_dot` | object constructor | V1 | bilin_module | — | `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.cone_comparison_inverse_right`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison` and 16 more | — |
| `obj.bilin_module.ordinary_kernel_restriction` | object constructor | V1 | bilin_module | bilin_module, commutative_rings, modules_r | `rx:complete.rx08.full_coordinate_inclusion`, `rx:complete.rx08.full_restricted_pairing`, `rx:complete.rx08.restricted_pairing_one`, `rx:complete.rx08.restriction_zero_composite` | — |
| `obj.bilin_module.rational_diagonal_2_3` | object constructor | V1 | bilin_module | — | `rx:complete.rx08.full_coordinate_inclusion`, `rx:complete.rx08.full_projection`, `rx:complete.rx08.full_restricted_pairing`, `rx:complete.rx08.restricted_pairing_one`, `rx:complete.rx08.restriction_zero_composite` | — |
| `mor.bilin_module.degenerate_plane_cone` | operation | V1 | bilin_module | — | `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.cone_comparison_inverse_right`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison` and 6 more | — |
| `mor.bilin_module.degenerate_plane_map` | operation | V1 | bilin_module | — | `rx:complete.lift.formed_arrow_action`, `rx:complete.lift.whole_formed_equation` | — |
| `mor.bilin_module.degenerate_plane_paired_cone` | operation | V1 | bilin_module | — | `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.separate_second_defining_equation` and 5 more | — |
| `mor.bilin_module.ordinary_kernel_inclusion` | operation | V1 | bilin_module | bilin_module, commutative_rings, modules_r | `rx:complete.rx08.full_coordinate_inclusion`, `rx:complete.rx08.restriction_zero_composite` | — |
| `mor.bilin_module.pulled_back_backward` | operation | V1 | bilin_module | bilin_module, commutative_rings | `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.cone_comparison_inverse_right` | — |
| `mor.bilin_module.pulled_back_forward` | operation | V1 | bilin_module | bilin_module, commutative_rings | `rx:addition.lift.complete_cone_triangle`, `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.cone_comparison_inverse_left`, `rx:addition.lift.cone_comparison_inverse_right`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison` and 2 more | — |
| `mor.sets.bilin_module_pairing` | operation | V1 | sets | bilin_module, commutative_rings, modules_r | `rx:complete.lift.final_full_pairing`, `rx:complete.lift.final_pairing_sample`, `rx:complete.lift.first_full_pairing`, `rx:complete.lift.whole_formed_equation`, `rx:complete.rx08.full_restricted_pairing`, `rx:complete.rx08.restricted_pairing_one` | — |

Existing registrations: none.

### `cat.arrows_bilin_module`

Layer (11); built from `cat.bilin_module`; milestone T212 Formed modules (M2); 29 computed statements on routes through it (29 V1, 0 V2).

Engine family **Bilinear and quadratic modules**: primary Sage; fallback Hecke through Oscar.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `lift.bilin_module.change_value_restriction` | lift | V1 | arrows_bilin_module, bilin_module | — | `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.separate_second_defining_equation`, `rx:addition.lift.unique_second_factor`, `rx:complete.lift.actual_second_inclusion`, `rx:complete.lift.composed_backward` and 12 more | — |
| `lift.bilin_module.restrict` | lift | V1 | arrows_bilin_module, bilin_module, modules_r | — | `rx:addition.lift.composed_factor_against_first`, `rx:addition.lift.second_input_compatibility`, `rx:addition.lift.separate_second_comparison`, `rx:addition.lift.separate_second_defining_equation`, `rx:addition.lift.unique_second_factor`, `rx:complete.lift.actual_second_inclusion` and 23 more | — |

Existing registrations (4): `lift.bilin_module.restrict#backward` on `lift.bilin_module.restrict#input` (sage-bilinear-lift); `lift.bilin_module.restrict#forward` on `lift.bilin_module.restrict#input` (sage-bilinear-lift); `lift.bilin_module.restrict#hom` on `lift.bilin_module.restrict#input` (sage-bilinear-lift); `lift.bilin_module.restrict#obj` on `lift.bilin_module.restrict#input` (sage-bilinear-lift).

### `cat.subobjects_groups`

Layer 5; built from `cat.groups`; milestone T214 Group kernels (M4-B0); 4 computed statements on routes through it (0 V1, 4 V2).

Engine family **Groups**: primary GAP through Sage; fallback Oscar; SymPy.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.subobjects_groups.domain` | functor (object and morphism actions) | V2 | groups, subobjects_groups | — | — | `groups.alternating.three_card`, `groups.kernel.identity_card`, `groups.kernel.sign_card`, `groups.kernel.trivial_card` |
| `obj.subgroups.alternating` | object constructor | V2 | subobjects_groups | — | — | `groups.alternating.three_card` |

Existing registrations (11): `meth.cardinality` on `cat.subobjects_groups` (gap-groups); `meth.cardinality` on `obj.subgroups.alternating` (gap-groups); `meth.cardinality` on `obj.subgroups.kernel` (gap-groups); `prop.is_abelian` on `cat.subobjects_groups` (gap-groups); `prop.is_abelian` on `obj.subgroups.kernel` (gap-groups); `prop.is_commutative` on `cat.subobjects_groups` (gap-groups); `prop.is_commutative` on `obj.subgroups.alternating` (gap-groups); `prop.is_commutative` on `obj.subgroups.kernel` (gap-groups); `prop.is_finite` on `cat.subobjects_groups` (gap-groups); `prop.is_finite` on `obj.subgroups.alternating` (gap-groups); `prop.is_finite` on `obj.subgroups.kernel` (gap-groups).

### `cat.arrows_groups`

Layer (6); built from `cat.groups`; milestone T214 Group kernels (M4-B0); 3 computed statements on routes through it (0 V1, 3 V2).

Engine family **Groups**: primary GAP through Sage; fallback Oscar; SymPy.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.arrows_groups.kernel` | functor (object and morphism actions) | V2 | arrows_groups, subobjects_groups | — | — | `groups.kernel.identity_card`, `groups.kernel.sign_card`, `groups.kernel.trivial_card` |
| `meth.group_arrow_kernel` | operation | V2 | arrows_groups, subobjects_groups | — | — | `groups.kernel.identity_card`, `groups.kernel.sign_card`, `groups.kernel.trivial_card` |

Existing registrations (2): `fun.arrows_groups.kernel` on `cat.arrows_groups` (gap-groups); `meth.group_arrow_kernel` on `cat.arrows_groups` (gap-groups).

### `cat.boolean_algebras` (BooleanAlgebras)

Layer 1; built from —; milestone T215 Boolean algebras (M4-B0); 14 computed statements on routes through it (14 V1, 0 V2).

Engine family **Boolean algebras, power sets**: primary Sage; fallback SymPy `boolalg`; z3.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.boolean_algebras.forget` | functor (object and morphism actions) | V1 | boolean_algebras, sets | — | `C14.1`, `F13.1`, `Q01.1`, `Q01.2`, `W06.1`, `finite_sets.difference` and 8 more | — |
| `obj.boolean_algebras.power_set` | object constructor | V1 | boolean_algebras | — | `C14.1`, `F13.1`, `Q01.1`, `Q01.2`, `W06.1`, `finite_sets.difference` and 8 more | — |
| `op.boolean_algebras.diff` | operation | V1 | boolean_algebras | boolean_algebras | `Q01.1`, `Q01.2`, `finite_sets.difference` | — |
| `op.boolean_algebras.inter` | operation | V1 | boolean_algebras | boolean_algebras | `finite_sets.intersection`, `finite_sets.intersection_subset`, `integration.normalized`, `integration.normalized_count` | — |
| `op.boolean_algebras.subset` | operation | V1 | boolean_algebras | boolean_algebras | `C14.1`, `W06.1`, `finite_sets.intersection_subset`, `finite_sets.subset_union`, `polynomials.irrational_roots` | — |
| `op.boolean_algebras.symm_diff` | operation | V1 | boolean_algebras | boolean_algebras | `finite_sets.symmetric_difference` | — |
| `op.boolean_algebras.union` | operation | V1 | boolean_algebras | boolean_algebras | `F13.1`, `finite_sets.subset_union`, `finite_sets.union` | — |

Existing registrations: none.

### `cat.integral_lattice`

Layer 10; built from `cat.commutative_rings`; milestone T216 Integral lattices (M4-B0); 1 computed statements on routes through it (0 V1, 1 V2).

Engine family **Lattices (quadratic forms)**: primary Sage; fallback Hecke through Oscar; PARI.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `fun.integral_lattice.forget_form` | functor (object and morphism actions) | V2 | bilin_module, integral_lattice | — | — | `lattices.rank.e8` |
| `obj.integral_lattice.e8` | object constructor | V2 | integral_lattice | — | — | `lattices.rank.e8` |

Existing registrations (4): `meth.cardinality` on `obj.integral_lattice.e8` (sage-modules); `meth.rank` on `obj.integral_lattice.e8` (sage-modules); `prop.is_abelian` on `obj.integral_lattice.e8` (gap-groups); `prop.is_commutative` on `obj.integral_lattice.e8` (gap-groups).

### `cat.enumerated_sets` (EnumeratedSets)

Layer 1; built from —; milestone T217 Set constructions (M4-coverage); 2 computed statements on routes through it (2 V1, 0 V2).

Engine family **Finite, countable, enumerated sets**: primary Sage; fallback SymPy.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `forget[clf.sets.enumerated]` | classifier forget (object and morphism actions) | V1 | enumerated_sets, sets | — | `N25.1`, `N25.2` | — |

Existing registrations: none.

### `cat.core_subobjects_sets`

Layer (2); built from `cat.subobjects_sets`; milestone T217 Set constructions (M4-coverage); 1 computed statements on routes through it (1 V1, 0 V2).

Engine family **Sets**: primary Sage; fallback SymPy sets; Catlab or CAP for general limits and colimits.

No row has its home here: the category is on the routes through the rows of other categories.

Existing registrations: none.

### `cat.subsets.subset_predicates`

Layer (3); built from `cat.core_subobjects_sets`, `cat.core_subobjects_sets`, `cat.sets`; milestone T217 Set constructions (M4-coverage); 1 computed statements on routes through it (1 V1, 0 V2).

Engine family **Sets**: primary Sage; fallback SymPy sets; Catlab or CAP for general limits and colimits.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `meth.set_eq` | operation | V1 | core_subobjects_sets, subobjects_sets, subsets.subset_predicates | — | `R03.1` | — |

Existing registrations: none.

### `cat.algebras` (Algebras)

Layer 8; built from `cat.commutative_rings`; milestone T220 Algebras (M4-coverage); 0 computed statements on routes through it (0 V1, 0 V2).

Engine family **Algebras**: primary Sage; fallback GAP; Oscar and Hecke.

No row has its home here: the category is on the routes through the rows of other categories.

Rows that only typing judgements read: `fun.algebras.forget`, `obj.algebras.mv_polynomials`, `obj.algebras.polynomials`.

Existing registrations: none.

### `cat.schemes_over_ring`

Layer (8); built from `cat.commutative_rings`; milestone T221 Schemes (M4-coverage); 0 computed statements on routes through it (0 V1, 0 V2).

Engine family: the survey has none; the plan names Sage `sage.schemes` and adds it to the survey record before the implementation.

No row has its home here: the category is on the routes through the rows of other categories.

Rows that only typing judgements read: `cat.schemes_over_ring`, `obj.schemes_over.spec_mv_polynomials`, `obj.schemes_over.spec_polynomials`.

Existing registrations: none.

### `cat.ideals_r`

Layer —; built from —; milestone T222 Module constructions (M4-coverage); 1 computed statements on routes through it (1 V1, 0 V2).

Engine family **Modules**: primary Sage; fallback Oscar or Macaulay2 for modules over polynomial rings; CAP.

| Row | Kind | Version | Catalogue owners | Parameters | V1 statements | V2 statements |
| --- | --- | --- | --- | --- | --- | --- |
| `meth.annihilator` | operation | V1 | core_modules_r, ideals_r, modules_r | — | `R01.1` | — |

Existing registrations: none.


## Notes

1. **Categories with no row.** `cat.core_groups`, `cat.subobjects_modules_r` and `cat.core_subobjects_sets` have no row with its home there. Each is on the route of a statement as an owner or a named category of rows whose home is a later category: the RX-03 bindings name $\mathrm{Core}(\mathbf{Grp})$; `meth.arrow_ker` and `meth.subobject_dim` are owned by `cat.subobjects_modules_r` and have their homes at `cat.arrows_modules_r` and `cat.core_subobjects_modules_r`; `meth.set_eq` (row R03 of the inventory) is owned by `cat.core_subobjects_sets` and has its home at `cat.subsets.subset_predicates`. The implementations of these categories are still prerequisites of those statements.
2. **Typing judgements only.** `cat.algebras` and `cat.schemes_over_ring` are read only by typing judgements (`algebras.polynomials`, `schemes.affine_line` and their siblings). They need no computed row for V1 or V2.
3. **Categories that this catalogue revision does not register.** The tasks T131 (the additive tower: additive magmas and additive semigroups) and T133 (preorders, semilattices, order lattices and bounded order lattices below Boolean algebras) add categories that the catalogue at `3f8aedf` does not have as structural steps. No route of these computations names them, so they have no entry here; they enter the implementation order at the place that their structural functors give them (`plan.md`, "Computational milestones").
4. **Calculus rows at `cat.sets`.** The catalogue declares the limit, integral and Taylor binders and the real functions at `cat.sets` with no parameter, so their home is `cat.sets`; their statements complete only with the ring categories (milestone T203 and later), and their engine is the Calculus family (SymPy, with the Sage symbolic ring as fallback).
5. **Most permanent statements are V1.** The permanent files restate `SPEC.md`, so 112 of the 134 computed permanent statements carry a spike computation or are K1 identifiers. The V2 statements are the lattice and formed-module statements, the group and F9 statements of K3 and K14, and the arithmetic and set statements that the spike did not compute.
