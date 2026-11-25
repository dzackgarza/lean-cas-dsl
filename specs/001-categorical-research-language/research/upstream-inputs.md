# Upstream inputs of the kernel: status on lean-categories `main`

Snapshot. This is a reading of fixed revisions, not a maintained record.

| Source | Revision | How it was read |
| --- | --- | --- |
| lean-categories `main` | `443fba9` (export of 2026-11-25) | files below; 1358 Lean files searched |
| Published catalogue (`declared-ports.json`, `extension-ports.json`) | mathematics revision `3f8aedf` | every entry parsed by script |
| Kernel source | `integration/kernel-v1-20261106` at `fc7fdf8` | excerpts, to see what the reader asks |
| Task list and plan | lean-cas-dsl `main`, read at `a9f3790` | sections named in the request. `main` moved to `45910a5` during the work; that commit rewords the rows T034, T048 and T059 to name T119, T123 and T124, and changes no row of the items below. |
| Mathlib order categories | `db584cd6` (local package tree) | `Mathlib/Order/Category/*.lean` |
| lean-categories issues | read 2026-11-25 | #182 to #189 in full; 150 issue bodies searched |

Conventions. **Fact** is a statement that I read at the given file and line. **Inference** is a conclusion that no source states; each one has the label. Paths are relative to `LeanCategories/` of the snapshot. `Sem/` is `Catalogue/Semantics/`. `Reg/` is `Catalogue/Registry/`.

## Summary

| Item | Status on `main` | Issue | First consumer |
| --- | --- | --- | --- |
| 1. Comparison of the monoid routes of a ring | Present for the two multiplicative routes. A third structural route (additive group read multiplicatively) is not comparable. | None for the cell. The remaining need is item 5. | T055 |
| 2. Binder operations as computation families | Partly. Eight binder rows; no computation reference for a binder operation. | New (N2) | T037 |
| 3. Membership, transpose, image of the power object | Partly. Fields of `pow.sets` only; direct image, equality and `contains` are rows. | New (N3) | T113, then T035 |
| 4. Linearity evidence at `W →ₗ[R] W'` | Partly. Admission exists for $M \to N$ in `ModuleCat` only. | New (N4) | T046 |
| 5. Owner of multiplication, addition, numerals | Partly. No operation at magmas; ring and semiring rows declare no restriction; the additive group read multiplicatively is a structural route. | New (N5a, N5b); rule in #53 §5 | T104 (Leaves 0.2); T055 by inference |
| 6. Order categories | Partly. `PartOrd` and `LinOrd` each registered twice; no semilattice or lattice category. | New (N6) | T104 (Leaves 0.3) |
| 7a. Role of the arrow and core constructors | Absent | New (N7a); related #53 §16, #54 | T061 |
| 7b. Refinement witness and proof procedure of a classifier | Absent | New (N7b) | T057 |
| 7c. Written forms `X ∖ 0`, `Spec A`, `X in C/Y` | Partly. The field exists; the rows use composed names; `Spec` is not a functor. | New (N7c) | T036 |
| 7d. Ellipsis definition and subtraction | Absent | New (N7d) | T068 |
| 7e. Three-valued decision | Not an upstream input | None | T113 |
| 7f. Equality as a published predicate | Present | None; closing procedure is #183 | T113 |
| 7g. Evidence procedures of admissions | Present for all 15 admissions | Literal obligations: #183 | T021 |
| 7h. Agreement over a route family that is not finite | Absent for the cycle sets ⇄ subsets | New (N7h) | T056 |
| 7i. Own-ring evaluation of a polynomial | Partly. The theorem exists; no reading rule. | Extend #188 | T036 |

## Corrections to the readings in the task list

1. **Fact.** In both catalogue files of the snapshot, `operations` and `inputForms` hold all eight binder ids, with `bind.sets.limit`, `bind.sets.limit_at_infinity` and `bind.sets.power_series_sum`. The row of TASKS that says these three "are not operations there" does not agree with these files.
2. **Fact.** A membership row exists: `fun.subsets.contains` with `meth.contains` (`Sem/Foundation/Subsets.lean:192-206`), in the published catalogue also. It is membership in a subobject of a set, not the membership map of the power object.
3. **Fact.** `cat.rings` has three structural routes to `cat.monoids` at `3f8aedf`, not two: direct; through semirings; through the additive group and groups. Computed from the structural functor rows and classifier forgets of `extension-ports.json`.
4. **Fact.** `main` has 24 registered ids that the published catalogue does not have (well-ordered sets, cusps, enumerated rankings, `fun.sets.power_set`, `cell.sets.finite_subsets.inclusion`, `lim.groups.product`). None of them supplies an item below.

## 1. Comparison of the structural monoid routes of a ring

**Consumers.** T034, T055, T056.

**Status: present for the pair (direct, through semirings).**

Facts:

- The cell row is `Sem/Algebra/ComputationDerivations.lean:156-163`: source `cat.rings`, target `cat.monoids`, `left := #[fun.rings.multiplicative_monoid]`, `right := #[fun.rings.semiring, fun.semirings.monoid]`, `invertible := true`.
- Its declaration is `ringMultiplicativeComparison : Ports.ringsMultiplicative.toFunctor ≅ (ringsSemiring ≫ semiringsMonoid).toFunctor := Iso.refl _` (`:90-92`). The components are identities. The direction is from the direct route to the route through semirings. The two functors are equal by `rfl` (`:85-87`).
- The two factors are structural functor rows (`:138-154`).
- A cell's direction designates the route on which a call runs (`Reg/Entry.lean:411-416`). `Sem/Algebra/PortComparison.lean:17-19` states the convention for `cmp.rings.carrier`: the call runs on the source route.
- The third route is `fun.rings.additive_group`, `fun.additive_groups.to_groups`, `fun.groups.monoid` (`Sem/Algebra/Ports.lean:103-119`, all `structural := true`). Along it the monoid multiplication is the addition of the ring: `MonoidOperationAgreement.additive_port` (`Sem/Algebra/MonoidOperationAgreement.lean:61-66`). `Ports.lean:20-32` says that the routes are not identified.
- A ring does not inherit `·` today. `op.rings.mul` binds the name at `cat.rings` and lookup stops there (`Reg/OperationBindingTests.lean:19-28`; rule at `Reg/Semantic.lean:1771-1778`). The same test removes that row and asserts that the routes to monoids then all survive, with no choice by order (`:29-35`). The test imports the monoid and ring rows only, so its routes are the direct one and the additive one. Inference: in the whole catalogue the route through semirings stops at `op.semirings.mul`, by the same first-binding rule.

Inference: the registered cell is the required comparison for the two multiplicative routes, with its components and its direction. By the stated convention the direct route is the designated one.

Inference: the consumer "inherited `mul` on a ring" lacks one thing that no cell can give. It lacks the declaration that the symbol `·` of a ring denotes the operation of the multiplicative port and not the operation that the additive port reaches. That declaration is item 5. The kernel side (no registered cell is consumed) is the existing rows T055, T056, T060.

**Mathematical requirement.** None beyond item 5. For a ring $R$ the functors $U_\times : \mathbf{Ring} \to \mathbf{Mon}$ and $\mathbf{Ring} \to \mathbf{SemiRing} \to \mathbf{Mon}$ are equal (Mathlib `forget₂`), and the registered isomorphism states it.

**Issue.** None. **First consumer.** T055.

## 2. Binder operations as published computation families

**Consumers.** T037, T067.

**Status: partly present.**

Facts:

- Eight binder rows are registered: `bind.sets.finite_sum`, `finite_product` (`Sem/Algebra/FiniteSums.lean:118-126`); `integral` (`Sem/Algebra/Calculus.lean:269-272`); `real_series`, `complex_series`, `power_series_sum` (`Sem/Algebra/Series.lean:475-488`); `limit`, `limit_at_infinity` (`Sem/Algebra/RealLimits.lean:511-519`).
- A binder row names its `operation`, a morphism family out of a registered object of maps, and its `domain` (`Reg/Entry.lean:284-303`; validation at `Reg/Semantic.lean:2632-2690`).
- `ComputationRef` has the constructors `operation`, `functor`, `method`, `construction`, `morphism` (`Reg/Computation.lean:33-39`). It has no constructor for a binder operation.
- No morphism row names a binder operation. Search: the eight declaration names (`sumOver`, `prodOver`, `integral`, `realSeriesSum`, `complexSeriesSum`, `powerSeriesSum`, `limit`, `limitAtInfinity`) in all Lean files; each occurs in registry rows only as a binder `operation`.
- Proved identities with a binder operation on one side exist and are not published as derivations: `sumOver_eq_sum`, `prodOver_eq_prod` (`FiniteSums.lean:88-105`), `realSeriesSum_eq`, `complexSeriesSum_eq` (`Series.lean:199`, `:211`), `powerSeriesSum_eq` (`Series.lean:343`), `limit_eq` (`RealLimits.lean:151`).
- The kernel takes its published families from `ComputationRef` (`CasCompiler/PublishedPorts.lean:22-27` at `fc7fdf8`); a binder is found by a scan of `state.binders` (`CasCompiler/Lower.lean:193`, `:331`).

**Mathematical requirement.** The operation of a binding operator is a morphism of sets out of an object of maps: $\int_a^b : C(\mathbb{R}) \to \mathbb{R}$, $\lim_{t \to a}$ on the maps convergent at $a$, $\sum_{t \in A} : Y^X \to Y$ for a finite subset $A$, and $\sum$ on summable families (Bourbaki, *Algebra I*, I.2.1; Mathlib `Finset.sum`, `tsum`, `intervalIntegral`). Each must be a family that a checked derivation can name as target or prerequisite. The identities above then become derivations.

**Issue: new (N2).** #185 covers the application of an object of maps, not an operation on one.

Draft title: *The operation of a binding operator as a published family*

```text
A binding operator applies an operation to the map t ↦ e: the integral C(ℝ) → ℝ at bounds a, b; the limit at a of a map convergent there; the sum of a map over a finite subset; the sum of a summable family. Each is a morphism of sets out of an object of maps.
At main (443fba9) eight binder rows name these morphisms as their `operation`. A computation reference names an operation, a functor, a method, a construction or a morphism; it cannot name the operation of a binder.
Identities with such an operation on one side are proved and cannot be published as derivations: `sumOver_eq_sum`, `prodOver_eq_prod`, `realSeriesSum_eq`, `complexSeriesSum_eq`, `powerSeriesSum_eq`, `limit_eq`.
Expected:
- each binder operation is a published family, with its parameters and its object of maps, that a derivation can take as target or prerequisite;
- the sum and product over a finite subset A are published as the values at A of the registered `∑` and `∏`;
- the real and complex series are published as the sum of a summable family in a Hausdorff commutative topological monoid, and the power-series sum as that sum in R[[t]];
- the limit is published with its uniqueness.
Sources: Bourbaki, Algebra I, I.2.1; Mathlib `Finset.sum`, `tsum`, `intervalIntegral`, `Filter.Tendsto`.
```

**First consumer.** T037.

## 3. Membership, transpose and image of the power object

**Consumers.** T035, T113.

**Status: partly present.**

Facts:

- `PowerObjectEntry` has the fields `member`, `transpose`, `extent`, `empty`, `singleton`, `terminal`, `image`, `directImage` (`Reg/Entry.lean:368-400`). The row `pow.sets` fills them (`Sem/Foundation/PowerSets.lean:387-399`).
- The declarations: `member : X × 𝒫 X ⟶ Ω` (`PowerSets.lean:172`), `transpose : (X ⟶ Ω) → (1 ⟶ 𝒫 X)` (`:180`), `extent` (`:184`), `image : (X ⟶ Y) → (1 ⟶ 𝒫 Y)` (`:197`), `directImage : (X ⟶ Y) → (𝒫 X ⟶ 𝒫 Y)` (`:203`).
- Rows that a computation reference can name: `mor.sets.direct_image` (`:401-403`), `mor.sets.equality` (`:464-466`), `fun.sets.power_set` (`:357-361`), `fun.sets.finite_subsets.direct_image` (`Sem/Foundation/FiniteSubsets.lean:164-169`), `fun.subsets.contains` and `fun.subsets.set_eq` with their methods (`Sem/Foundation/Subsets.lean:192-209`).
- No morphism, functor, method or operation row names `member`, `transpose`, `extent` or `image`. Search: rows named `∈`, `contains`, `mem*`, `member*`, `image`, `preimage`, `transpose` in the parsed operation, morphism and method rows; the four declaration names in all Lean files.
- `transpose` is declared at the terminal stage only: its result is a global element $1 \to \mathcal{P}X$.
- No inverse image of subsets is registered. Search: `preimage`, `inverse image`, `inverseImage` in `Catalogue/`.
- The kernel reads `power.row.member` and `power.row.transpose` from the row (`CasCompiler/SourceSubset.lean:131-147` at `fc7fdf8`).

**Mathematical requirement.** The power object $(\mathcal{P}X, \in_X)$ of an elementary topos (Mac Lane–Moerdijk, *Sheaves in Geometry and Logic*, IV.1): membership $\in_X : X \times \mathcal{P}X \to \Omega$; for every stage $Y$ the bijection $\operatorname{Hom}(Y \times X, \Omega) \cong \operatorname{Hom}(Y, \mathcal{P}X)$; the extent of a subset; the image of a map (Mathlib `Set.range`, `Set.image`, `Set.preimage`). Each must be a family that a derivation can name. The relation between $\in_X$ and `contains` on $\operatorname{Sub}(\mathbf{Set})$ must be a theorem.

**Issue: new (N3).**

Draft title: *Membership, comprehension, extent and image of the power object as published families*

```text
The power object 𝒫X of sets has membership ∈ : X × 𝒫X → Ω, the transpose that sends a predicate Y × X → Ω to the map Y → 𝒫X that it classifies, the extent of a subset and the image of a map (Mac Lane–Moerdijk, Sheaves in Geometry and Logic, IV.1).
At main (443fba9) the row `pow.sets` holds `member`, `transpose`, `extent`, `empty`, `singleton`, `terminal` and `image` as fields. Of the power-object maps only the direct image is a named family (`mor.sets.direct_image`). A computation derivation cannot name a field of the row.
`transpose` is declared at the terminal stage only: (X → Ω) → (1 → 𝒫X). No inverse image of subsets is registered.
Expected:
- membership is a published family X × 𝒫X → Ω, natural in X;
- the transpose is declared at every stage Y, as the bijection Hom(Y × X, Ω) ≅ Hom(Y, 𝒫X) with its two inverse laws; the present global form is its case Y = 1;
- the image of f : X → Y is published and equals the direct image of the whole of X; the inverse image 𝒫Y → 𝒫X is declared with its adjunction to the direct image;
- the extent is published with its inclusion into X;
- a theorem relates membership in 𝒫X to `contains` on Subobjects(Sets).
Sources: Mathlib `Set.image`, `Set.preimage`, `Set.range`, `Set.image_subset_iff`.
```

**First consumer.** T113 (document order), then T035.

## 4. Linearity evidence for a map written at `W →ₗ[R] W'`

**Consumer.** T046 (second lift of RX-LIFT, `composite_lift`).

**Status: partly present.**

Facts:

- `obj.sets.module_morphisms` is `linearMaps (R : RingCat) (M N : ModuleCat R) := M ⟶ N` with `admitLinear` (a map $M \to N$ and a proof of `IsLinearMap R f`) and `linearEvidence` (`Sem/Modules/LinearMaps.lean:68`, `:90-92`, `:122`, row `:159-165`).
- `fun.bilin_module.change_value` is declared with `(R : Type u) [CommRing R] (W W' : Type u) [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')` (`Sem/Modules/Bilinear/Valued/CatalogueRegistration.lean:156-160`, row `:214-224`). The lift `lift.bilin_module.change_value_restriction` has the same parameter (`Sem/Modules/Bilinear/Valued/ChangeValueLifts.lean:40-43`, row `:161-165`). So do `fun.quad_module.change_value` (`Sem/Modules/Quadratic/Valued/CatalogueRegistration.lean:116-118`) and `fun.lattice.change_value` (`Sem/Lattices/Valued/CatalogueRegistration.lean:345-347`).
- No object row has a declaration, an admission or an evidence procedure at the type `W →ₗ[R] W'`. All 15 rows with an `admission` were listed; the one for linear maps is the row above.
- `FunctorEntry` and `LiftEntry` have no field that names an admission for a parameter (`Reg/Entry.lean:505-520`, `:85-93`).
- Change of values preserves identity and composition: `changeValue_id`, `changeValue_comp` (`Modules/Bilinear/Valued/ChangeValue.lean:36-43`). The family `fam.bilin_module` records `transportSemantics := .discrete` (`Sem/Modules/Bilinear/Valued/CatalogueRegistration.lean:74-81`).
- The closed requirements inventory #56 (B2) states that the categorical language speaks category homs, which repackage the bundled hom types.

Inference: the linearity procedure exists; what is absent is the statement that the parameter of change of values is an element of the registered set of module morphisms.

**Mathematical requirement.** For a commutative ring $R$, $W \mapsto \mathrm{Bil}_R(W)$ is a functor $\mathbf{Mod}_R \to \mathbf{Cat}$: an $R$-linear $f : W \to W'$ acts by $b \mapsto f \circ b$ (Mathlib `LinearMap.compr₂`). Its parameter is a morphism of $\mathbf{Mod}_R$, an element of $\operatorname{Hom}_{\mathbf{Mod}_R}(W, W')$ (Mathlib `ModuleCat.ofHom`, `ModuleCat.Hom.hom`). The same holds for quadratic modules and lattices, and for the lift of subobjects along change of values.

**Issue: new (N4).**

Draft title: *Change of values as the action of module morphisms on categories of forms*

```text
For a commutative ring R and R-modules W, W′, an R-linear map f : W → W′ gives the functor Bil_R(W) → Bil_R(W′) that composes each form with f. Identity and composition are preserved (`changeValue_id`, `changeValue_comp`), so W ↦ Bil_R(W) is a functor Mod_R → Cat and f is a morphism of Mod_R.
At main (443fba9) the rows `fun.bilin_module.change_value`, `fun.quad_module.change_value`, `fun.lattice.change_value` and the lift `lift.bilin_module.change_value_restriction` take f as a Mathlib linear map `W →ₗ[R] W'` between carrier types. The family `fam.bilin_module` records its transport in W as discrete.
The set of module morphisms, with its admission of a map by a proof of linearity (`obj.sets.module_morphisms`, `admitLinear`, `linearEvidence`), is declared for Hom in `ModuleCat R` over `RingCat`. No declaration relates the parameter f to that set.
Expected:
- the parameter of change of values is an element of the registered set Hom_{Mod_R}(W, W′), for commutative R through CommRing → Ring, so that a map of the carriers with its linearity is admitted by the one existing procedure;
- the covariant dependence of Bil_R(W), Quad_R(W) and the lattice categories on W is declared, with the identity and composition laws that are already proved;
- the lift of subobjects along change of values is stated at the same morphism.
Sources: Mathlib `ModuleCat.ofHom`, `ModuleCat.Hom.hom`, `LinearMap.compr₂`; requirements inventory #56, B2.
```

**First consumer.** T046.

## 5. Owner of multiplication, of addition and of the numerals

**Consumers.** T104 (Leaves 0.2, SC-015). Inference: T055 and T056 observe the selected reading of `·`, so they consume the same declaration first.

**Status: partly present.**

### What exists

Facts:

- Rows named `·`: `op.monoids.mul` (`Sem/Algebra/MonoidOperations.lean:64-66`), `op.semirings.mul` (`Sem/Algebra/Semirings.lean:191-193`), `op.rings.mul` (`Sem/Algebra/NamedRings.lean:149-151`). Rows named `+`: `op.additive_monoids.add` (`Sem/Algebra/AdditiveOperations.lean:92-95`), `op.semirings.add` (`Semirings.lean:188-190`), `op.rings.add` (`NamedRings.lean:145-147`). Other rows: `op.monoids.one` named `1`, `op.groups.inverse`, `op.rings.neg`, `op.rings.pow`, `op.semirings.pow`, `op.modules.zero`, `op.modules.scalar_action`. `main` has 25 operation rows.
- No operation row is at `cat.magmas`, `cat.semigroups`, `cat.additive_magmas` or `cat.additive_semigroups`. Search: `category :=` of all 25 rows. The four categories are registered (`Sem/Algebra/CatalogueRegistration.lean:133-162`).
- `OperationEntry.refines` declares an operation as the restriction of a general owner along a structural route, with a proved identification (`Reg/Entry.lean:328-334`, `:364-365`; validation `Reg/Semantic.lean:2507-2545`). One row uses it: `op.linear_orders.le` (`Sem/Foundation/PowerSets.lean:451-458`). The ring and semiring rows have `refines := none`.
- The equalities exist as theorems and as derivations, not as declarations on the rows: `ring_mul` (`MonoidOperationAgreement.lean:36-40`); `derive.rings.mul.monoid`, `derive.semirings.mul.monoid`, `derive.rings.mul.semiring` (`ComputationDerivations.lean:183-205`).
- `Semirings.lean:21-32` states the built ownership: "The rings ℤ, ℚ, ℝ, ℂ are refined in `Rings` only, so each operation on their elements has one owner."
- `fun.additive_groups.to_groups` reads an additive group multiplicatively (Mathlib `AddGrpCat.toGrp`) and is structural (`Ports.lean:109-113`). `fun.modules.additive_group` is structural (`Sem/Modules/CatalogueRegistration.lean:581`).
- `cat.rings` has two structural routes to `cat.additive_monoids` (through the additive group; through additive commutative monoids). No cell at additive monoids compares them; the registered cells compare carriers at sets (`cell.rings.additive_monoid_carrier`, `cell.additive_groups.carrier`).
- `cat.semirings` has two structural functors, to sets and to monoids (`Semirings.lean:171-175`, `ComputationDerivations.lean:147-154`). It has none to additive monoids.
- Numerals: `num.rings` is the image of $k$ under the ring map $\mathbb{Z} \to R$ (`NamedRings.lean:90-94`, row `:113-115`); `num.semirings` is the image under $\mathbb{N} \to S$ (`Semirings.lean:90`, row `:177-179`). `NumeralEntry` has the fields `id`, `over`, `declaration` (`Reg/Entry.lean:241-245`). No theorem relates `ringNumeral` to `semiringNumeral`. Search: both names in all Lean files.
- The kernel reads `refines` of an operation binding (`CasCompiler/Resolve.lean:256-270` at `fc7fdf8`).

### The intended owner

Facts (governing sources of lean-categories):

- FOUNDATIONS Definition 12.1: $\mathbf{Mag} := \operatorname{Op}_2(\mathbf{Set})$; each stage has the forgetful functor to the preceding one; distant forgetful functors are composites. Definition 12.2: $\mathbf{AddMag}$ and $\mathbf{MulMag}$ are distinct objects. Definition 12.3: a ring has $U_+ : \mathbf{Ring} \to \mathbf{AddAbGrp}$ and $U_\times : \mathbf{Ring} \to \mathbf{MulMon}$ (`FOUNDATIONS.md:763-811`).
- Issue #53 §5: a method is declared where the construction is generated; a derived name points to a composite or an alias and does not introduce a second operation.
- `AGENTS.md:575-595` (§10.3, §10.5): declare at the lowest level where it is generated; an object acquires a method by functorial composition.
- `Sem/Algebra/Catalogue/Magmas.lean:13-17`: "Magmas cluster — least-host ownership".

Inference: the owner of `·` is the category of magmas (`cat.magmas`). The owner of `+` is the category of additive magmas. `1` belongs to unital magmas or monoids, `0` to additive monoids, the inverse to groups, negation to additive groups, and the power $x \mapsto x^k$ to monoids. The monoid, semiring and ring rows are restrictions of those owners.

### What must change so that `2 * 3 = 6 in ℤ` reads its multiplication through a monoid structure of ℤ

Fact: today the reading is `op.rings.mul`, bound at `cat.rings` with no restriction. The route `rings → monoids → semigroups → magmas → sets` carries the carrier of `obj.rings.integers` (`NamedRings.lean:117-128`), and no operation is declared on its last two stages. A computed value can already come from the monoid through `derive.rings.mul.monoid`; that is a derivation of the value, not the reading.

Inference, the smallest set of declarations:

1. `·` is declared at its generating category, and the rows above it are its restrictions along the multiplicative functors, with the proved equality of the whole families. For a ring the route is $U_\times$.
2. `+` is declared the same way on the additive side. `op.semirings.add` needs the functor $\mathbf{SemiRing} \to \mathbf{AddCommMon}$ (Mathlib `forget₂`), which is not registered. The two additive routes of a ring need their comparison at additive monoids.
3. The multiplicative reading of an additive group must not carry operation names. Inference from the rows, not executed: on an additive group, a module or a ring without its own row, the names `·`, `1` and `⁻¹` reach `op.monoids.mul`, `op.monoids.one` and `op.groups.inverse` along `fun.additive_groups.to_groups` and denote addition, zero and negation.
4. The numeral of a ring is declared as the numeral of its underlying semiring (Mathlib `Int.cast_natCast`). Its generating level is an additive monoid with a chosen element $1$ (Mathlib `AddMonoidWithOne`, `Nat.cast`). #186 owns the numeral `0` of additive monoids.

**Mathematical requirement.** The binary operation of a magma $\mu_X : X \times X \to X$, natural in magma homomorphisms, is the structure that $\mathbf{Mag}$ adds to $\mathbf{Set}$ (Bourbaki, *Algebra I*, I.1; Mathlib `MagmaCat`, `Semigrp`, `MonCat`). The multiplication of a ring is $\mu$ at $U_\times(R)$; its addition is the additive operation at $U_+(R)$. Each operation of a richer category is the restriction of one owner, by a theorem about the whole family.

**Issue: new (N5a, N5b).** #53 §5 states the rule and is open; no issue records these rows.

Draft title (N5a): *One multiplication and one addition: the operations of magmas, with the operations of monoids, semirings and rings as their restrictions*

```text
A magma is a set with one binary operation (FOUNDATIONS Def. 12.1, Mag = Op₂(Set)). A ring has two: on its multiplicative monoid U_×(R) and on its additive group U_+(R) (Def. 12.2, 12.3).
At main (443fba9) `·` is a separate row at monoids, at semirings and at rings, and `+` at additive monoids, at semirings and at rings. No operation is declared at magmas, semigroups, additive magmas or additive semigroups.
No row states that the multiplication of a ring is that of U_×(R), or that its addition is that of U_+(R). The equalities are separate theorems (`MonoidOperationAgreement.ring_mul`, `additive_port`) and derivations.
`AddGrpCat.toGrp` is a structural functor. Along it the multiplication and the unit of a monoid are the addition and the zero of the additive group (`additive_port`), so an additive group, a module or a ring has structural routes on which `·` and `1` denote `+` and `0`.
Expected:
- the binary operation is declared once at magmas and once at additive magmas, natural in homomorphisms; the unit at unital magmas or monoids, zero at additive monoids, the inverse at groups, negation at additive groups, x ↦ xᵏ at monoids;
- each operation of a richer category (semigroups, monoids, groups, semirings, rings, commutative rings, modules) is the restriction of that owner along a stated structural functor, with the equality of the whole families proved;
- Semiring → AddCommMon is a structural functor; the two routes Ring → AddMon are compared at additive monoids;
- no route gives an additive structure the multiplicative names, or the reverse.
Sources: FOUNDATIONS §12; #53 §5; Bourbaki, Algebra I, I.1; Mathlib `MagmaCat`, `Semigrp`, `MonCat`, `AddMagmaCat`, `forget₂`.
```

Draft title (N5b): *The numerals of a ring are the numerals of its underlying semiring*

```text
The numeral k of a semiring S is the image of k under the unique semiring map ℕ → S. The numeral k of a ring R is the image of k under the unique ring map ℤ → R. Every ring has an underlying semiring, by the registered functor Ring → SemiRing.
At main (443fba9) the rows `num.semirings` and `num.rings` declare the two families. No declaration relates them.
Expected:
- the theorem that, for every ring R and every k ∈ ℕ, the numeral k of R equals the numeral k of its underlying semiring (Mathlib `Int.cast_natCast`), stated for the whole family, so that the numeral of rings is the restriction of the numeral of semirings;
- the numerals 0 and 1 equal the zero of the additive monoid and the unit of the multiplicative monoid (Mathlib `Nat.cast_zero`, `Nat.cast_one`);
- the generating level of numerals is decided from the mathematics: an additive monoid with a chosen element 1 (Mathlib `AddMonoidWithOne`, `Nat.cast`; ℕ is the free monoid on one generator). Issue #186 owns the numeral 0 of additive monoids.
```

**First consumer.** T104 as recorded. Inference: place the task before T055.

## 6. The order categories

**Consumer.** T104 (Leaves 0.3).

**Status: partly present.**

Facts:

- Pair A: `cat.partially_ordered_sets` and `cat.totally_ordered_sets` (`Sem/Foundation/CatalogueRegistration.lean:152-162`), declared `Cat.of PartOrd` and `Cat.of LinOrd` (`Foundation/Sets.lean:519`, `:522`). Their functors to sets, `fun.sets.partially_ordered_to_sets` and `fun.sets.totally_ordered_to_sets`, do not set `structural` (`:188-202`). The classifier `clf.linear_orders.well_ordered` has `cat.totally_ordered_sets` as host (`Sem/Foundation/WellOrderedSetsRegistration.lean:138-143`), and `fun.well_ordered_sets.linear_order` has it as target (`:157-164`). Issue #98 (closed 2026-11-05) requested categories with these two names.
- Pair B: `cat.partial_orders` and `cat.linear_orders` (`Sem/Foundation/PowerSets.lean:309-319`), also `Cat.of PartOrd` and `Cat.of LinOrd` (`:89-92`). Structural functors: `fun.partial_orders.forget`, `fun.linear_orders.forget`, `fun.linear_orders.to_partial_orders` (`:327-344`). Cell `cmp.linear_orders.carrier` (`:363-370`). Operations `op.partial_orders.le`, `op.linear_orders.le` (a restriction of the first), `op.linear_orders.lt` (`:447-462`). Objects ℕ, ℤ, ℚ, ℝ (`:422-445`) and `FinOrder`, `ReverseFinOrder` (`Sem/Foundation/FiniteOrders.lean:81-94`).
- No functor, cell or object row relates pair A to pair B. Search: every functor, cell, classifier, object and operation row that names an order category.
- The functor $\mathbf{LinOrd} \to \mathbf{PartOrd}$ is defined twice: `Foundation/WellOrderedSets.lean:152` and `PowerSets.lean:118`.
- No category of preorders, semilattices or order-theoretic lattices is registered. Search: `SemilatSupCat`, `SemilatInfCat`, `semilattice`, `Lat`, `Preord`, `BddLat`, `DistLat`, `HeytAlg`, `BddOrd`, `Frm`, `CompleteLat` in `Catalogue/`, `Foundation/`, `Orders/` and `Orders.lean`. The hits are the composite `forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd` inside one functor (`PowerSets.lean:119`), two docstrings (`Foundation/WellOrderedSets.lean:20`, `:149`) and the imports of `Orders.lean`, which registers nothing.
- `cat.boolean_algebras` has one structural functor, to sets (`PowerSets.lean:321-325`). `⊆`, `∪`, `∩` of a Boolean algebra are separate rows (`:405-420`) with no restriction declared. No operation is named `⊔`, `⊓`, `min` or `max`.
- Mathlib `db584cd6` has `Preord`, `PartOrd`, `LinOrd`, `SemilatSupCat` (join-semilattices with a bottom), `SemilatInfCat` (meet-semilattices with a top), `Lat`, `BddLat`, `DistLat`, `BddDistLat`, `HeytAlg`, `BoolAlg`, with `forget₂` instances `LinOrd → Lat`, `Lat → PartOrd`, `PartOrd → Preord`, `BddLat → Lat`, `BddLat → SemilatSupCat`, `BddLat → SemilatInfCat`, `SemilatSupCat → PartOrd`, `SemilatInfCat → PartOrd`, `BoolAlg → BddDistLat` (`Mathlib/Order/Category/Semilat.lean:29-45`, `:72`, `:108`; `Lat.lean:152`; `LinOrd.lean:127`; `BddLat.lean:113-125`).
- The closed inventory #56 names the order cluster: `Preord`, `PartOrd`, `LinOrd`, `Lat` with their forgetful tower to sets, and orderedness as a functor lift.

Inference: the statements of Leaves 0.3 (`0 ≤ 1 in FinOrder(5)`) read rows of pair B only, and those rows exist. The well-order classifier is not reachable from an object of pair B.

**What the scaffolding sets → orders → semilattices and lattices needs.** One category for each of preorders, partial orders and linear orders. Categories of join-semilattices, meet-semilattices and lattices. The forgetful functors between them as structural functors, with a comparison for each pair of parallel routes. `≤` and `<` at preorders, join and meet at the semilattices, `min` and `max` of a linear order as its meet and join, and the rows of Boolean algebras as restrictions.

**Mathematical requirement.** The tower $\mathbf{LinOrd} \to \mathbf{Lat} \to \mathbf{SemiLat}_{\vee}, \mathbf{SemiLat}_{\wedge} \to \mathbf{PartOrd} \to \mathbf{Preord} \to \mathbf{Set}$ (Davey–Priestley, *Introduction to Lattices and Order*, ch. 2; Mathlib `Order/Category`). A semilattice without a bound, such as $(\mathbb{Z}, \max)$, is not an object of Mathlib's `SemilatSupCat`; the issue decides the generality.

**Issue: new (N6).**

Draft title: *One category for each kind of order; semilattices and lattices with their forgetful functors and operations*

```text
At main (443fba9) the catalogue names Mathlib's `PartOrd` twice (`cat.partially_ordered_sets`, `cat.partial_orders`) and `LinOrd` twice (`cat.totally_ordered_sets`, `cat.linear_orders`).
The first pair has functors to sets that are not structural, and hosts the well-order classifier. The second pair has the structural functors, the relations ≤ and <, and the named orders ℕ, ℤ, ℚ, ℝ, Fin. No functor or cell relates the pairs. LinOrd → PartOrd is defined twice.
Preorders, semilattices and order-theoretic lattices are not registered. Boolean algebras have a functor to sets only; their ⊆, ∪, ∩ are not related to ≤, join and meet.
Expected:
- one registered category for each of preorders, partial orders and linear orders, each named once, with the well-order classifier on the one category of linear orders;
- categories of join-semilattices, meet-semilattices and lattices, at a generality that admits a semilattice without a bound (ℤ under max); Mathlib's `SemilatSupCat` and `SemilatInfCat` are the bounded cases;
- the forgetful functors LinOrd → Lat → semilattices → PartOrd → Preord → Set and BoolAlg → Lat, with the comparison of every pair of parallel routes;
- ≤ and < at their generating category, join and meet at the semilattices, min and max of a linear order as its meet and join, ⊥ and ⊤ at bounded orders; ⊆, ∪, ∩ of a Boolean algebra as their restrictions.
Sources: Davey–Priestley, Introduction to Lattices and Order, ch. 2; Mathlib `Order/Category/{Preord,PartOrd,LinOrd,Semilat,Lat,BddLat,BoolAlg}`; inventory #56, the order cluster.
```

**First consumer.** T104 (Leaves 0.3).

## 7. Other rows of the correction tables

### Rows that an existing issue covers

| TASKS row (task) | Required upstream | Issue |
| --- | --- | --- |
| T034, numeral domain obligation | evidence procedure on the numeral row | #183 (with its audit note LC-183-F01) |
| T035, graph literal totality | evaluation on the graph-literal row | #183 |
| T113, closing of a literal evaluation | registered closing procedure | #183 |
| T035, T036, T075, surface forms tied by literals | notation of morphisms and methods | #184 (with its audit note LC-184-F01) |
| T032, T036, object application | computation reference of an application | #185 |
| T034, numeral `0` of an additive monoid | numeral row | #186 |
| T048, `K.leg(j)` | names of the objects of a limit shape | #187 |
| T059, changed reading of an operand | coercion rule | #188 (with its audit note LC-188-F01) |
| T036, Krull dimension of `ℚ[x, y]` | commutative-ring object | #189 |
| T115, permitted choice | choice fibre | #182 |

### 7a. A registered role for the arrow and core constructors

**Consumer.** T061. **Status: absent.**

Facts:

- `ctor.arrow` and `ctor.core` are rows with `semantics`, `functorialAction` and three comparisons (`Sem/ConstructorRegistration.lean:86-99`; `Reg/Entry.lean:448-466`). `ConstructorEntry` has no field for a role.
- The validator of lean-categories finds the core row by `semantics == CasCatalogue.Constructors.core` (`Reg/Semantic.lean:2797-2815`). The kernel uses the same test for both rows (`CasCompiler/SourceMethod.lean`, `SourceConstruction.lean` at `fc7fdf8`) and applies `CategoryTheory.Arrow.mk` by name.
- No row declares $\operatorname{Mor}(C) \cong \operatorname{Ob}(\operatorname{Arr} C)$, the functors $\mathrm{dom}, \mathrm{cod}$, or the inclusion $\operatorname{Core}(C) \to C$ for the constructors. Search: `Arrow.mk`, `Arrow.leftFunc`, `Arrow.rightFunc`, `Core.inclusion` in `Catalogue/`; the hits are bodies of individual functors.
- #53 §16, question 2, asks if `Core`, `Disc`, `Elements` and `Arr` need dedicated forms. #54 owns typed constructors. Neither states this requirement.

**Mathematical requirement.** The objects of $\operatorname{Arr}(C)$ are the morphisms of $C$, with $\mathrm{dom}, \mathrm{cod} : \operatorname{Arr}(C) \to C$ (Mac Lane, *CWM*, II.4; Mathlib `Arrow`, `Arrow.leftFunc`, `Arrow.rightFunc`). The morphisms of $\operatorname{Core}(C)$ are the isomorphisms of $C$, with the inclusion $\operatorname{Core}(C) \to C$ (Mathlib `Core`, `Core.inclusion`). These data, natural in $C$, identify the two constructors.

**Issue: new (N7a).** Draft title: *The universal data of the arrow and core constructors*

```text
For a category C, the objects of Arr(C) are the morphisms of C, with the functors dom, cod : Arr(C) → C. The morphisms of Core(C) are the isomorphisms of C, with the inclusion Core(C) → C. A method on morphisms is a functor on Arr(C); an isomorphism invariant is a functor on Core(C).
At main (443fba9) the rows `ctor.arrow` and `ctor.core` declare the category and its action on functors, with the comparisons for identity and composition.
The bijection Mor(C) ≅ Ob(Arr C), the functors dom and cod, the inclusion of the core and the bijection Iso_C(X, Y) ≅ Hom_{Core C}(X, Y) are not declared for the constructors. The registry validator finds the core row by the name of its semantics declaration.
Expected:
- these four data are declared for the two constructors, with their naturality in C;
- a constructor row states that it is the arrow constructor or the core constructor by these data, and a consumer needs no declaration name to find it;
- the same question is settled for the other registered constructors (slice, coslice, elements, subobjects, functor category): which universal data identify each.
Sources: Mac Lane, CWM II.4; Mathlib `CategoryTheory.Arrow`, `CategoryTheory.Core`. Related: #53 §16 question 2; #54.
```

### 7b. The refinement witness and proof procedure of a classifier refinement

**Consumer.** T057. **Status: absent.**

Facts:

- `Classifier.Holds c X` is the inhabitation of the fibre over $X$; `holds_ofProperty` relates it to the property (`Catalogue/Holds.lean:31-41`).
- A property row has `id`, `name`, `classifier`, `receiver` (`Reg/Entry.lean:431-436`). A classifier row has `id`, `declaration`, `host`, `realization` (`:497-502`). Five property rows exist: `is_finite`, `is_commutative`, `is_abelian`, `is_lattice`, `is_alternating`.
- `refinementRealization` is a field of a category row, the pullback witness of a refined category (`Reg/Entry.lean:475-476`). It is not a refinement of an object.
- `ObjectEntry.refines` declares a named object as another with more structure (`Reg/Entry.lean:128-137`). It does not refine an arbitrary object from a proof.
- No declaration sends an object and a proof of `Holds` to the refined object with its comparison. No proof procedure for `Holds` is registered. Search: `refine`, `ofHolds`, `liftObject`, `refinedObject` in `CategoryTheory/OneCat/`, `Catalogue/Lift.lean`, `Catalogue/Realization.lean`; `evidence` and `evaluation` fields in all rows. `Sem/Foundation/Finiteness.lean:19` names `CasCatalogue.refine`. A search for `def refine` in all Lean files found `CategoryExpr.refine` and `refine'` only (`Catalogue/Syntax.lean:270`, `:359`); they form the expression of a refined category, not a refined object.

**Mathematical requirement.** For a property classifier $p : A \to C$ and an object $X$ with $p^{-1}(X)$ inhabited, the object $\tilde{X}$ of $A$ with $p(\tilde{X}) = X$, unique up to unique isomorphism (Mathlib `ObjectProperty.FullSubcategory`). For a structure classifier, inhabitation selects no point of the fibre. Each registered property needs the procedure that settles it for a closed object.

**Issue: new (N7b).** Draft title: *The refinement of an object along a classifier, and the proof procedures of the registered properties*

```text
A classifier p : A → C states a property or a structure. An object X of C has it when the fibre of p over X is inhabited (`Classifier.Holds`, FOUNDATIONS Def. 46.4).
For a property classifier a proof gives the object X̃ of A with p(X̃) = X, unique up to unique isomorphism. Several classifiers can hold of one object.
At main (443fba9) the five property rows name a classifier and nothing else. No declaration sends (X, a proof of Holds) to X̃ with its comparison p(X̃) ≅ X. No registered procedure establishes `Holds` for a closed object, as `ObjectEntry.evidence` does for an admission.
Expected:
- for each registered property classifier, the refinement of an object from a proof, with its comparison to the object and its uniqueness;
- for a structure classifier, the statement that inhabitation of the fibre selects no structure, so that a basis, an orientation or an enumeration is never obtained from an existence proof;
- two refinements of one object along two classifiers are both available, with the comparison between their images;
- the procedure that proves or refutes each registered property (`is_finite`, `is_commutative`, `is_abelian`, `is_lattice`, `is_alternating`) for a closed object, and leaves it unsettled otherwise.
Sources: Mathlib `ObjectProperty.FullSubcategory`, `Functor.Fiber`; `Classifier.holds_ofProperty`.
```

### 7c. Written forms of the objects `X ∖ 0`, `Spec A`, `X in C/Y`

**Consumers.** T036, T057. **Status: partly present.**

Facts:

- `ObjectEntry.notations` exists (`Reg/Entry.lean:173-176`). Four rows use it (`NamedRings.lean:110`, `:132`; `Sem/Foundation/Objects.lean:62`, `:75`).
- Three objects have a composed name and no notation: `obj.sets.nonzero_polynomials` named `Poly∖0` (`Sem/Algebra/Polynomials.lean:311-316`), `obj.schemes_over.spec_polynomials` named `Spec Poly`, `obj.schemes_over.spec_mv_polynomials` named `Spec MvPoly` (`Sem/Algebra/Schemes.lean:127-135`). The family category is named `Schemes/` (`:117-121`).
- No `Spec` functor is registered, and the three scheme rows have no `functorPresentation`. `ctor.slice` has no object-level constructor row.

**Mathematical requirement.** $\operatorname{Spec} : \mathbf{CRing}^{\mathrm{op}} \to \mathbf{Sch}$ and its relative form $\mathbf{Alg}_K^{\mathrm{op}} \to \mathbf{Sch}/\operatorname{Spec} K$ (Hartshorne II.2; Mathlib `AlgebraicGeometry.Scheme.Spec`). The nonzero elements $X \setminus \{0\}$ of an object with a zero, as a subobject. An object of a slice $C/Y$ from an object $X$ and a morphism $X \to Y$ (Mathlib `Over.mk`).

**Issue: new (N7c).** #184 covers morphisms and methods, not objects. Draft title: *Spec, complements of zero and objects of a slice as registered constructions with their written forms*

```text
At main (443fba9) three objects are named by a composed string: `Poly∖0` (nonzero polynomials), `Spec Poly` and `Spec MvPoly` (spectra over Spec K). The family of schemes over a ring is named `Schemes/`.
Spec is not a registered functor. The spectra are not presented as its values. The field for written forms of an object is used by four rows.
Expected:
- Spec : CRing^op → Sch and its relative form Alg_K^op → Sch/Spec K are registered functors; each registered spectrum is presented as a value of the functor, with its identification;
- the nonzero elements X ∖ {0} of an object with a zero are one construction, with its inclusion and its admission; `Poly∖0` is a value of it;
- an object of a slice C/Y is formed from an object X and a morphism X → Y; the object and its structure map are both retained;
- each written form (`X ∖ 0`, `Spec A`, `X in C/Y`) is declared on the construction that it denotes.
Sources: Hartshorne, Algebraic Geometry, II.2; Mathlib `AlgebraicGeometry.Scheme.Spec`, `Spec.map`, `Over.mk`.
```

### 7d. The ellipsis definition and published subtraction

**Consumer.** T068. **Status: absent.**

Facts:

- No declaration defines a progression or an ellipsis. Search: `ellipsis`, `progression`, `arithmeticProgression` in the whole snapshot; the one hit is prose in `Lattices/Valued/AETHypotheses.lean:362`.
- No binary subtraction is registered. `op.rings.neg` is the only row named `-` (`NamedRings.lean:157-159`). Search: operation and morphism rows named `-`, `−`, `sub*`, `minus`, `difference`.
- The kernel computes the difference of the first two numerals in host `Nat` arithmetic (`CasCompiler/ReadSubsetNotation.lean` at `fc7fdf8`).

**Mathematical requirement.** The arithmetic progression $\{a + k d \mid k \in \mathbb{N}\}$ in an additive monoid, and its finite sections. The difference $d = a_1 - a_0$ exists and is unique in an additive group, and in $\mathbb{N}$ when $a_0 \le a_1$ (Mathlib `Sub`, `Nat.sub`, ordered subtraction). An ellipsis $\{a_0, a_1, \ldots\}$ denotes the one progression that begins with the written terms.

**Issue: new (N7d).** Draft title: *Arithmetic progressions, the meaning of an ellipsis, and subtraction*

```text
The written set {a₀, a₁, …} denotes the arithmetic progression {a₀ + k·d | k ∈ ℕ}, with d the difference of the first two terms. {a₀, a₁, …, aₙ} denotes its finite part.
The difference d = a₁ − a₀ exists and is unique in an additive group, and in ℕ when a₀ ≤ a₁.
At main (443fba9) no declaration defines a progression or an ellipsis. No binary subtraction is registered; the only row named `-` is the negation of a ring.
Expected:
- the progression with first term a and difference d in an additive monoid, as the image of ℕ under k ↦ a + k·d, with its finite sections;
- the statement that written terms begin exactly one progression, with the condition (constant difference) as a proposition and the procedure that settles it;
- binary subtraction at additive groups, a − b = a + (−b), and the subtraction of ℕ with its domain a ≥ b;
- the map k ↦ a + k·d as the selected enumeration of the progression, so that an enumeration of its elements is not a choice.
Sources: Mathlib `Sub`, `AddGroup`, `Nat.sub`, `Set.range`.
```

### 7e. A three-valued decision

**Consumers.** T113, T027. **Status: not an upstream input.**

Facts: the constitution says that an `unknown` outcome "is an inability to establish the requested result, not a third mathematical truth value" (`.specify/memory/constitution.md:447-449`; FR-029). Issue #28 of lean-categories rules that `unknown` is resolver output and is never a value of a classifier fibre. The truth values are `obj.sets.truth_values`, $\Omega = \mathrm{Prop}$ (`PowerSets.lean:160`, `:372-374`).

Inference: the three-valued reply is a shape of the reply in the contract and the kernel. It needs no declaration of lean-categories. No issue.

### 7f. Equality as a published predicate

**Consumer.** T113. **Status: present.**

Facts: `mor.sets.equality` is $X \times X \to \Omega$ for every set $X$ (`PowerSets.lean:176-177`, row `:464-466`). It is in the published catalogue. `meth.set_eq` compares subsets as objects of $\operatorname{Sub}(\mathbf{Set})$ (`Subsets.lean:207-209`). No other row is named `=`. Search: rows named `=`, `==`, `eq*`, `set_eq`.

Inference: the family at sets covers elements of $\mathcal{P}X$, of $Y^X$ and of the underlying set of a structured object, so the cases of T113 (scalars, subsets, maps) have a published predicate. The procedure that closes a statement between literals is #183.

### 7g. Evidence procedures of admissions

**Consumers.** T021, T059. **Status: present.**

Facts: 15 object rows have an `admission`, and each has an `evidence` procedure (list from all `admission := some` rows). `ObjectEntry.evidence` is the only proof search for membership in the domain (`Reg/Entry.lean:203-210`).

Not checked: whether each procedure settles its goal on the term as read. That needs a build, which this task excludes.

### 7h. Agreement over a route family that is not finite

**Consumer.** T056. **Status: absent for one cycle.**

Facts: `fun.sets.whole_subset` and `fun.subobjects_sets.domain` are both structural (`Subsets.lean:178-191`). They form the one cycle of the structural functor graph at `3f8aedf` (computed from `extension-ports.json`; edges induced by constructors not included). No cell names either functor, and no theorem relates `wholeSubset ⋙ subsetCarrier` to the identity. Search: cell rows; `Foundation/Subsets.lean`.

Inference: this cycle makes the route family from a set to sets infinite, and the "supplied uniform comparison" of the T056 row is this comparison. Families induced by `Arr` and `Core` have the comparisons of `ctor.arrow` and `ctor.core`.

**Mathematical requirement.** The natural isomorphism $\mathrm{dom} \circ \mathrm{whole} \cong 1_{\mathbf{Set}}$, with identity components: the whole subset of $X$ is $\mathrm{id}_X$, and its domain is $X$.

**Issue: new (N7h).** Draft title: *The domain of the whole subset of a set is that set*

```text
`fun.sets.whole_subset` sends a set X to X as its own largest subset. `fun.subobjects_sets.domain` sends a subset to the set that it is. Both are structural functors.
Their composite Sets → Sets sends X to the domain of the identity of X, which is X.
At main (443fba9) no cell compares this composite with the identity functor. The structural routes from a set that pass n times through Subobjects(Sets) are then infinitely many, with no declared agreement.
Expected:
- the natural isomorphism dom ∘ whole ≅ 1 on Sets, with identity components, as an invertible comparison of the two routes;
- the statement of what the other composite, whole ∘ dom on Subobjects(Sets), is: it sends a subset A ⊆ X to A ⊆ A and is not the identity;
- the same comparison for any other pair of structural functors whose composite is an endofunctor.
Sources: `LeanCategories/Foundation/Subsets.lean` (`wholeSubset`, `subsetCarrier`); Mathlib `Subobject`, `MonoOver`.
```

### 7i. Own-ring evaluation of a polynomial

**Consumer.** T036. **Status: partly present.**

Facts: the registered application of `obj.sets.polynomials` is `evaluation (R : CommRingCat) (A : Under R)` (`Polynomials.lean:67-69`). `ownEvaluation`, `evaluationAlong` and the theorem `evaluation_own : evaluation R (Under.mk (𝟙 R)) = ownEvaluation R` are declared and are in no row (`:71-93`). `obj.algebras.scalar_extension` is `Under.mk f` for a ring map $f$ (`Sem/Algebra/Algebras.lean:86-88`).

Inference: the argument object of the application is in the registry. The absent declaration is the rule that reads $p(a)$ for $a \in R$ at the algebra $(R, \mathrm{id}_R)$. This is a reading of one written term as a related one, the subject of #188, which lists three other readings. Add it there as a fourth case.

## Files read and files searched

| Read in full | Read in part | Searched |
| --- | --- | --- |
| TASKS lines 1-225 and 399-466; plan lines 242-283 | TASKS lines 472, 473, 482, 552, 608 | — |
| `Reg/Entry.lean`, `Reg/Computation.lean`, `Reg/operation-agreement.md`, `Catalogue/Id.lean`, `Catalogue.lean`, `Catalogue/Holds.lean`, `Orders.lean` | `Reg/Semantic.lean` (lines 1745-1800, 2036-2062, 2440-2560, 2790-2830) | all 1358 Lean files, by the terms named in each section |
| `Sem/Algebra/`: `ComputationDerivations`, `MonoidOperations`, `AdditiveOperations`, `Ports`, `PortComparison`, `NamedRings`, `MonoidOperationAgreement`, `Catalogue`, `Catalogue/Magmas`, `Catalogue/Rings` | `Semirings`, `CommutativeMonoids`, `FiniteSums`, `Polynomials`, `Schemes`, `Algebras`, `CatalogueRegistration`, three test files | all 676 registry rows, parsed to a table |
| `Sem/Foundation/`: `PowerSets`, `Subsets`, `CatalogueRegistration`; `Sem/Modules/LinearMaps`; `Sem/ConstructorCatalogue` | `Maps`, `FiniteSubsets`, `Finiteness`, `WellOrderedSetsRegistration`; `Foundation/Sets.lean`, `Foundation/WellOrderedSets.lean`; `Bilinear/Valued/CatalogueRegistration`, `ChangeValueLifts`; `Catalogue/Constructors.lean` | `AGENTS.md`, `FOUNDATIONS.md`, `INTENT.md`, `README.md`, `TODO.md` for ownership and order terms |
| Contract `api/README.md`; issues #182 to #189 with comments | `AGENTS.md` lines 520-631; `FOUNDATIONS.md` lines 761-830; issue #53 §5, §9, §12, §16; heads of #28, #30, #31, #41, #54; passages of #56 | both catalogue JSON files, every entry; 150 issue bodies |
| — | kernel at `fc7fdf8`: `Lower`, `SourceMethod`, `SourceConstruction`, `SourceRing`, `SourceNumeral`, `ReadSubsetNotation`, `SourceRoutes`, `PublishedPorts` | kernel `CasCompiler/`, `CasRuntime/` by `git grep` |
