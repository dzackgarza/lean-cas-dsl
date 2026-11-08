# Independent mathematical source notes

These notes record the sources of the reconstructed expectations before any execution. They
do not certify a mathematical release or a computation. The author read the cited declarations
and their proof terms in the assigned mathematical checkout; the author did not rebuild them.

Mathematical paths below are relative to `lean-categories`. The exact checkout revision and
file SHA-256 values are in [provenance.json](provenance.json). The checked source checkout
contains both assigned ancestor commits `8533af0599d37515cea581e45a65be1f6cc21224` and
`03a6cc06c1aeca70001d03747928e582a3b98378`. This ancestry check records source provenance,
not acceptance of either revision. The parent assignment supplies the mathematical scope;
the proofs below independently establish its numerical and formula expectations.

## M01: selected finite linear orders

Path: `LeanCategories/Catalogue/Semantics/Foundation/FiniteOrders.lean`.
Namespace: `CasCatalogue.Foundation.FiniteOrders`.

- `ordinary`, `reverse`, `ordinaryCarrier`, and `reverseCarrier` retain the two selected
  orders and the identity set comparisons with `Fin n`.
- `ordinary_carrier_card n` and `reverse_carrier_card n` prove the cardinal equalities
  directly from `Cardinal.mk (Fin n) = n`; specialize to `n=5`.
- `ordinary_five_zero_le_one`, `reverse_five_not_zero_le_one`, and
  `five_relations_distinct` prove that the equal finite cardinalities do not equate the
  selected orders.

`Foundation/PowerSets.lean` owns `linearOrdersForget` and registers
`fun.linear_orders.forget`; `[M13]` owns the inherited cardinality operation.

## M02: unordered two-element subsets

Path: `LeanCategories/Catalogue/Semantics/Foundation/TwoSubsets.lean`.
Namespace: `CasCatalogue.Foundation.TwoSubsets`.

`twoSubsets X` is Mathlib's `Set.powersetCard X 2`. The theorem `card` cites
`Set.powersetCard.card`; `fin_five_card` proves the exact value ten and
`fin_five_cardinal` proves the cardinal-valued version used by the old cardinality operation.
The independent arithmetic is `choose(5,2)=5*4/2=10`.

`inclusion`, `inclusion_mono`, `map`, `map_extent`, and `onCore` supply the actual inclusion,
direct-image action, and complete identity/composition laws. `singleton_not_member` proves
the repeated-element control. The registered object presentation and `meth.two_subsets`
both cite the same functor; the source is `Core(Sets)`, not all set morphisms.

## M03: cyclic quotient automorphisms

Path: `LeanCategories/Catalogue/Semantics/Algebra/CyclicQuotients.lean`.
Namespace: `CasCatalogue.Algebra.CyclicQuotients`.

`cyclicQuotient`, `quotientMap`, `generator`, `residueComparison`, and
`residueComparison_quotient` fix the quotient group, its class-of-one generator, and the
actual comparison with the old residue group. The comparison is supplied by Mathlib's
`Int.quotientZMultiplesNatEquivZMod`.

`quotientAutUnits` is the multiplicative equivalence between categorical group
automorphisms and `(ZMod n)^x`, using `ZMod.AddAutEquivUnits`.
`aut_five_card` and `aut_five_cardinal` prove the value four using
`ZMod.card_units_eq_totient`. Thus the count is a group-automorphism count, not the
permutation count of an underlying five-element set.

`byUnitMorphism`, `byUnit_coordinate`, `byUnit_mul`, and `byUnit_inv` retain complete
automorphisms and their inherited group operations. `unitTwo` has coefficient/inverse pair
`(2,3)` and `unitThree` has `(3,2)`; both inverse equations are checked in their definitions.
`unitTwo_inv`, `byUnit_two_inverse`, and `byUnit_two_order` prove inversion and order four.

The additional point observations follow directly from the universal coordinate theorem:
`2*1=2`, `2*3=6=1 (mod 5)`, and `3*2=6=1 (mod 5)`.
Both complete inverse equations follow because these values inhabit the actual `Aut` group.

## M04: genuine conjugation by a core isomorphism

Path: `LeanCategories/Catalogue/Semantics/Algebra/Automorphisms.lean`.
Namespace: `CasCatalogue.Algebra.Automorphisms`.

`automorphisms C` is the existing functor `Core C -> GrpCat`. Its map is
`Aut.autMulEquivOfIso e.iso`, with action
`e.iso.inv ≫ v.hom ≫ e.iso.hom`. Its `map_id` and `map_comp` proof fields establish the
functorial equations. `automorphismsConstruction` is the generic direct construction
registered as `con.automorphisms`, surface name `Aut`.

At the `residueComparison 5` of `[M03]`, this gives exactly the complete conjugation
`e o v o e^(-1)` and sends the selected quotient doubling/tripling maps to the corresponding
residue maps. This follows from the definition of `quotientAutUnits` and
`byUnit_coordinate`, rather than from a computed table of automorphisms.

The caution concerning self-conjugations is mathematical: `[M03]` identifies this
automorphism group with the unit group of a commutative ring, so that group is commutative.
It does not remove the selected conjugation from the question.

## M05: the exact square bound and finite refinement

Path: `LeanCategories/Catalogue/Semantics/Foundation/IntegerSquareBounds.lean`.
Namespace: `CasCatalogue.Foundation.IntegerSquareBounds`.

`squareBound_eq_Icc` proves the interval equation from `sq_le_sq` and `abs_le`.
`squareBound_three` identifies radius three with the actual bound nine;
`squareBound_three_members` proves the complete seven-element list;
`extent_three_card` proves `Nat.card=7` using `Int.card_Icc`.
`extent_finite` supplies finiteness, so this is also the finite cardinal seven of `[M13]`.

`inclusion`, `finiteExtent`, `finiteIdentification`, `finiteHolds`,
`admittedSubset`, and `admission_retains_subset` fix the original subtype, finite
classifier/refinement, and finite-subset admission equation. `integers_not_finiteHolds`
proves the negative for all integers. No classifier outcome comes from an external answer.

## M06: the prime-residue field and distinct operations

Path: `LeanCategories/Catalogue/Semantics/Algebra/PrimeResidueFields.lean`.
Namespace: `CasCatalogue.Algebra.PrimeResidueFields`.

`primeResidues p hp` uses the actual proof `hp : p.Prime` to obtain Mathlib's field
structure on `ZMod p`. `underlying_ring` proves that the forgotten ring is the already
named residue ring, with no new multiplication or addition.

`five_multiplicative_cardinality`, `five_additive_cardinality`, and
`five_operations_separate` prove both five-element counts and the conjunction
`1+1=2`, `1*1=1`, and `1+1 != 1*1` in `ZMod 5`.
`carrier_comparison_apply` and `carrier_routes_map` give the component's complete point
action and both complete map actions.

The prime proof at five occurs as `by decide` in these theorem statements. The proposal's
`proof(by decide)` is formal input checked against that actual dependent parameter; it
is not an output assertion or an admission based on a runtime Boolean.

## M07: the existing carrier comparison and its exact registered routes

Paths:

- `LeanCategories/Catalogue/Semantics/Algebra/Ports.lean`;
- `LeanCategories/Catalogue/Semantics/Algebra/PortComparison.lean`;
- `LeanCategories/Algebra/Concrete/RingCarrierComparison.lean`.

`Ports.lean` owns the edge identifiers. `PortComparison.lean` registers precisely
`cmp.rings.carrier`, with the ordered routes reproduced in RX-05, declared invertible,
and the multiplicative route on its left/source side.

`LeanCategories.Algebra.ringCarrierComparison` is the actual natural isomorphism
`ringCarrierMultiplicative ~= ringCarrierAdditive`, constructed by
`NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)`.
Thus both component directions are the identity on each residue, and naturality holds
for every ring homomorphism with its complete original function. This mathematical
isomorphism only compares the routes after all operations have been forgotten.

The missing-cell and reordered-registration requirements are independently supplied
language obligations, not new theorems that an omitted cell exists. Their public authority
is `[P02]`; the scope is also explicit in the supplied integration note `[I01]`.

## M08: scalar restriction along the selected coefficient morphism

Path: `LeanCategories/Catalogue/Semantics/Modules/IntegerResidueModules.lean`.
Namespace: `CasCatalogue.Modules.IntegerResidueModules`.

`restrictedRegularModule R S q` is defined by the existing module-family reindexing on
the existing regular module. `integerResidueModule` specializes it to integer residues.
`reindex_selected_quotient` and `quotient_is_integer_coefficients` identify the actual
reindexing and the existing coefficient morphism exactly.

The original morphism is independently declared in
`Algebra/NamedCommutativeRings.lean`, namespace
`CasCatalogue.Algebra.NamedCommutativeRings`, as
`integerCoefficients R = CommRingCat.ofHom (Int.castRingHom R)`.
Its value at seven in `ZMod 5` is two by integer residue arithmetic.

`five_regular_dimension`, `five_cardinality`, and `action_formula` prove the original
dimension, restricted cardinality, and complete scalar action. `five_actions` proves
the three selected observations. Their arithmetic is independently transparent:
`2*3=6=1`, `5*1=0`, and `(-1)*2=-2=3` modulo five.

`five_cartesian_base` and `five_cartesian_carrier` retain the actual base morphism and
identity additive function of the cartesian arrow. `reindex_map_apply` proves the full
map action. `reindex_double_three` is exactly the fixed true question of RX-10, including
the selected quotient, regular module, full linear map, argument three and answer one.

## M09: public F9 presentations, generators and maps

Path: `LeanCategories/Catalogue/Semantics/Algebra/PolynomialPresentations.lean`.
Namespace: `CasCatalogue.Algebra.PolynomialPresentations`.

`first`, `second`, `firstSet`, `secondSet`, `firstGenerator`, `secondGenerator`,
`firstConstants`, and `secondConstants` retain the selected quotient presentations and
coefficient maps. `quadraticComparison` is the registered `cmp.f9.translation`.

`quadraticComparison_root`, `quadraticComparison_inv_root`,
`quadraticComparison_generator`, `quadraticComparison_inv_generator`,
`quadraticComparison_constants`, and `quadraticComparison_inv_constants` prove the
complete prescribed root and coefficient actions. The inverse equations come from this
actual isomorphism. No expected value is taken from the module's evaluation procedure.

## M10: independent F9 relations and arithmetic derivation

Path: `LeanCategories/Algebra/Concrete/PolynomialPresentation.lean`.
Namespace: `LeanCategories.Algebra.PolynomialPresentation`.

`firstPolynomial = X^2+1` and `secondPolynomial = X^2+X+2` are defined over `ZMod 3`.
`translate`, `translated_first`, `translatedComparison`, and `comparison` construct
the quotient isomorphism from Mathlib's polynomial translation and quotient universal
property. `comparison_root`, `comparison_symm_root`, and `comparison_root_ne` prove
the nonidentity prescribed generator actions. `first_irreducible` and
`second_irreducible` prove that both selected quadratics are irreducible.

The successive numerical expressions in RX-07 are derived independently from these
quotient relations and the ring-isomorphism laws:

1. `e(x+1)=(y+2)+1=y` in characteristic three.
2. In the target quotient, `y^2+y+2=0`, so `y^2=-y-2=2y+1`.
3. `e^(-1)(2y+1)=2(x-2)+1=2x-3=2x`.
4. For every coefficient `c`, preservation of sums, products and coefficients gives
   `e(x+i_A(c))=y+2+i_B(c)` and
   `e^(-1)((e(x+i_A(c)))^2)=(x+i_A(c))^2`.

These are calculations in the selected quotient rings, not values observed from a transport
implementation. The universal equations establish the whole-map expectations, and
specializing `c=1` gives the stated samples.

## M11: ordinary projection, complete kernel and restricted form

Path: `LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/ModuleKernelRestriction.lean`.
Namespace: `CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction` and its
subnamespace `RationalProjection`.

`ordinaryKernelRestriction` and `ordinaryKernelInclusion` compose the actual ordinary
module kernel with the old arbitrary-submodule form restriction. Their parameter order is
the scalar ring, value module, formed source, ordinary target module and ordinary arrow.
`ordinaryKernelInclusion_condition` proves the full zero-composite equation.

`diagonalSource`, `projection`, `projection_apply`, and `diagonalSource_pairing` fix the
selected row and form. `mem_kernel`, `kernelCoordinates`, and `kernel_dimension` give the
entire kernel and the actual coordinate equivalence. `inclusion_coordinates`,
`restricted_pairing`, `restricted_pairing_one`, and `projection_inclusion` prove all
required inclusion and form observations.

The complete ordinary universal property in RX-08 follows directly from these sources:
if `p o h=0`, `mem_kernel` says that the first coordinate of every `h(t)` is zero.
`kernelCoordinates` then identifies `h(t)` with its second coordinate. The map to that
coordinate is linear, gives the required factor, and is unique since the coordinate
equivalence and the subtype inclusion are injective. This is an explicit derivation from
the complete maps; no new upstream interface is asserted to have been registered.

The existing selected pairing observation is already public mathematics:
`Modules/Bilinear/Valued/CatalogueRegistration.lean` declares
`CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.pairing`
at ordered parameters `R : CommRingCat`, `W : ModuleCat R`, and `L : BilinModuleCat R W`.
It is the entire map `L.carrier x L.carrier -> W`, `(x,y) |-> L.pairing x y`, registered
as `mor.sets.bilin_module_pairing`, surface name `pairing`.
`Modules/Bilinear/Valued/Kernels.lean` additionally registers the old `restricted_pairing`
and proves `restrictedPairing_apply`. A new pairing operation is not required by this proposal.

`projection_not_formed B` quantifies over every target bilinear form `B`. Its proof
applies the formed-arrow equation at `(0,1)`, obtaining the impossible equality `0=3`.
It therefore justifies the full universal negative, not merely rejection for one target form.

## M12: the actual nonsquare row operation

Path: `LeanCategories/Catalogue/Semantics/Algebra/RectangularLinearAlgebra.lean`.
Namespace: `CasCatalogue.Algebra.RectangularLinearAlgebra`.

`rectangularMatrices`, `rectangularLinearMap`, and `rectangularLinearMap_apply` retain
independent row/column dimensions and the complete `Matrix.mulVec` action.
`rowLinearMap` has the regular scalar module as codomain and `rowLinearMap_apply`
proves its full row-sum equation. The selected `1 x 2` row specializes to `(a,b)|->a`.
`square_specialization` identifies the square case with the old owner without changing
the independent dimensions of the general construction.

## M13: inherited cardinality and finite cardinal literals

Path: `LeanCategories/Catalogue/Semantics/Foundation/Cardinality.lean`.
Namespace: `CasCatalogue.Foundation.Cardinality`.

`setsCardinality` is the existing `LeanCategories.Foundation.cardinality` on `Core(Sets)`.
It is registered once as `fun.sets.cardinality`, method `meth.cardinality`, owner `Sets`.
`CardinalLiteral.denote` interprets a natural numeral as its finite cardinal;
`CardinalLiteral.denote_inj` proves equality of these denotations is equality of literals.

The finite `Nat.card` theorems in `[M05]`, `[M06]` and `[M08]`, together with their actual
finite carriers, yield the corresponding finite-cardinal observations. `[M01]`, `[M02]`
and `[M03]` also supply the cardinal-valued equalities directly.

## M14: the successor series and the inadmissible constant family

Path: `LeanCategories/Catalogue/Semantics/Algebra/SuccessorSeries.lean`.
Namespace: `CasCatalogue.Algebra.SuccessorSeries`.

`successorTerms` is the entire morphism `n |-> C(n+1) X^n`, with no truncation parameter.
`successorTerms_summable` invokes the old `Series.summable_of_X_pow_dvd` theorem.
`successorTerms_admission` proves that the admitted value retains this same function.
`successorTerms_sum` proves equality with `PowerSeries.mk (n |-> n+1)` for every
selected commutative coefficient ring. `integer_degree_three` proves four over the integers.

The other fixed coefficient observations are direct substitutions in the proved complete
coefficient formula: `0+1=1`, `1+1=2`, and `5+1=6`. The individual-term coefficient
formula is the defining coefficient law of `C(n+1) X^n`, stated in the declaration's
mathematical documentation; it is not an inference from a returned finite polynomial.

`integer_constant_one_not_summable` uses degree-zero coefficients and Mathlib's
`summable_const_iff` in the discrete integer topology. `no_constant_one_admission`
then excludes any admitted-family value having that complete constant-one function.

## M15: the existing admitted-family and power-series binder

Path: `LeanCategories/Catalogue/Semantics/Algebra/Series.lean`.
Namespace: `CasCatalogue.Algebra.Series`.

`SummableFamily Y N` contains the complete function `N -> Y` and the proposition
`Summable toFun`. `admit` forms this actual value from its function and proof.
`powerSeriesTAdic R` selects the `(X)`-adic topology, and
`powerSeriesTAdicIdentification` retains the underlying series set.
`powerSeriesSum`, `powerSeriesSum_eq`, and `powerSeriesSum_C_mul_X_pow` identify the
old binder with the genuine series sum and give the complete coefficient reconstruction.

These inputs establish why replacing the family by a finite prefix or replacing admission
by an external truth flag would change the question.

## M16a: the genuine formed-arrow and the two successive lifted objects

Path: `LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/DegeneratePlaneLifts.lean`.
Namespace: `CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts`.

`source_pairing`, `target_pairing`, `underlyingMap_apply`, and the proof field of
`formedMap` fix the complete forms and the genuine arrow `(a,b)|->(a+b,0)`.
`kernelInclusion_apply`, `kernel_condition`, `kernel_range`, and `kernel_universal`
prove the factor-two model is the entire module kernel with its universal property.

`firstLift`, `firstObject`, `firstInclusion`, `alpha`, and `beta` are the actual first
outputs. `alpha_value`, `beta_value`, `alpha_four`, `first_defining_map`,
`first_pairing`, both `first_inverse_*` theorems, and `first_factorization` prove all
first-stage equations.

`pairedSource_pairing` and `pairedSource_first` retain the actual extra dot product and
the selected `fst` map. `compositeLift` is literally `secondLift.comp firstLift`.
`final_object_is_successive` and `final_inclusion_is_second` expose the first inclusion
as the second stage's input. `final_alpha_value`, `final_beta_value`, both
`final_inverse_*` theorems, `final_factorization`, `final_pairing`,
`final_pairing_one`, and `final_defining_map_three_halves` prove the full final equations
and fixed values.

The coefficient eight is independently visible from the dot product of the chosen
coordinates: `(2s)(2t)+(-2s)(-2t)=8st`. It does not replace the distinct coefficient
three in RX-08.

## M16b: the actual generic second lift

Path: `LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/ChangeValueLifts.lean`.
Namespace: `CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts`.

`pulledBack`, `pulledBack_pairing`, `pulledBackHom`, and `pulledBackIso` supply the
complete value-preserving pullback and identity carrier comparison. `changeValueMonoLift`
contains the full cartesian universal property, with the two factorization equations and
uniqueness for arbitrary compatible arrows. `changeValueMonoLiftComputation` supplies
the four complete callable fields. Its existing registration is
`lift.bilin_module.change_value_restriction`, on the actual change-value arrow action.

## M16c: both nonzero universal factorizations

Path: `LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/DegeneratePlaneFactorization.lean`.
Namespace: `CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization`.

`coneUnderlying_apply` and `baseMediator_apply` fix the complete, independently selected
matrix and row. `cone_base_factorization` proves their compatibility. The complete first
and final maps are `formedMediator` and `finalMediator`.

`formedMediator_factorization`, `formedMediator_comparison`, and
`formedMediator_unique` give the first equations and uniqueness.
`pairedConeSource` pulls both forms back along the actual cone, using `[M16b]`.
`finalMediator_factorization`, `finalMediator_comparison`, and `finalMediator_unique`
give the final equations and uniqueness with the retained final defining map.

`first_observation` and `second_observation` prove exactly the table in RX-LIFT:
at `(2,1)`, `3*2-2*1=4` and `4/2=2`; at `(1,3)`, `3-6=-3` and `-3/2`.
The complete pairing on the paired cone source follows from
`pulledBack_pairing`, `pairedSource_pairing`, and `coneUnderlying_apply`:
the first component is zero and the second is `2(3s-2t)(3u-2v)`.

## I01: supplied upstream integration note

Path: `Integration/IndependentScalarAndFormExtensions.md`.

This source fixes the selected parameters, complete registered identities, the actual
ring cell, the two separate form examples, the two-stage/factorization requirement, and
the scope of the missing-cell control. Its author-validation statements are not treated
as independent release acceptance. This reconstruction confirms its expected mathematical
values against the actual declarations and proofs cited above.

## Public requirement sources

| Label | Public source | Use in this proposal |
| --- | --- | --- |
| P01 | Root `lean-cas-dsl/SPEC.md`, including the supplied explicit-proof-parameters paragraph | Definitions, assertions, proof-valued arguments, selected generators, presentation transport, and limits of documented syntax |
| P02 | `lean-cas-dsl/AGENTS.md`; `CONTRIBUTING.md`, “Acceptance assertions”; `specs/architecture.md`, “Authors: one role per agent”, “Core invariants” and policy 3 | Role separation, permanence, ambiguity without precedence, failure stages and preservation of the full question |
| P03 | `lean-cas-dsl-leaf-contracts/api/README.md` and `api/wire-examples.md`, “Malformed cases and ownership” | Complete map/result/selected-parameter interfaces and host-held session ownership; no expected mathematical answer is drawn from protocol examples |
| P04 | The current explicit independent-acceptance assignment | The ten retained trial scopes, separate genuine lift, additive-only reconstruction status, and the six requested execution observations |
| P05 | `lean-cas-dsl-execution/SPEC.md`, supplied as public source snapshot `760ca888`, published document revision `88fce07f61a531553080fb1f3b337a9a0758f55c` | Registered construction application and map action, selected functor views, natural components, generalized application, lift fields and universal factor syntax; no other file from that checkout was inspected |
| P06 | Root `lean-cas-dsl/specs/leaf-registration.md`, “Running a fixed question with selected implementations”, supplied as authored snapshot `2f5736e` | Existing harness selection, exact report outcomes, complete-question/report boundary, actual execution requirement, and separate internal-fault/foreign-session engineering fixtures |

The public proof syntax was permitted to be read in the root checkout before its publication.
The additional action/lift syntax was subsequently supplied as [P05]. The provenance record
labels both sources; no claim is made that their combined bytes occur in the published worktree
base. Further public surface documentation may translate the fixed questions without changing
their mathematics or claiming identity with unavailable original assertion bytes.
