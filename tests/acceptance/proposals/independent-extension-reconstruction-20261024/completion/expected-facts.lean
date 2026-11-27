/-
Independent expected facts for the already fixed RX questions.

These examples consume only independently supplied mathematical declarations.
They introduce no definition, registry row, computational implementation, or
acceptance outcome. A proof of an expected fact does not perform the required
public-language computation. This source is not a permanent assertion inventory.
-/
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Foundation
open CasCatalogue.Algebra
open CasCatalogue.Modules
open CasCatalogue.Modules.Bilinear.Valued

-- The selected second-stage target is definitionally the original source.
-- Make the already proved monicity available at that exact displayed type.
local instance : Mono
    (show DegeneratePlaneLifts.firstObject ⟶
      (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).obj
        DegeneratePlaneLifts.pairedSource from DegeneratePlaneLifts.firstInclusion) :=
  DegeneratePlaneLifts.firstInclusion_mono

-- RX-01: cardinality forgets the order; the selected relations stay distinct.
example : Cardinal.mk (PowerSets.linearOrdersForget.toFunctor.obj
    (FiniteOrders.ordinary 5)) = 5 := FiniteOrders.ordinary_carrier_card 5

example : Cardinal.mk (PowerSets.linearOrdersForget.toFunctor.obj
    (FiniteOrders.reverse 5)) = 5 := FiniteOrders.reverse_carrier_card 5

example : (0 : PowerSets.orderCarrier (FiniteOrders.ordinary 5)) ≤ 1 :=
  FiniteOrders.ordinary_five_zero_le_one

example : ¬ (0 : PowerSets.orderCarrier (FiniteOrders.reverse 5)) ≤ 1 :=
  FiniteOrders.reverse_five_not_zero_le_one

-- RX-02: the complete bijection/embedding action is direct image.
example : Cardinal.mk (TwoSubsets.twoSubsets (Fin 5)) = 10 :=
  TwoSubsets.fin_five_cardinal

example {X Y : Type} (e : X ↪ Y) (s : TwoSubsets.twoSubsets X) :
    ((TwoSubsets.map e s : TwoSubsets.twoSubsets Y) : Set Y) = e '' (s : Set X) :=
  TwoSubsets.map_extent e s

example (x : Fin 5) : ({x} : Finset (Fin 5)) ∉ Set.powersetCard (Fin 5) 2 :=
  TwoSubsets.singleton_not_member (Fin 5) x

-- RX-03: Aut is in Groups, and the complete unit action remains selected.
example : Cardinal.mk (Aut (CyclicQuotients.cyclicQuotient 5)) = 4 :=
  CyclicQuotients.aut_five_cardinal

example : (CyclicQuotients.byUnit 5 CyclicQuotients.unitTwo)⁻¹ =
    CyclicQuotients.byUnit 5 CyclicQuotients.unitThree :=
  CyclicQuotients.byUnit_two_inverse

example : orderOf (CyclicQuotients.byUnit 5 CyclicQuotients.unitTwo) = 4 :=
  CyclicQuotients.byUnit_two_order

example (u : (ZMod 5)ˣ) (z : CyclicQuotients.cyclicQuotient 5) :
    @Multiplicative.toAdd (ZMod 5)
        ((CyclicQuotients.residueComparison 5).hom
          ((CyclicQuotients.byUnit 5 u).hom z)) =
      (u : ZMod 5) * @Multiplicative.toAdd (ZMod 5)
        ((CyclicQuotients.residueComparison 5).hom z) :=
  CyclicQuotients.byUnit_coordinate 5 u z

example (v : Aut (CyclicQuotients.cyclicQuotient 5)) :
    ((Aut.autMulEquivOfIso (CyclicQuotients.residueComparison 5)) v).hom =
      (CyclicQuotients.residueComparison 5).inv ≫ v.hom ≫
        (CyclicQuotients.residueComparison 5).hom := rfl

-- RX-04: exact predicate, original admission, and universal ambient negative.
example : IntegerSquareBounds.squareBound 3 = {n : ℤ | n ^ 2 ≤ 9} :=
  IntegerSquareBounds.squareBound_three

example : Nat.card (IntegerSquareBounds.extent 3) = 7 :=
  IntegerSquareBounds.extent_three_card

example : IntegerSquareBounds.admittedSubset 3 ≫ FiniteSubsets.inclusion ℤ =
    IntegerSquareBounds.subset 3 := IntegerSquareBounds.admission_retains_subset 3

example : ¬ CasCatalogue.Classifier.Holds
    LeanCategories.Foundation.Mathlib.finite Objects.integers :=
  IntegerSquareBounds.integers_not_finiteHolds

-- RX-05: whole carrier actions preserve the original ring map.
example {R S : RingCat} (f : R ⟶ S) (x : R) :
    LeanCategories.Algebra.ringCarrierMultiplicative.map f x = f.hom x ∧
      LeanCategories.Algebra.ringCarrierAdditive.map f x = f.hom x :=
  ⟨rfl, rfl⟩

example (z : ZMod 5) :
    (LeanCategories.Algebra.ringCarrierComparison.app
      ((forget₂ CommRingCat RingCat).obj
        (Fields.ring (PrimeResidueFields.primeResidues 5 (by decide))))).hom z = z :=
  PrimeResidueFields.carrier_comparison_apply 5 (by decide) z

example : (1 + 1 : ZMod 5) = 2 ∧ (1 * 1 : ZMod 5) = 1 ∧
    (1 + 1 : ZMod 5) ≠ (1 * 1 : ZMod 5) :=
  PrimeResidueFields.five_operations_separate

-- RX-06: the actual quotient map determines restriction, not carrier equality.
example (r : ℤ) (m : IntegerResidueModules.integerResidueModule 5) :
    ((IntegerResidueModules.integerResidueModule 5).smul r).hom m =
      (r : ZMod 5) * (show ZMod 5 from m) :=
  IntegerResidueModules.action_formula 5 r m

example (f : CatalogueRegistration.regularModule (RingCat.of (ZMod 5)) ⟶
    CatalogueRegistration.regularModule (RingCat.of (ZMod 5)))
    (m : IntegerResidueModules.integerResidueModule 5) :
    ((CatalogueRegistration.modulesFamilyRealization.reindex
      (RingCat.ofHom (Int.castRingHom (ZMod 5)))).map f).hom m = f.hom m :=
  IntegerResidueModules.reindex_map_apply 5 f m

-- RX-10: this exact question is reused under all six execution observations.
example :
    ((CatalogueRegistration.modulesFamilyRealization.reindex
      (RingCat.ofHom (Int.castRingHom (ZMod 5)))).map
      (ModuleCat.ofHom
        (X := CatalogueRegistration.regularModule (RingCat.of (ZMod 5)))
        (Y := CatalogueRegistration.regularModule (RingCat.of (ZMod 5)))
        ((2 : ZMod 5) • LinearMap.id))).hom (3 : ZMod 5) = (1 : ZMod 5) :=
  IntegerResidueModules.reindex_double_three

-- RX-07: the comparison is nonidentity and retains every coefficient.
example : PolynomialPresentations.quadraticComparison.hom
      (AdjoinRoot.root LeanCategories.Algebra.PolynomialPresentation.firstPolynomial) =
    AdjoinRoot.root LeanCategories.Algebra.PolynomialPresentation.secondPolynomial + 2 :=
  PolynomialPresentations.quadraticComparison_root

example (c : ZMod 3) :
    PolynomialPresentations.quadraticComparison.hom
      (PolynomialPresentations.firstConstants c) =
      PolynomialPresentations.secondConstants c :=
  PolynomialPresentations.quadraticComparison_constants c

example (c : ZMod 3) :
    PolynomialPresentations.quadraticComparison.inv
      (PolynomialPresentations.secondConstants c) =
      PolynomialPresentations.firstConstants c :=
  PolynomialPresentations.quadraticComparison_inv_constants c

-- RX-08: preserve the nonsquare projection, full restricted form, and every B.
example (x : Fin 2 → ℚ) :
    ModuleKernelRestriction.RationalProjection.projection.hom x = x 0 :=
  ModuleKernelRestriction.RationalProjection.projection_apply x

example (x : Fin 2 → ℚ) :
    x ∈ ModuleKernelRestriction.RationalProjection.projection.hom.ker ↔ x 0 = 0 :=
  ModuleKernelRestriction.RationalProjection.mem_kernel x

example (s t : ℚ) :
    ModuleKernelRestriction.RationalProjection.restricted.pairing
      (ModuleKernelRestriction.RationalProjection.kernelCoordinates s)
      (ModuleKernelRestriction.RationalProjection.kernelCoordinates t) = 3 * s * t :=
  ModuleKernelRestriction.RationalProjection.restricted_pairing s t

example (B : LinearMap.BilinMap ℚ ℚ ℚ) :
    ¬ ∃ f : ModuleKernelRestriction.RationalProjection.diagonalSource ⟶
        BilinModuleCat.ofBilinMap B,
      BilinModuleCat.underlyingMap f =
        ModuleKernelRestriction.RationalProjection.projection.hom :=
  ModuleKernelRestriction.RationalProjection.projection_not_formed B

-- RX-09: no finite prefix or alternative topology replaces the whole family.
section
attribute [local instance] Series.tAdic

example :
    Series.powerSeriesSum NamedCommutativeRings.integers ℕ
      ⟨(fun n => SuccessorSeries.successorTerms NamedCommutativeRings.integers n),
        SuccessorSeries.successorTerms_summable NamedCommutativeRings.integers⟩ =
      PowerSeries.mk (fun d => (d + 1 : ℤ)) :=
  SuccessorSeries.successorTerms_sum NamedCommutativeRings.integers

example (d : ℕ) :
    PowerSeries.coeff d (Series.powerSeriesSum NamedCommutativeRings.integers ℕ
      ⟨(fun n => SuccessorSeries.successorTerms NamedCommutativeRings.integers n),
        SuccessorSeries.successorTerms_summable NamedCommutativeRings.integers⟩) =
      (d + 1 : ℤ) := by
  rw [SuccessorSeries.successorTerms_sum, PowerSeries.coeff_mk]

example : ¬ Summable (fun _ : ℕ => (1 : PowerSeries ℤ)) :=
  SuccessorSeries.integer_constant_one_not_summable

example : ¬ ∃ F : Series.SummableFamily
      (Series.powerSeriesTAdic NamedCommutativeRings.integers) ℕ,
    F.toFun = (fun _ : ℕ => (1 : PowerSeries ℤ)) :=
  SuccessorSeries.no_constant_one_admission
end

-- RX-LIFT: both stages, original scaled coordinate, and complete factorizations.
example (s t : ℚ) :
    DegeneratePlaneLifts.firstObject.pairing
      (DegeneratePlaneLifts.beta.hom s) (DegeneratePlaneLifts.beta.hom t) = 0 :=
  DegeneratePlaneLifts.first_pairing s t

example (x : DegeneratePlaneLifts.firstObject.carrier) :
    DegeneratePlaneLifts.alpha.hom x = x.val 0 / 2 :=
  DegeneratePlaneLifts.alpha_value x

example : DegeneratePlaneLifts.finalObject =
    DegeneratePlaneLifts.secondLift.obj DegeneratePlaneLifts.pairedSource
      DegeneratePlaneLifts.firstInclusion :=
  DegeneratePlaneLifts.final_object_is_successive

example : DegeneratePlaneLifts.finalInclusion =
    DegeneratePlaneLifts.secondLift.hom DegeneratePlaneLifts.pairedSource
      DegeneratePlaneLifts.firstInclusion :=
  DegeneratePlaneLifts.final_inclusion_is_second

example (s t : ℚ) : DegeneratePlaneLifts.finalObject.pairing
    (DegeneratePlaneLifts.finalBeta.hom s) (DegeneratePlaneLifts.finalBeta.hom t) =
      (0, 8 * s * t) := DegeneratePlaneLifts.final_pairing s t

example : DegeneratePlaneFactorization.formedMediator ≫
    DegeneratePlaneLifts.firstInclusion = DegeneratePlaneFactorization.cone :=
  DegeneratePlaneFactorization.formedMediator_factorization

example : DegeneratePlaneFactorization.finalMediator ≫
    DegeneratePlaneLifts.finalInclusion = DegeneratePlaneFactorization.pairedCone :=
  DegeneratePlaneFactorization.finalMediator_factorization

example :
    ((changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)) ⋙ forget ℚ ℚ).map
      DegeneratePlaneFactorization.finalMediator ≫ DegeneratePlaneLifts.finalAlpha =
      DegeneratePlaneFactorization.baseMediator :=
  DegeneratePlaneFactorization.finalMediator_comparison

example (k : DegeneratePlaneFactorization.pairedConeSource ⟶
    DegeneratePlaneLifts.finalObject)
    (hk : ((changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)) ⋙ forget ℚ ℚ).map k ≫
        DegeneratePlaneLifts.finalAlpha = DegeneratePlaneFactorization.baseMediator ∧
      k ≫ DegeneratePlaneLifts.finalInclusion = DegeneratePlaneFactorization.pairedCone) :
    k = DegeneratePlaneFactorization.finalMediator :=
  DegeneratePlaneFactorization.finalMediator_unique k hk

-- The necessary second-factor source comparison is a complete formed isomorphism.
-- Its source is not replaced by a carrier identity in any .cas proposal.
example :
    (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).map
        DegeneratePlaneFactorization.finalMediator ≫
      DegeneratePlaneLifts.secondLift.computation.forward
        DegeneratePlaneLifts.pairedSource DegeneratePlaneLifts.firstInclusion =
      (ChangeValueLifts.pulledBackIso ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
          DegeneratePlaneLifts.pairedSource DegeneratePlaneFactorization.cone).hom ≫
        DegeneratePlaneFactorization.formedMediator := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ModuleCat.hom_ext
  rfl

example :
    (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).map
        DegeneratePlaneFactorization.pairedCone =
      ((ChangeValueLifts.pulledBackIso ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
          DegeneratePlaneLifts.pairedSource DegeneratePlaneFactorization.cone).hom ≫
        DegeneratePlaneFactorization.formedMediator) ≫
          DegeneratePlaneLifts.firstInclusion := by
  rw [Category.assoc, DegeneratePlaneFactorization.formedMediator_factorization]
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ModuleCat.hom_ext
  rfl
