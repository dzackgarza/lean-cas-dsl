/-
Additional independently specified expectations for the existing RX questions.

Only mathematical imports occur here. In particular these examples do not import
the CAS kernel, a computation implementation, or execution output. The expected
statements were fixed before checking their proofs. No definition or registry row
is introduced, and no acceptance or execution outcome is declared.
-/
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Foundation
open CasCatalogue.Algebra
open CasCatalogue.Modules
open CasCatalogue.Modules.Bilinear.Valued

-- RX-02: both directions are the original map on the original finite set.
example : (CoreIsomorphisms.finRevIso 5).hom = Morphisms.finRev 5 := rfl

example : (CoreIsomorphisms.finRevIso 5).inv = Morphisms.finRev 5 := rfl

example : (CoreIsomorphisms.finRevIso 5).hom (0 : Fin 5) = 4 := rfl

example (s : TwoSubsets.twoSubsets (Fin 5)) :
    TwoSubsets.inclusion (Fin 5) s = s.val := rfl

example (s : TwoSubsets.twoSubsets (Fin 5)) :
    FiniteSubsets.inclusion (Fin 5)
        (TwoSubsets.inclusion (Fin 5)
          (TwoSubsets.onCore.map (CoreIsomorphisms.finRevCore 5) s)) =
      (CoreIsomorphisms.finRevIso 5).hom ''
        FiniteSubsets.inclusion (Fin 5) (TwoSubsets.inclusion (Fin 5) s) :=
  TwoSubsets.map_extent (CoreIsomorphisms.finRevCore 5).iso.toEquiv.toEmbedding s

example :
    TwoSubsets.onCore.map
        (CoreIsomorphisms.finRevCore 5 ≫ CoreIsomorphisms.finRevCore 5) =
      TwoSubsets.onCore.map (CoreIsomorphisms.finRevCore 5) ≫
        TwoSubsets.onCore.map (CoreIsomorphisms.finRevCore 5) :=
  TwoSubsets.onCore.map_comp _ _

example :
    TwoSubsets.onCore.map
        (CoreIsomorphisms.finRevCore 5 ≫ CoreIsomorphisms.finRevCore 5) =
      𝟙 (TwoSubsets.twoSubsets (Fin 5)) := by
  rw [CoreIsomorphisms.finRevCore_comp, TwoSubsets.onCore.map_id]
  rfl

-- RX-03: the two complete coordinate formulas use the group structure of
-- Multiplicative(ZMod 5), whose powers are additive repeated sums.
set_option backward.isDefEq.respectTransparency false in
example (z : CyclicQuotients.cyclicQuotient 5) :
    (CyclicQuotients.residueComparison 5).hom
        (AutomorphismArrows.groupsForward (CyclicQuotients.cyclicQuotient 5)
          (CyclicQuotients.byUnit 5 CyclicQuotients.unitTwo) z) =
      ((CyclicQuotients.residueComparison 5).hom z) ^ 2 := by
  apply (@Multiplicative.toAdd (ZMod 5)).injective
  rw [toAdd_pow (α := ZMod 5)]
  simpa only [nsmul_eq_mul, Nat.cast_ofNat, AutomorphismArrows.groupsForward,
    AutomorphismArrows.forward, CyclicQuotients.unitTwo, Units.val_mk] using
    CyclicQuotients.byUnit_coordinate 5 CyclicQuotients.unitTwo z

set_option backward.isDefEq.respectTransparency false in
example (z : CyclicQuotients.cyclicQuotient 5) :
    (CyclicQuotients.residueComparison 5).hom
        (AutomorphismArrows.groupsForward (CyclicQuotients.cyclicQuotient 5)
          (CyclicQuotients.byUnit 5 CyclicQuotients.unitThree) z) =
      ((CyclicQuotients.residueComparison 5).hom z) ^ 3 := by
  apply (@Multiplicative.toAdd (ZMod 5)).injective
  rw [toAdd_pow (α := ZMod 5)]
  simpa only [nsmul_eq_mul, Nat.cast_ofNat, AutomorphismArrows.groupsForward,
    AutomorphismArrows.forward, CyclicQuotients.unitThree, Units.val_mk] using
    CyclicQuotients.byUnit_coordinate 5 CyclicQuotients.unitThree z

example :
    AutomorphismArrows.groupsBackward (CyclicQuotients.cyclicQuotient 5)
        (CyclicQuotients.byUnit 5 CyclicQuotients.unitTwo) =
      AutomorphismArrows.groupsForward (CyclicQuotients.cyclicQuotient 5)
        (CyclicQuotients.byUnit 5 CyclicQuotients.unitThree) := by
  change (CyclicQuotients.byUnit 5 CyclicQuotients.unitTwo)⁻¹.hom = _
  rw [CyclicQuotients.byUnit_two_inverse]
  rfl

example (k : ℤ) :
    AutomorphismArrows.groupsForward (CyclicQuotients.cyclicQuotient 5)
        (CyclicQuotients.byUnit 5 CyclicQuotients.unitTwo)
        (CyclicQuotients.quotientMap 5 k) =
      CyclicQuotients.quotientMap 5 (2 * k) := by
  apply (ConcreteCategory.bijective_of_isIso
    (CyclicQuotients.residueComparison 5).hom).injective
  apply (@Multiplicative.toAdd (ZMod 5)).injective
  calc
    _ = (CyclicQuotients.unitTwo : ZMod 5) *
        @Multiplicative.toAdd (ZMod 5)
          ((CyclicQuotients.residueComparison 5).hom
            (CyclicQuotients.quotientMap 5 k)) :=
      CyclicQuotients.byUnit_coordinate 5 CyclicQuotients.unitTwo
        (CyclicQuotients.quotientMap 5 k)
    _ = ((2 * k : ℤ) : ZMod 5) := by
      rw [CyclicQuotients.residueComparison_quotient]
      change (2 : ZMod 5) * (k : ZMod 5) = ((2 * k : ℤ) : ZMod 5)
      simp
    _ = _ := by rw [CyclicQuotients.residueComparison_quotient]; rfl

-- RX-08 and RX-LIFT: the full vector modules are definitionally the declared
-- Fin-indexed modules. No product-to-vector comparison is needed at these uses.
example : ModuleKernelRestriction.RationalProjection.diagonalSource.carrierObj =
    LinearAlgebra.vectorModule (RingCat.of ℚ) 2 := rfl

example : DegeneratePlaneLifts.source.carrierObj =
    LinearAlgebra.vectorModule (RingCat.of ℚ) 2 := rfl

example : DegeneratePlaneLifts.target.carrierObj =
    LinearAlgebra.vectorModule (RingCat.of ℚ) 2 := rfl

example : DegeneratePlaneLifts.pairedSource.carrierObj =
    LinearAlgebra.vectorModule (RingCat.of ℚ) 2 := rfl

example : DegeneratePlaneFactorization.zeroSource.carrierObj =
    LinearAlgebra.vectorModule (RingCat.of ℚ) 2 := rfl

example : DegeneratePlaneFactorization.pairedConeSource.carrierObj =
    LinearAlgebra.vectorModule (RingCat.of ℚ) 2 := rfl

example : ModuleKernelRestriction.RationalProjection.projection =
    RectangularLinearAlgebra.rowLinearMap 2 (CommRingCat.of ℚ) !![1, 0] := rfl

example : DegeneratePlaneFactorization.baseMediator =
    RectangularLinearAlgebra.rowLinearMap 2 (CommRingCat.of ℚ) !![3 / 2, -1] := rfl

example : CatalogueRegistration.regularModule (RingCat.of ℚ) =
    ModuleCat.of ℚ ℚ := rfl

-- RX-08's ordinary kernel carries the full categorical universal property.
-- This is separate from the universal exclusion of every target form in
-- expected-facts.lean and from any observations of the returned kernel.
example : CategoryTheory.Limits.IsLimit
    (ModuleCat.kernelCone ModuleKernelRestriction.RationalProjection.projection) :=
  ModuleCat.kernelIsLimit ModuleKernelRestriction.RationalProjection.projection

-- The value module is the ordered product module; this is a LinearMap on
-- ℚ × ℚ, independently of the separate vector-carrier presentations above.
example (p : ℚ × ℚ) : (LinearMap.fst ℚ ℚ ℚ) p = p.1 := rfl

-- RX-LIFT: the source comparison is the existing whole formed isomorphism.
example :
    ChangeValueLifts.pulledBackForward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
        DegeneratePlaneLifts.pairedSource DegeneratePlaneFactorization.cone ≫
      ChangeValueLifts.pulledBackBackward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
        DegeneratePlaneLifts.pairedSource DegeneratePlaneFactorization.cone =
      𝟙 ((changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).obj
        DegeneratePlaneFactorization.pairedConeSource) :=
  ChangeValueLifts.pulledBackForward_backward _ _ _ _ _ _

example :
    ChangeValueLifts.pulledBackBackward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
        DegeneratePlaneLifts.pairedSource DegeneratePlaneFactorization.cone ≫
      ChangeValueLifts.pulledBackForward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
        DegeneratePlaneLifts.pairedSource DegeneratePlaneFactorization.cone =
      𝟙 DegeneratePlaneFactorization.zeroSource :=
  ChangeValueLifts.pulledBackBackward_forward _ _ _ _ _ _

-- This proves compatibility for the actual first canonical factor, not for
-- a substituted named map that merely has the same underlying function.
set_option backward.isDefEq.respectTransparency false in
example :
    (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).map
        DegeneratePlaneFactorization.pairedCone =
      (ChangeValueLifts.pulledBackForward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
          DegeneratePlaneLifts.pairedSource DegeneratePlaneFactorization.cone ≫
        DegeneratePlaneLifts.firstLift.factor DegeneratePlaneLifts.source
          DegeneratePlaneLifts.kernelInclusion
          (Y := DegeneratePlaneFactorization.zeroSource)
          DegeneratePlaneFactorization.baseMediator
          DegeneratePlaneFactorization.cone
          DegeneratePlaneFactorization.cone_base_factorization) ≫
        DegeneratePlaneLifts.firstInclusion := by
  apply CasCatalogue.Independent.InterfaceCompletionTests.paired_cone_factor_compatibility
  exact DegeneratePlaneLifts.firstLift.factor_hom _ _ _ _ _
