/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Foundation.CatalogueRegistration
public import CasCatalogue.Semantics.Algebra.CatalogueRegistration
public import LeanCategories.Algebra.GroupKernel
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import LeanCategories.Modules.Bilinear.Valued.Cokernel
public import CasCatalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public meta import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# Registered limit presentations (CC-UNIV)

* `lim.sets.pullback`: the explicit pullback of sets, `{(x, y) | f x = g y}` with its projections
  (Mathlib `Types.pullbackLimitCone`);
* `colim.sets.coproduct`: the disjoint union `X ⊕ Y` with its injections (Mathlib
  `Types.binaryCoproductColimitCocone`);
* `colim.bil_w_form.cokernel`: the cokernel of a map of formed modules with varying values, the
  quotients of the carrier and of the values by the images and the mixed relations
  (lean-categories `BilWFormCat.cokernelIsColimit`); the discriminant `L♯/L` of an integral lattice
  is the cokernel of `L → L♯`;
* `lim.groups.kernel`: the kernel `ker f ↪ G` of a group homomorphism, an equalizer of `f` and
  the trivial homomorphism (`LeanCategories.Algebra.kernelLimitCone`).

Each is a family of Mathlib `LimitCone`s: apex, legs, and the mediator `IsLimit.lift`.
-/

open CategoryTheory Limits

namespace CasCatalogue.Limits.Registration

universe u

/-- Pullbacks in `Sets`. -/
def setsPullback {X Y Z : LeanCategories.Foundation.Mathlib.Sets.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    LimitCone (cospan f g) :=
  Types.pullbackLimitCone f g

/-- Kernels in `Grp`. -/
def groupsKernel {G H : GrpCat.{u}} (f : G ⟶ H) :
    LimitCone (parallelPair f 1) :=
  LeanCategories.Algebra.kernelLimitCone f

/-- Binary coproducts in `Sets`. -/
def setsCoproduct (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    ColimitCocone (pair X Y) :=
  Types.binaryCoproductColimitCocone X Y

/-- Cokernels of formed modules with varying values. -/
def bilWFormCokernel {R : Type u} [CommRing R]
    {X Y : LeanCategories.Modules.Bilinear.Valued.BilWFormCat R} (f : X ⟶ Y) :
    ColimitCocone (parallelPair f 0) :=
  ⟨_, LeanCategories.Modules.Bilinear.Valued.BilWFormCat.cokernelIsColimit f⟩

end CasCatalogue.Limits.Registration

namespace CasCatalogue

normalized_registry .limit
  { id := ⟨"lim.sets.pullback"⟩, category := CategoryId.sets, shape := "pullback"
    declaration := `CasCatalogue.Limits.Registration.setsPullback }

normalized_registry .limit
  { id := ⟨"colim.sets.coproduct"⟩, category := CategoryId.sets, shape := "coproduct"
    declaration := `CasCatalogue.Limits.Registration.setsCoproduct, colimit := true }

normalized_registry .limit
  { id := ⟨"colim.bil_w_form.cokernel"⟩, category := CategoryId.bilWForm, shape := "cokernel"
    declaration := `CasCatalogue.Limits.Registration.bilWFormCokernel, colimit := true }

normalized_registry .limit
  { id := ⟨"lim.groups.kernel"⟩, category := ⟨"cat.groups"⟩, shape := "kernel"
    declaration := `CasCatalogue.Limits.Registration.groupsKernel }

end CasCatalogue
