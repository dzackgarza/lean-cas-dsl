/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public import CasCatalogue.Semantics.ConstructorRegistration
public import CasCatalogue.Lift
public import LeanCategories.CategoryTheory.OneCat.KernelFunctor
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.ConstructorCatalogue
public meta import CasCatalogue.Semantics.Modules.Bilinear.Valued.Expressions

@[expose] public section

/-!
# Kernels of formed-module morphisms (CC-LIFT)

The kernel is owned by modules: `kernel : Arr(Mod_R) → Subobjects(Mod_R)`
(`LeanCategories.kernelFunctor`, complete universal data `(K, ι)`). A morphism of formed modules
reaches it along `Arr(U) : Arr(BilinModule) → Arr(Mod_R)`, the forgetful functor `U` acting on
arrows: a derived edge (the arrow constructor is functorial), not a registered row. The result is a subobject of the *underlying module*; to be a formed submodule of the
formed module it must be lifted back, and the lift is registered data: restriction of the form
along the kernel inclusion (`BilinModuleCat.restrict`), the cartesian lift of monomorphisms along
the forgetful functor (`forgetMonoLift`). Without that row the call reports the missing lift.
-/

open CategoryTheory CategoryTheory.Limits
open LeanCategories LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration

namespace CasCatalogue

namespace CategoryId
def arrowsModules : CategoryId := ⟨"cat.arrows_modules_r"⟩
def subobjectsModules : CategoryId := ⟨"cat.subobjects_modules_r"⟩
def arrowsBilinModule : CategoryId := ⟨"cat.arrows_bilin_module"⟩
def subobjectsBilinModule : CategoryId := ⟨"cat.subobjects_bilin_module"⟩
end CategoryId

namespace FunctorId
def arrowsModulesKernel : FunctorId := ⟨"fun.arrows_modules.kernel"⟩
end FunctorId

namespace Modules.Bilinear.Valued.Kernels

universe u

def ArrowsModules : CategoryExpr := .construct ConstructorId.arrow #[.category Modules.Modules]
def SubobjectsModules : CategoryExpr :=
  .construct ConstructorId.subobjects #[.category Modules.Modules]
def ArrowsBilin : CategoryExpr :=
  .construct ConstructorId.arrow #[.category Modules.Bilinear.Valued.Catalogue.BilinModule]
def SubobjectsBilin : CategoryExpr :=
  .construct ConstructorId.subobjects #[.category Modules.Bilinear.Valued.Catalogue.BilinModule]
def KernelExpr : FunctorExpr ArrowsModules SubobjectsModules := .atomic FunctorId.arrowsModulesKernel

noncomputable section

def arrowsModulesCategory (R : RingCat.{u}) :=
  Constructors.arrow (Modules.Mathlib.ModulesOf.{u, u} R)
def arrowsModulesRealization (R : RingCat.{u}) :
    CategoryRealization ArrowsModules (arrowsModulesCategory R) := {}
def subobjectsModulesCategory (R : RingCat.{u}) :=
  Constructors.subobjects (Modules.Mathlib.ModulesOf.{u, u} R)
def subobjectsModulesRealization (R : RingCat.{u}) :
    CategoryRealization SubobjectsModules (subobjectsModulesCategory R) := {}
def arrowsBilinCategory (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W] :=
  Constructors.arrow (bilinModuleCategory R W)
def arrowsBilinRealization (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W]
    [Module R W] : CategoryRealization ArrowsBilin (arrowsBilinCategory R W) := {}
def subobjectsBilinCategory (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W]
    [Module R W] := Constructors.subobjects (bilinModuleCategory R W)
def subobjectsBilinRealization (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W]
    [Module R W] : CategoryRealization SubobjectsBilin (subobjectsBilinCategory R W) := {}

/-- The kernel of a module map, with its inclusion. -/
def kernelDeclaration (R : RingCat.{u}) :
    arrowsModulesCategory R ⥤ subobjectsModulesCategory R :=
  kernelFunctor (ModuleCat.{u} R)
def kernelRealization (R : RingCat.{u}) :
    FunctorRealization KernelExpr (arrowsModulesCategory R) (subobjectsModulesCategory R)
      (kernelDeclaration R) :=
  { sourceRealization := arrowsModulesRealization R
    targetRealization := subobjectsModulesRealization R }

/-- Restriction of forms: the cartesian lift of a monomorphism `K ↪ U(X)` along the forgetful
functor `U` of formed modules is `X` restricted to the image of `K`, with its isometric
inclusion. -/
def forgetMonoLift (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W] :
    MonoLift (forget R W) where
  obj X _ i _ := X.restrict (LinearMap.range i.hom)
  hom X _ i _ := X.restrictInclusion (LinearMap.range i.hom)
  iso X _ i hi :=
    (LinearEquiv.ofInjective i.hom ((ModuleCat.mono_iff_injective i).mp hi)).symm.toModuleIso
  fac X _ i hi := by
    ext x
    exact (LinearEquiv.ofInjective_symm_apply (f := i.hom)
      (h := (ModuleCat.mono_iff_injective i).mp hi) x).symm

variable {R : Type u} [CommRing R] {W : Type u} [AddCommGroup W] [Module R W]

/-- The kernel of the underlying module map, as a submodule of the source. -/
def kernelSubmodule {L L' : BilinModuleCat R W} (f : L ⟶ L') : Submodule R L.carrier :=
  LinearMap.range (kernel.ι ((forget R W).map f)).hom

/-- The kernel of a formed-module morphism, as a formed module: the module kernel, lifted back
by restricting the form. -/
def formedKernel {L L' : BilinModuleCat R W} (f : L ⟶ L') : BilinModuleCat R W :=
  (forgetMonoLift R W).obj L (kernel.ι ((forget R W).map f))

/-- Its carrier is the kernel submodule. -/
theorem formedKernel_carrier {L L' : BilinModuleCat R W} (f : L ⟶ L') :
    ((formedKernel f).carrier : Type u) = kernelSubmodule f :=
  rfl

/-- Its form is the restriction of `L`'s. -/
theorem formedKernel_pairing {L L' : BilinModuleCat R W} (f : L ⟶ L')
    (x y : kernelSubmodule f) :
    (formedKernel f).pairing (show (formedKernel f).carrier from x)
      (show (formedKernel f).carrier from y) = L.pairing x.1 y.1 :=
  rfl

/-- Its elements are sent to zero by `f`. -/
theorem kernelSubmodule_map {L L' : BilinModuleCat R W} (f : L ⟶ L') (x : kernelSubmodule f) :
    BilinModuleCat.underlyingMap f x.1 = 0 := by
  obtain ⟨k, hk⟩ := x.2
  rw [← hk]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (kernel.condition ((forget R W).map f))) k

end

end Modules.Bilinear.Valued.Kernels

open Modules.Bilinear.Valued.Kernels

normalized_registry .category
  { id := CategoryId.arrowsModules
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.arrowsModulesCategory
    expression := ArrowsModules
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.arrowsModulesRealization }
normalized_registry .category
  { id := CategoryId.subobjectsModules
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsModulesCategory
    expression := SubobjectsModules
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsModulesRealization }
normalized_registry .category
  { id := CategoryId.arrowsBilinModule
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.arrowsBilinCategory
    expression := ArrowsBilin
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.arrowsBilinRealization }
normalized_registry .category
  { id := CategoryId.subobjectsBilinModule
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsBilinCategory
    expression := SubobjectsBilin
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsBilinRealization }
normalized_registry .functor
  { id := FunctorId.arrowsModulesKernel, source := ArrowsModules, target := SubobjectsModules
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.kernelDeclaration
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.kernelRealization
    expression := KernelExpr }
normalized_registry .method
  { id := ⟨"meth.kernel"⟩, name := "kernel", owner := ArrowsModules
    functor := FunctorId.arrowsModulesKernel, shape := .object, returnsToSource := true }
normalized_registry .lift
  { id := ⟨"lift.bilin_module.restrict"⟩
    edge := .constructMap ConstructorId.arrow (.functor FunctorId.bilinModuleForget)
    evidence := `CasCatalogue.Modules.Bilinear.Valued.Kernels.forgetMonoLift }

end CasCatalogue
