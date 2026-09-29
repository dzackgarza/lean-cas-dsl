/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Modules.Rank
public import CasCatalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Modules.Annihilator
public import LeanCategories.CategoryTheory.OneCat.ImageFunctor
public import LeanCategories.CategoryTheory.OneCat.SubobjectMap
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import CasCatalogue.Semantics.ConstructorRegistration
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.Modules.Catalogue
public meta import CasCatalogue.Semantics.Modules.Rank
public meta import CasCatalogue.Semantics.Modules.Bilinear.Valued.Kernels

@[expose] public section

/-!
# Operations on modules and their morphisms (`cc-dsl-migration`)

* `annihilator : Core(Mod_R) ⥤ Disc(Ideal R)` (`LeanCategories.Modules.annihilatorFunctor`), the
  iso-invariant method `annihilator` of `Mod_R`;
* `dim`: the surface name of the rank of a module (`fun.modules.rank`), for vector spaces;
* `im : Arr(Mod_R) ⥤ Subobjects(Mod_R)` (`LeanCategories.imageFunctor`), the image of a morphism
  as a subobject of its codomain, and `ker`, the surface name of the kernel of a morphism;
* `Sub(Mod_R) ⥤ Sub(Sets)` (`LeanCategories.subobjectMap` of the forgetful functor, a right
  adjoint and so mono-preserving): a submodule as the subset it is of the underlying set of its
  ambient module — the structural route by which a submodule reaches `contains`, `set_eq`, `⊆`;
* `Sub(Mod_R) ⥤ Mod_R`, a submodule as the module it is (the domain of its inclusion). It is
  not structural: a submodule `W ≤ V` read as the module `W` would reach `contains` as membership
  in `W` itself (always true of an element of `W`), a different operation from membership in `V`
  through the subset `W ⊆ V`. `dim` is registered on subobjects directly, as
  `rank ∘ domain : Core(Sub(Mod_R)) ⥤ Card`.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Modules.Rank CasCatalogue.Modules.Bilinear.Valued.Kernels
open CasCatalogue.Foundation.Cardinality

namespace CasCatalogue

namespace CategoryId
def ideals : CategoryId := ⟨"cat.ideals_r"⟩
def coreSubobjectsModules : CategoryId := ⟨"cat.core_subobjects_modules_r"⟩
end CategoryId

namespace FunctorId
def modulesAnnihilator : FunctorId := ⟨"fun.modules.annihilator"⟩
def arrowsModulesImage : FunctorId := ⟨"fun.arrows_modules.image"⟩
def subobjectsModulesForget : FunctorId := ⟨"fun.subobjects_modules.forget"⟩
def subobjectsModulesDomain : FunctorId := ⟨"fun.subobjects_modules.domain"⟩
def subobjectsModulesRank : FunctorId := ⟨"fun.subobjects_modules.rank"⟩
end FunctorId

namespace Modules.Operations

universe u

def Ideals : CategoryExpr := .atom CategoryId.ideals
def AnnihilatorExpr : FunctorExpr CoreModules Ideals := .atomic FunctorId.modulesAnnihilator
def ImageExpr : FunctorExpr ArrowsModules SubobjectsModules :=
  .atomic FunctorId.arrowsModulesImage
def SubobjectsForgetExpr : FunctorExpr SubobjectsModules Constructed.SubobjectsSets :=
  .atomic FunctorId.subobjectsModulesForget
def SubobjectsDomainExpr : FunctorExpr SubobjectsModules Modules.Modules :=
  .atomic FunctorId.subobjectsModulesDomain
def CoreSubobjectsModules : CategoryExpr :=
  .construct ConstructorId.core #[.category SubobjectsModules]
def SubobjectsRankExpr : FunctorExpr CoreSubobjectsModules Foundation.Cardinality.Cardinals :=
  .atomic FunctorId.subobjectsModulesRank

noncomputable section

/-- The ideals of `R`, as a discrete category. -/
def idealsCategory (R : RingCat.{u}) : ObjCat.{u, u} := Cat.of (Discrete (Ideal R))
def idealsRealization (R : RingCat.{u}) : CategoryRealization Ideals (idealsCategory R) := {}

/-- `Ann_R : Core(Mod_R) ⥤ Disc(Ideal R)`. -/
def annihilatorDeclaration (R : RingCat.{u}) : coreModulesCategory R ⥤ idealsCategory R :=
  LeanCategories.Modules.annihilatorFunctor.{u, u} R
def annihilatorRealization (R : RingCat.{u}) :
    FunctorRealization AnnihilatorExpr (coreModulesCategory R) (idealsCategory R)
      (annihilatorDeclaration R) :=
  { sourceRealization := coreModulesRealization R, targetRealization := idealsRealization R }

/-- The image of a module map, with its inclusion into the codomain. -/
def imageDeclaration (R : RingCat.{u}) :
    arrowsModulesCategory R ⥤ subobjectsModulesCategory R :=
  imageFunctor (ModuleCat.{u} R)
def imageRealization (R : RingCat.{u}) :
    FunctorRealization ImageExpr (arrowsModulesCategory R) (subobjectsModulesCategory R)
      (imageDeclaration R) :=
  { sourceRealization := arrowsModulesRealization R
    targetRealization := subobjectsModulesRealization R }

/-- A submodule, as a subset of the underlying set of its ambient module. -/
def subobjectsForgetDeclaration (R : RingCat.{u}) :
    subobjectsModulesCategory R ⥤
      CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsCategory.{u} :=
  subobjectMap (C := ModuleCat.{u} R) (D := Type u) (forget (ModuleCat.{u} R))
def subobjectsForgetRealization (R : RingCat.{u}) :
    FunctorRealization SubobjectsForgetExpr (subobjectsModulesCategory R)
      CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsCategory.{u}
      (subobjectsForgetDeclaration R) :=
  { sourceRealization := subobjectsModulesRealization R
    targetRealization := CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsRealization }

/-- A submodule is the module it is: the domain of its inclusion. -/
def subobjectsDomainDeclaration (R : RingCat.{u}) :
    subobjectsModulesCategory R ⥤ Modules.Mathlib.ModulesOf.{u, u} R :=
  (Constructors.isMonoArrow (Modules.Mathlib.ModulesOf.{u, u} R)).ι ⋙ Arrow.leftFunc
def subobjectsDomainRealization (R : RingCat.{u}) :
    FunctorRealization SubobjectsDomainExpr (subobjectsModulesCategory R)
      (Modules.Mathlib.ModulesOf.{u, u} R) (subobjectsDomainDeclaration R) :=
  { sourceRealization := subobjectsModulesRealization R
    targetRealization := CasCatalogue.Modules.CatalogueRegistration.modulesRealization R }

def coreSubobjectsModulesCategory (R : RingCat.{u}) :=
  Constructors.core (subobjectsModulesCategory R)
def coreSubobjectsModulesRealization (R : RingCat.{u}) :
    CategoryRealization CoreSubobjectsModules (coreSubobjectsModulesCategory R) := {}

/-- `dim` of a submodule: the rank of the module it is. -/
def subobjectsRankDeclaration (R : RingCat.{u}) :
    coreSubobjectsModulesCategory R ⥤ cardinalsCategory.{u} :=
  (subobjectsDomainDeclaration R).core ⋙ rankDeclaration R
def subobjectsRankRealization (R : RingCat.{u}) :
    FunctorRealization SubobjectsRankExpr (coreSubobjectsModulesCategory R) cardinalsCategory.{u}
      (subobjectsRankDeclaration R) :=
  { sourceRealization := coreSubobjectsModulesRealization R
    targetRealization := cardinalsRealization }

end

end Modules.Operations

open Modules.Operations

normalized_registry .category
  { id := CategoryId.ideals, declaration := `CasCatalogue.Modules.Operations.idealsCategory
    expression := Ideals, realization := `CasCatalogue.Modules.Operations.idealsRealization }
normalized_registry .functor
  { id := FunctorId.modulesAnnihilator, source := CoreModules, target := Ideals
    declaration := `CasCatalogue.Modules.Operations.annihilatorDeclaration
    realization := `CasCatalogue.Modules.Operations.annihilatorRealization
    expression := AnnihilatorExpr }
normalized_registry .functor
  { id := FunctorId.arrowsModulesImage, source := ArrowsModules, target := SubobjectsModules
    declaration := `CasCatalogue.Modules.Operations.imageDeclaration
    realization := `CasCatalogue.Modules.Operations.imageRealization
    expression := ImageExpr }
normalized_registry .functor
  { id := FunctorId.subobjectsModulesForget, source := SubobjectsModules
    target := Constructed.SubobjectsSets
    declaration := `CasCatalogue.Modules.Operations.subobjectsForgetDeclaration
    realization := `CasCatalogue.Modules.Operations.subobjectsForgetRealization
    expression := SubobjectsForgetExpr, structural := true }
normalized_registry .functor
  { id := FunctorId.subobjectsModulesDomain, source := SubobjectsModules
    target := Modules.Modules
    declaration := `CasCatalogue.Modules.Operations.subobjectsDomainDeclaration
    realization := `CasCatalogue.Modules.Operations.subobjectsDomainRealization
    expression := SubobjectsDomainExpr }
normalized_registry .category
  { id := CategoryId.coreSubobjectsModules
    declaration := `CasCatalogue.Modules.Operations.coreSubobjectsModulesCategory
    expression := CoreSubobjectsModules
    realization := `CasCatalogue.Modules.Operations.coreSubobjectsModulesRealization }
normalized_registry .functor
  { id := FunctorId.subobjectsModulesRank, source := CoreSubobjectsModules
    target := Foundation.Cardinality.Cardinals
    declaration := `CasCatalogue.Modules.Operations.subobjectsRankDeclaration
    realization := `CasCatalogue.Modules.Operations.subobjectsRankRealization
    expression := SubobjectsRankExpr }
normalized_registry .method
  { id := ⟨"meth.subobject_dim"⟩, name := "dim", owner := SubobjectsModules
    functor := FunctorId.subobjectsModulesRank, shape := .isoInvariant }
normalized_registry .method
  { id := ⟨"meth.annihilator"⟩, name := "annihilator", owner := Modules.Modules
    functor := FunctorId.modulesAnnihilator, shape := .isoInvariant }
normalized_registry .method
  { id := ⟨"meth.dim"⟩, name := "dim", owner := Modules.Modules
    functor := FunctorId.modulesRank, shape := .isoInvariant }
normalized_registry .method
  { id := ⟨"meth.arrow_ker"⟩, name := "ker", owner := ArrowsModules
    functor := FunctorId.arrowsModulesKernel, shape := .object }
normalized_registry .method
  { id := ⟨"meth.arrow_im"⟩, name := "im", owner := ArrowsModules
    functor := FunctorId.arrowsModulesImage, shape := .object }

end CasCatalogue
