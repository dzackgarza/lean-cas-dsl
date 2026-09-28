/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Modules.Rank
public import CasCatalogue.Leaves.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Modules.Annihilator
public import LeanCategories.CategoryTheory.OneCat.ImageFunctor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Modules.Catalogue
public meta import CasCatalogue.Leaves.Modules.Rank
public meta import CasCatalogue.Leaves.Modules.Bilinear.Valued.Kernels

@[expose] public section

/-!
# Operations on modules and their morphisms (`cc-dsl-migration`)

* `annihilator : Core(Mod_R) ⥤ Disc(Ideal R)` (`LeanCategories.Modules.annihilatorFunctor`), the
  iso-invariant method `annihilator` of `Mod_R`;
* `dim`: the surface name of the rank of a module (`fun.modules.rank`), for vector spaces;
* `im : Arr(Mod_R) ⥤ Subobjects(Mod_R)` (`LeanCategories.imageFunctor`), the image of a morphism
  as a subobject of its codomain, and `ker`, the surface name of the kernel of a morphism.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Modules.Rank CasCatalogue.Modules.Bilinear.Valued.Kernels

namespace CasCatalogue

namespace CategoryId
def ideals : CategoryId := ⟨"cat.ideals_r"⟩
end CategoryId

namespace FunctorId
def modulesAnnihilator : FunctorId := ⟨"fun.modules.annihilator"⟩
def arrowsModulesImage : FunctorId := ⟨"fun.arrows_modules.image"⟩
end FunctorId

namespace Modules.Operations

universe u

def Ideals : CategoryExpr := .atom CategoryId.ideals
def AnnihilatorExpr : FunctorExpr CoreModules Ideals := .atomic FunctorId.modulesAnnihilator
def ImageExpr : FunctorExpr ArrowsModules SubobjectsModules :=
  .atomic FunctorId.arrowsModulesImage

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
