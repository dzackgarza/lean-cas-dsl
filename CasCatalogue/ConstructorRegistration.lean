/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.ConstructorCatalogue
public import CasCatalogue.Constructors
public import CasCatalogue.Registry.Extension
public import CasCatalogue.Leaves.Foundation.CatalogueRegistration
public import CasCatalogue.Leaves.Modules.CatalogueRegistration
public meta import CasCatalogue.ConstructorCatalogue
public meta import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# Registered typed category constructors and constructed categories (#54 §1, CC-CALC)

Every constructed category below is registered with the expression `.construct c args` and is
checked at registration to be definitionally `c`'s semantics (`Catalogue/Constructors.lean`)
applied to the registered denotations of its arguments. `Subobjects(Sets)` is a constructed
category, not an alias or atom (#54 acceptance).
-/

namespace CasCatalogue.Catalogue.ConstructorRegistration
open LeanCategories

open CategoryTheory LeanCategories CasCatalogue CasCatalogue.Modules.CatalogueRegistration

noncomputable section

universe u

def arrowsSetsCategory := Constructors.arrow Foundation.Mathlib.Sets.{u}
def arrowsSetsRealization :
    CategoryRealization Constructed.ArrowsSets arrowsSetsCategory.{u} := {}

def coreSetsCategory := Constructors.core Foundation.Mathlib.Sets.{u}
def coreSetsRealization : CategoryRealization Constructed.CoreSets coreSetsCategory.{u} := {}

def sliceSetsCategory (X : Type u) := Constructors.slice Foundation.Mathlib.Sets.{u} X
def sliceSetsRealization (X : Type u) :
    CategoryRealization Constructed.SliceSets (sliceSetsCategory X) := {}

def cosliceSetsCategory (X : Type u) := Constructors.coslice Foundation.Mathlib.Sets.{u} X
def cosliceSetsRealization (X : Type u) :
    CategoryRealization Constructed.CosliceSets (cosliceSetsCategory X) := {}

def subobjectsSetsCategory := Constructors.subobjects Foundation.Mathlib.Sets.{u}
def subobjectsSetsRealization :
    CategoryRealization Constructed.SubobjectsSets subobjectsSetsCategory.{u} := {}

def modulePointsCategory :=
  Constructors.elements modulesTotalCategory.{u, u} modulesUnderlyingDeclaration.{u, u}
def modulePointsRealization :
    CategoryRealization Constructed.ModulePoints modulePointsCategory.{u} := {}

def endofunctorsSetsCategory :=
  Constructors.functorCategory Foundation.Mathlib.Sets.{u} Foundation.Mathlib.Sets.{u}
def endofunctorsSetsRealization :
    CategoryRealization Constructed.EndofunctorsSets endofunctorsSetsCategory.{u} := {}

/-- The forgetful functor `Over X ⥤ Sets`. -/
def sliceSetsForgetDeclaration (X : Type u) :
    sliceSetsCategory X ⥤ Foundation.Mathlib.Sets.{u} :=
  Over.forget X
def sliceSetsForgetRealization (X : Type u) :
    FunctorRealization Constructed.SliceSetsForgetExpr (sliceSetsCategory X)
      Foundation.Mathlib.Sets.{u} (sliceSetsForgetDeclaration X) :=
  { sourceRealization := sliceSetsRealization X
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

/-- The projection of the points of modules to the modules: `CategoryOfElements.π U`. -/
def modulePointsProjectionDeclaration :
    modulePointsCategory.{u} ⥤ modulesTotalCategory.{u, u} :=
  CategoryOfElements.π _
def modulePointsProjectionRealization :
    FunctorRealization Constructed.ModulePointsProjectionExpr modulePointsCategory.{u}
      modulesTotalCategory.{u, u} modulePointsProjectionDeclaration :=
  { sourceRealization := modulePointsRealization
    targetRealization := modulesTotalRealization }

end

normalized_registry .constructor
  { id := ConstructorId.arrow, signature := #[.category],
    semantics := `CasCatalogue.Constructors.arrow
    functorialAction := some `CasCatalogue.Constructors.arrowMap }
normalized_registry .constructor
  { id := ConstructorId.core, signature := #[.category],
    semantics := `CasCatalogue.Constructors.core
    functorialAction := some `CasCatalogue.Constructors.coreMap }
normalized_registry .constructor
  { id := ConstructorId.slice, signature := #[.category, .object],
    semantics := `CasCatalogue.Constructors.slice }
normalized_registry .constructor
  { id := ConstructorId.coslice, signature := #[.category, .object],
    semantics := `CasCatalogue.Constructors.coslice }
normalized_registry .constructor
  { id := ConstructorId.elements, signature := #[.category, .functor],
    semantics := `CasCatalogue.Constructors.elements }
normalized_registry .constructor
  { id := ConstructorId.subobjects, signature := #[.category],
    semantics := `CasCatalogue.Constructors.subobjects }
normalized_registry .constructor
  { id := ConstructorId.functorCategory, signature := #[.category, .category],
    semantics := `CasCatalogue.Constructors.functorCategory }

normalized_registry .category
  { id := CategoryId.arrowsSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.arrowsSetsCategory
    expression := Constructed.ArrowsSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.arrowsSetsRealization }
normalized_registry .category
  { id := CategoryId.coreSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.coreSetsCategory
    expression := Constructed.CoreSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.coreSetsRealization }
normalized_registry .category
  { id := CategoryId.sliceSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.sliceSetsCategory
    expression := Constructed.SliceSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.sliceSetsRealization }
normalized_registry .category
  { id := CategoryId.cosliceSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.cosliceSetsCategory
    expression := Constructed.CosliceSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.cosliceSetsRealization }
normalized_registry .category
  { id := CategoryId.subobjectsSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsCategory
    expression := Constructed.SubobjectsSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsRealization }
normalized_registry .category
  { id := CategoryId.modulePoints,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.modulePointsCategory
    expression := Constructed.ModulePoints
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.modulePointsRealization }
normalized_registry .category
  { id := CategoryId.endofunctorsSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.endofunctorsSetsCategory
    expression := Constructed.EndofunctorsSets
    realization :=
      `CasCatalogue.Catalogue.ConstructorRegistration.endofunctorsSetsRealization }

normalized_registry .functor
  { id := FunctorId.sliceSetsForget,
    source := Constructed.SliceSets
    target := Foundation.Sets
    declaration :=
      `CasCatalogue.Catalogue.ConstructorRegistration.sliceSetsForgetDeclaration
    realization :=
      `CasCatalogue.Catalogue.ConstructorRegistration.sliceSetsForgetRealization
    expression := Constructed.SliceSetsForgetExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.modulePointsProjection,
    source := Constructed.ModulePoints
    target := Modules.ModulesTotal
    declaration :=
      `CasCatalogue.Catalogue.ConstructorRegistration.modulePointsProjectionDeclaration
    realization :=
      `CasCatalogue.Catalogue.ConstructorRegistration.modulePointsProjectionRealization
    expression := Constructed.ModulePointsProjectionExpr
    structural := true }

/-! ### Negative probe: a constructed category must be its constructor's semantics -/

noncomputable def coreAsArrows := Constructors.core Foundation.Mathlib.Sets.{0}
noncomputable def coreAsArrowsRealization :
    CategoryRealization Constructed.ArrowsSets coreAsArrows := {}

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let rejects (entry : RegistryEntry) : MetaM Bool := do
      try
        validateRegistryEntryDeclaration entry
        pure false
      catch _ => pure true
    unless ← rejects (.category
        { id := ⟨"cat.probe.core_as_arrows"⟩
          declaration := `CasCatalogue.Catalogue.ConstructorRegistration.coreAsArrows
          expression := Constructed.ArrowsSets
          realization :=
            `CasCatalogue.Catalogue.ConstructorRegistration.coreAsArrowsRealization }) do
      throwError "Core(Sets) was accepted as Arr(Sets)"
    if ← rejects (.category
        { id := CategoryId.arrowsSets
          declaration := `CasCatalogue.Catalogue.ConstructorRegistration.arrowsSetsCategory
          expression := Constructed.ArrowsSets
          realization :=
            `CasCatalogue.Catalogue.ConstructorRegistration.arrowsSetsRealization }) then
      throwError "the canonical Arr(Sets) was rejected"

end CasCatalogue.Catalogue.ConstructorRegistration
