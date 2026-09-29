/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Lattices.Valued.CatalogueRegistration
public import CasCatalogue.Refine
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.Modules.Bilinear.Valued.Expressions

@[expose] public section

/-!
# Being a lattice, as a property of formed modules (CC-PROP)

`clf.bilin_module.lattice` is the classifier of the property `isLattice` (projective carrier,
symmetric form) on `BilinModule(R, W)`: its total is Mathlib's full subcategory `LatticeCat R W`,
the registered `cat.lattice`. `is_lattice` presents it; a formed module proved to be a lattice is
re-typed into `cat.lattice` by `refine%`.
-/

open CategoryTheory LeanCategories LeanCategories.Lattices.Valued

namespace CasCatalogue

namespace ClassifierId
def bilinModuleLattice : ClassifierId := ⟨"clf.bilin_module.lattice"⟩
end ClassifierId

namespace Lattices.Valued.Property

universe u

open CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration

/-- The classifier of the lattice property on formed modules. -/
noncomputable def latticeClassifier (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W]
    [Module R W] : Classifier (bilinModuleCategory R W) :=
  Classifier.ofProperty (C := bilinModuleCategory R W) (isLattice R W)

noncomputable def latticeClassifierRealization (R : Type u) [CommRing R] (W : Type u)
    [AddCommGroup W] [Module R W] :
    ClassifierRealization Modules.Bilinear.Valued.Catalogue.BilinModule
      ClassifierId.bilinModuleLattice (bilinModuleCategory R W) (latticeClassifier R W) :=
  { hostRealization := bilinModuleRealization R W, totalRealization := {} }

end Lattices.Valued.Property

normalized_registry .classifier
  { id := ClassifierId.bilinModuleLattice
    declaration := `CasCatalogue.Lattices.Valued.Property.latticeClassifier
    host := Modules.Bilinear.Valued.Catalogue.BilinModule
    realization := `CasCatalogue.Lattices.Valued.Property.latticeClassifierRealization }

normalized_registry .property
  { id := ⟨"prop.is_lattice"⟩, name := "is_lattice", classifier := ClassifierId.bilinModuleLattice }

end CasCatalogue
