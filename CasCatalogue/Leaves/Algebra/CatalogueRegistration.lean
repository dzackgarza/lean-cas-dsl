module

public import LeanCategories.Algebra.Concrete.Magmas
public import LeanCategories.Algebra.Concrete.Rings
public import CasCatalogue.Leaves.Algebra.Catalogue.Magmas
public import CasCatalogue.Leaves.Algebra.Catalogue.Rings
public import CasCatalogue.Leaves.Foundation.CatalogueRegistration
public import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Algebra.Catalogue.Magmas
public meta import CasCatalogue.Leaves.Algebra.Catalogue.Rings
public meta import CasCatalogue.Leaves.Foundation.CatalogueRegistration
public meta import CasCatalogue.Leaves.Algebra.Catalogue

@[expose] public section

namespace CasCatalogue.Algebra.CatalogueRegistration
open LeanCategories LeanCategories.Algebra

open LeanCategories CasCatalogue

universe u

noncomputable def magmasRealization :
    CategoryRealization Algebra.Catalogue.Magmas.Magmas Algebra.Magmas := { familyFibre := none }
noncomputable def semigroupsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.Semigroups Algebra.Semigroups := { familyFibre := none }
noncomputable def monoidsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.Monoids Algebra.Monoids := { familyFibre := none }
noncomputable def groupsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.Groups Algebra.Groups := { familyFibre := none }
noncomputable def additiveMagmasRealization :
    CategoryRealization Algebra.Catalogue.Magmas.AdditiveMagmas Algebra.AdditiveMagmas :=
  { familyFibre := none }
noncomputable def additiveSemigroupsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.AdditiveSemigroups
      Algebra.AdditiveSemigroups := { familyFibre := none }
noncomputable def additiveMonoidsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.AdditiveMonoids Algebra.AdditiveMonoids :=
  { familyFibre := none }
noncomputable def additiveGroupsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.AdditiveGroups Algebra.AdditiveGroups :=
  { familyFibre := none }
noncomputable def ringsRealization :
    CategoryRealization Algebra.Catalogue.Rings.Rings Algebra.Rings := { familyFibre := none }
noncomputable def commutativeRingsRealization :
    CategoryRealization Algebra.Catalogue.Rings.CommutativeRings
      Algebra.CommutativeRings := { familyFibre := none }
noncomputable def divisionRingsRealization :
    CategoryRealization Algebra.Catalogue.Rings.DivisionRings Algebra.DivisionRings :=
  { familyFibre := none }

noncomputable def associativeRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasAssociative
      Algebra.Magmas Algebra.associative :=
  { hostRealization := magmasRealization, totalRealization := {} }
noncomputable def commutativeRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasCommutative
      Algebra.Magmas Algebra.commutative :=
  { hostRealization := magmasRealization, totalRealization := {} }
noncomputable def unitalRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasUnital
      Algebra.Magmas Algebra.unital :=
  { hostRealization := magmasRealization, totalRealization := {} }
noncomputable def inverseRealization :
    ClassifierRealization (.classifierTotal ClassifierId.magmasUnital)
      ClassifierId.magmasInverse Algebra.UnitalMagmas Algebra.inverse :=
  { hostRealization := {}, totalRealization := {} }
noncomputable def additiveRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasAdditive
      Algebra.Magmas Algebra.additive :=
  { hostRealization := magmasRealization, totalRealization := {} }
noncomputable def multiplicativeRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasMultiplicative
      Algebra.Magmas Algebra.multiplicative :=
  { hostRealization := magmasRealization, totalRealization := {} }
noncomputable def divisionRealization :
    ClassifierRealization Algebra.Catalogue.Rings.Rings ClassifierId.ringsDivision
      Algebra.Rings Algebra.divisionOnRings :=
  { hostRealization := { familyFibre := none }, totalRealization := {} }

normalized_registry .classifier
  { id := ClassifierId.magmasAssociative,
    declaration := `LeanCategories.Algebra.associative
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `CasCatalogue.Algebra.CatalogueRegistration.associativeRealization}
normalized_registry .classifier
  { id := ClassifierId.magmasCommutative,
    declaration := `LeanCategories.Algebra.commutative
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `CasCatalogue.Algebra.CatalogueRegistration.commutativeRealization}
normalized_registry .classifier
  { id := ClassifierId.magmasUnital,
    declaration := `LeanCategories.Algebra.unital
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `CasCatalogue.Algebra.CatalogueRegistration.unitalRealization}
normalized_registry .classifier
  { id := ClassifierId.magmasInverse,
    declaration := `LeanCategories.Algebra.inverse
    host := .classifierTotal ClassifierId.magmasUnital
    realization := `CasCatalogue.Algebra.CatalogueRegistration.inverseRealization}
normalized_registry .classifier
  { id := ClassifierId.magmasAdditive,
    declaration := `LeanCategories.Algebra.additive
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `CasCatalogue.Algebra.CatalogueRegistration.additiveRealization}
normalized_registry .classifier
  { id := ClassifierId.magmasMultiplicative,
    declaration := `LeanCategories.Algebra.multiplicative
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `CasCatalogue.Algebra.CatalogueRegistration.multiplicativeRealization}

normalized_registry .category
  { id := CategoryId.magmas,
    declaration := `LeanCategories.Algebra.Magmas
    expression := Algebra.Catalogue.Magmas.Magmas
    realization := `CasCatalogue.Algebra.CatalogueRegistration.magmasRealization}
normalized_registry .category
  { id := CategoryId.semigroups,
    declaration := `LeanCategories.Algebra.Semigroups
    expression := Algebra.Catalogue.Magmas.Semigroups
    realization := `CasCatalogue.Algebra.CatalogueRegistration.semigroupsRealization}
normalized_registry .category
  { id := CategoryId.monoids,
    declaration := `LeanCategories.Algebra.Monoids
    expression := Algebra.Catalogue.Magmas.Monoids
    realization := `CasCatalogue.Algebra.CatalogueRegistration.monoidsRealization}
normalized_registry .category
  { id := CategoryId.groups,
    declaration := `LeanCategories.Algebra.Groups
    expression := Algebra.Catalogue.Magmas.Groups
    realization := `CasCatalogue.Algebra.CatalogueRegistration.groupsRealization}
normalized_registry .category
  { id := CategoryId.additiveMagmas,
    declaration := `LeanCategories.Algebra.AdditiveMagmas
    expression := Algebra.Catalogue.Magmas.AdditiveMagmas
    realization := `CasCatalogue.Algebra.CatalogueRegistration.additiveMagmasRealization}
normalized_registry .category
  { id := CategoryId.additiveSemigroups,
    declaration := `LeanCategories.Algebra.AdditiveSemigroups
    expression := Algebra.Catalogue.Magmas.AdditiveSemigroups
    realization := `CasCatalogue.Algebra.CatalogueRegistration.additiveSemigroupsRealization}
normalized_registry .category
  { id := CategoryId.additiveMonoids,
    declaration := `LeanCategories.Algebra.AdditiveMonoids
    expression := Algebra.Catalogue.Magmas.AdditiveMonoids
    realization := `CasCatalogue.Algebra.CatalogueRegistration.additiveMonoidsRealization}
normalized_registry .category
  { id := CategoryId.additiveGroups,
    declaration := `LeanCategories.Algebra.AdditiveGroups
    expression := Algebra.Catalogue.Magmas.AdditiveGroups
    realization := `CasCatalogue.Algebra.CatalogueRegistration.additiveGroupsRealization}
end CasCatalogue.Algebra.CatalogueRegistration
