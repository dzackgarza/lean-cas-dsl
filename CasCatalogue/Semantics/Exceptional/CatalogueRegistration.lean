module

public import CasCatalogue.Semantics.Algebra.Catalogue.Rings
public import CasCatalogue.Semantics.Algebra.CatalogueRegistration
public import CasCatalogue.Semantics.Foundation.CatalogueRegistration
public import CasCatalogue.Registry.Extension
public import LeanCategories.Exceptional.Mathlib
public import CasCatalogue.Semantics.Foundation.Expressions
public import CasCatalogue.Semantics.Exceptional.Catalogue
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.Exceptional.Catalogue
public meta import CasCatalogue.Semantics.Algebra.Catalogue.Rings
public meta import CasCatalogue.Semantics.Algebra.CatalogueRegistration
public meta import CasCatalogue.Semantics.Foundation.CatalogueRegistration

@[expose] public section

namespace CasCatalogue.Exceptional.CatalogueRegistration
open LeanCategories LeanCategories.Exceptional

open LeanCategories CasCatalogue

universe u

def CrystalsExpr : CategoryExpr := .opaque CategoryId.crystals

noncomputable def m2oRealization :
    CategoryRealization Algebra.Catalogue.Rings.MagmasWithTwoOperations
      Exceptional.Mathlib.MagmasWithTwoOperations := { familyFibre := none }
noncomputable def crystalsRealization :
    CategoryRealization CrystalsExpr Exceptional.Mathlib.Crystals :=
  { familyFibre := none }
noncomputable def distributiveRealization :
    ClassifierRealization Algebra.Catalogue.Rings.MagmasWithTwoOperations
      ClassifierId.m2oDistributive Exceptional.Mathlib.MagmasWithTwoOperations
      Exceptional.Mathlib.distributive :=
  { hostRealization := m2oRealization
    totalRealization := { familyFibre := none } }

def multiplicativePortId : OpaquePortId := ⟨"oport.m2o.multiplicative"⟩
def additivePortId : OpaquePortId := ⟨"oport.m2o.additive"⟩
def crystalsPortId : OpaquePortId := ⟨"oport.crystals.sets"⟩

def multiplicativePortExpr :
    FunctorExpr Algebra.Catalogue.Rings.MagmasWithTwoOperations
      Algebra.Catalogue.Magmas.Magmas := .opaquePort multiplicativePortId
noncomputable def multiplicativePortRealization :
    FunctorRealization multiplicativePortExpr Exceptional.Mathlib.MagmasWithTwoOperations
      Algebra.Magmas Exceptional.Mathlib.multiplicativePort.toFunctor where
  sourceRealization := m2oRealization
  targetRealization := CasCatalogue.Algebra.CatalogueRegistration.magmasRealization

def additivePortExpr :
    FunctorExpr Algebra.Catalogue.Rings.MagmasWithTwoOperations
      Algebra.Catalogue.Magmas.Magmas := .opaquePort additivePortId
noncomputable def additivePortRealization :
    FunctorRealization additivePortExpr Exceptional.Mathlib.MagmasWithTwoOperations
      Algebra.Magmas Exceptional.Mathlib.additivePort.toFunctor where
  sourceRealization := m2oRealization
  targetRealization := CasCatalogue.Algebra.CatalogueRegistration.magmasRealization

def crystalsPortExpr : FunctorExpr CrystalsExpr Foundation.Sets := .opaquePort crystalsPortId
noncomputable def crystalsPortRealization :
    FunctorRealization crystalsPortExpr Exceptional.Mathlib.Crystals Foundation.Mathlib.Sets
      Exceptional.Mathlib.crystalsToSets.toFunctor where
  sourceRealization := crystalsRealization
  targetRealization := CasCatalogue.Foundation.CatalogueRegistration.setsRealization

normalized_registry .category
  { id := CategoryId.magmasWithTwoOperations
    declaration := `LeanCategories.Exceptional.Mathlib.MagmasWithTwoOperations
    expression := Algebra.Catalogue.Rings.MagmasWithTwoOperations
    realization := `CasCatalogue.Exceptional.CatalogueRegistration.m2oRealization}
normalized_registry .category
  { id := CategoryId.crystals,
    declaration := `LeanCategories.Exceptional.Mathlib.Crystals
    expression := CrystalsExpr
    realization := `CasCatalogue.Exceptional.CatalogueRegistration.crystalsRealization}

normalized_registry .classifier
  { id := ClassifierId.m2oDistributive,
    declaration := `LeanCategories.Exceptional.Mathlib.distributive
    host := Algebra.Catalogue.Rings.MagmasWithTwoOperations
    realization := `CasCatalogue.Exceptional.CatalogueRegistration.distributiveRealization}

normalized_registry .opaque
  { id := CategoryId.magmasWithTwoOperations
    declaration := `LeanCategories.Exceptional.Mathlib.MagmasWithTwoOperations
    realization := `CasCatalogue.Exceptional.CatalogueRegistration.m2oRealization
    ports := #[
      { id := multiplicativePortId
        source := Algebra.Catalogue.Rings.MagmasWithTwoOperations
        target := Algebra.Catalogue.Magmas.Magmas
        declaration := `LeanCategories.Exceptional.Mathlib.multiplicativePort
        realization := `CasCatalogue.Exceptional.CatalogueRegistration.multiplicativePortRealization
        provenance := "authored opaque interface" },
      { id := additivePortId
        source := Algebra.Catalogue.Rings.MagmasWithTwoOperations
        target := Algebra.Catalogue.Magmas.Magmas
        declaration := `LeanCategories.Exceptional.Mathlib.additivePort
        realization := `CasCatalogue.Exceptional.CatalogueRegistration.additivePortRealization
        provenance := "authored opaque interface" }]
    reason := "two-operation host; distributivity is a separate classifier"}

normalized_registry .opaque
  { id := CategoryId.crystals
    declaration := `LeanCategories.Exceptional.Mathlib.Crystals
    realization := `CasCatalogue.Exceptional.CatalogueRegistration.crystalsRealization
    ports := #[
      { id := crystalsPortId
        source := CrystalsExpr, target := Foundation.Sets
        declaration := `LeanCategories.Exceptional.Mathlib.crystalsToSets
        realization := `CasCatalogue.Exceptional.CatalogueRegistration.crystalsPortRealization
        provenance := "authored opaque interface" }]
    reason := "exceptional combinatorial host"}

normalized_registry .category
  { id := CategoryId.rings,
    declaration := `LeanCategories.Algebra.Rings
    expression := Algebra.Catalogue.Rings.Rings
    realization := `CasCatalogue.Algebra.CatalogueRegistration.ringsRealization}
normalized_registry .category
  { id := CategoryId.commutativeRings,
    declaration := `LeanCategories.Algebra.CommutativeRings
    expression := Algebra.Catalogue.Rings.CommutativeRings
    realization := `CasCatalogue.Algebra.CatalogueRegistration.commutativeRingsRealization}
normalized_registry .classifier
  { id := ClassifierId.ringsDivision,
    declaration := `LeanCategories.Algebra.divisionOnRings
    host := Algebra.Catalogue.Rings.Rings
    realization := `CasCatalogue.Algebra.CatalogueRegistration.divisionRealization}
normalized_registry .category
  { id := CategoryId.divisionRings,
    declaration := `LeanCategories.Algebra.DivisionRings
    expression := Algebra.Catalogue.Rings.DivisionRings
    realization := `CasCatalogue.Algebra.CatalogueRegistration.divisionRingsRealization}
end CasCatalogue.Exceptional.CatalogueRegistration
