module

public import CasCatalogue.Registry.Extension
public import CasCatalogue.Semantics.Foundation.Expressions
public import LeanCategories.Foundation.Mathlib
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.Foundation.Expressions
public meta import CasCatalogue.Semantics.Foundation.Catalogue

@[expose] public section

namespace CasCatalogue.Foundation.CatalogueRegistration
open LeanCategories LeanCategories.Foundation

open CategoryTheory
open LeanCategories CasCatalogue

universe u

noncomputable def setsRealization :
    CategoryRealization Foundation.Sets Foundation.Mathlib.Sets :=
  { familyFibre := none }

noncomputable def finiteRealization :
    ClassifierRealization Foundation.Sets ClassifierId.setsFinite
      Foundation.Mathlib.Sets Foundation.Mathlib.finite :=
  { hostRealization := setsRealization, totalRealization := {} }

noncomputable def gradedRealization :
    ClassifierRealization Foundation.Sets ClassifierId.setsGraded
      Foundation.Mathlib.Sets Foundation.Mathlib.graded :=
  { hostRealization := setsRealization, totalRealization := {} }

noncomputable def binaryOperationRealization :
    ClassifierRealization Foundation.Sets ClassifierId.setsBinaryOperation
      Foundation.Mathlib.Sets Foundation.Mathlib.binaryOperation :=
  { hostRealization := setsRealization, totalRealization := {} }

noncomputable def setsIdentity : Foundation.Mathlib.Sets ⟶ Foundation.Mathlib.Sets :=
  CategoryStruct.id _

def setsIdentityExpr : FunctorExpr Foundation.Sets Foundation.Sets :=
  .identity Foundation.Sets

noncomputable def setsIdentityRealization :
    FunctorRealization setsIdentityExpr Foundation.Mathlib.Sets
      Foundation.Mathlib.Sets setsIdentity.toFunctor :=
  { sourceRealization := setsRealization, targetRealization := setsRealization }

normalized_registry .category
  { id := CategoryId.sets
    declaration := `LeanCategories.Foundation.Mathlib.Sets
    expression := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.setsRealization}

normalized_registry .classifier
  { id := ClassifierId.setsFinite
    declaration := `LeanCategories.Foundation.Mathlib.finite
    host := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.finiteRealization}

normalized_registry .classifier
  { id := ClassifierId.setsGraded
    declaration := `LeanCategories.Foundation.Mathlib.graded
    host := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.gradedRealization}

normalized_registry .classifier
  { id := ClassifierId.setsBinaryOperation
    declaration := `LeanCategories.Foundation.Mathlib.binaryOperation
    host := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.binaryOperationRealization}

normalized_registry .functor
  { id := FunctorId.setsIdentity
    source := Foundation.Sets
    target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.CatalogueRegistration.setsIdentity
    realization := `CasCatalogue.Foundation.CatalogueRegistration.setsIdentityRealization
    expression := setsIdentityExpr }

end CasCatalogue.Foundation.CatalogueRegistration
