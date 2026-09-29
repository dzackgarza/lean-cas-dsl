/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.ConstructorRegistration
public import LeanCategories.Foundation.Subsets
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.ConstructorCatalogue

@[expose] public section

/-!
# Subsets and their membership operations

A subset is an object of `Subobjects(Sets)` (`LeanCategories.Foundation.Subsets`). Registered here:

* `fun.sets.whole_subset : Sets → Subobjects(Sets)`, each set as its own largest subset, and
  `fun.subobjects_sets.domain : Subobjects(Sets) → Sets`, a subset as the set it is — both
  structural;
* `contains` and `set_eq`, iso-invariant methods owned by `Subobjects(Sets)`: natural sections of
  predicates on the ambient set (resp. on its subsets), functors
  `Core(Subobjects(Sets)) ⥤ Elements(P)` into the categories of elements of those predicate
  functors.

A set, and anything with an underlying set, reaches `contains` through `whole_subset`; the
argument of `contains` is an element of the ambient set, that of `set_eq` a subset of it.
-/

open CategoryTheory
open LeanCategories LeanCategories.Foundation
open CasCatalogue.Catalogue.ConstructorRegistration

namespace CasCatalogue

namespace CategoryId
def coreSubobjectsSets : CategoryId := ⟨"cat.core_subobjects_sets"⟩
def subsetPredicates : CategoryId := ⟨"cat.subsets.point_predicates"⟩
def subsetSubsetPredicates : CategoryId := ⟨"cat.subsets.subset_predicates"⟩
end CategoryId

namespace FunctorId
def setsWholeSubset : FunctorId := ⟨"fun.sets.whole_subset"⟩
def subobjectsSetsDomain : FunctorId := ⟨"fun.subobjects_sets.domain"⟩
def subsetsPointPredicates : FunctorId := ⟨"fun.subsets.point_predicates"⟩
def subsetsSubsetPredicates : FunctorId := ⟨"fun.subsets.subset_predicates"⟩
def subsetsContains : FunctorId := ⟨"fun.subsets.contains"⟩
def subsetsEquals : FunctorId := ⟨"fun.subsets.set_eq"⟩
end FunctorId

namespace Foundation.Subsets

universe u

def CoreSubobjectsSets : CategoryExpr :=
  .construct ConstructorId.core #[.category Constructed.SubobjectsSets]
def PointPredicates : CategoryExpr :=
  .construct ConstructorId.elements
    #[.category CoreSubobjectsSets, .functor FunctorId.subsetsPointPredicates]
def SubsetPredicates : CategoryExpr :=
  .construct ConstructorId.elements
    #[.category CoreSubobjectsSets, .functor FunctorId.subsetsSubsetPredicates]

def WholeExpr : FunctorExpr Foundation.Sets Constructed.SubobjectsSets :=
  .atomic FunctorId.setsWholeSubset
def DomainExpr : FunctorExpr Constructed.SubobjectsSets Foundation.Sets :=
  .atomic FunctorId.subobjectsSetsDomain
def PointPredicatesExpr : FunctorExpr CoreSubobjectsSets Foundation.Sets :=
  .atomic FunctorId.subsetsPointPredicates
def SubsetPredicatesExpr : FunctorExpr CoreSubobjectsSets Foundation.Sets :=
  .atomic FunctorId.subsetsSubsetPredicates
def ContainsExpr : FunctorExpr CoreSubobjectsSets PointPredicates :=
  .atomic FunctorId.subsetsContains
def EqualsExpr : FunctorExpr CoreSubobjectsSets SubsetPredicates :=
  .atomic FunctorId.subsetsEquals

noncomputable section

def coreSubobjectsSetsCategory := Constructors.core subobjectsSetsCategory.{u}
def coreSubobjectsSetsRealization :
    CategoryRealization CoreSubobjectsSets coreSubobjectsSetsCategory.{u} := {}

def pointPredicatesDeclaration :
    coreSubobjectsSetsCategory.{u} ⥤ LeanCategories.Foundation.Mathlib.Sets.{u} :=
  ambientPredicates
def pointPredicatesRealization :
    FunctorRealization PointPredicatesExpr coreSubobjectsSetsCategory.{u}
      LeanCategories.Foundation.Mathlib.Sets.{u} pointPredicatesDeclaration :=
  { sourceRealization := coreSubobjectsSetsRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

def subsetPredicatesDeclaration :
    coreSubobjectsSetsCategory.{u} ⥤ LeanCategories.Foundation.Mathlib.Sets.{u} :=
  ambientSubsetPredicates
def subsetPredicatesRealization :
    FunctorRealization SubsetPredicatesExpr coreSubobjectsSetsCategory.{u}
      LeanCategories.Foundation.Mathlib.Sets.{u} subsetPredicatesDeclaration :=
  { sourceRealization := coreSubobjectsSetsRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

def pointPredicatesCategory :=
  Constructors.elements coreSubobjectsSetsCategory.{u} pointPredicatesDeclaration.{u}
def pointPredicatesCategoryRealization :
    CategoryRealization PointPredicates pointPredicatesCategory.{u} := {}
def subsetPredicatesCategory :=
  Constructors.elements coreSubobjectsSetsCategory.{u} subsetPredicatesDeclaration.{u}
def subsetPredicatesCategoryRealization :
    CategoryRealization SubsetPredicates subsetPredicatesCategory.{u} := {}

def wholeDeclaration :
    LeanCategories.Foundation.Mathlib.Sets.{u} ⥤ subobjectsSetsCategory.{u} :=
  wholeSubset
def wholeRealization :
    FunctorRealization WholeExpr LeanCategories.Foundation.Mathlib.Sets.{u}
      subobjectsSetsCategory.{u} wholeDeclaration :=
  { sourceRealization := Foundation.CatalogueRegistration.setsRealization
    targetRealization := subobjectsSetsRealization }

def domainDeclaration :
    subobjectsSetsCategory.{u} ⥤ LeanCategories.Foundation.Mathlib.Sets.{u} :=
  subsetCarrier
def domainRealization :
    FunctorRealization DomainExpr subobjectsSetsCategory.{u}
      LeanCategories.Foundation.Mathlib.Sets.{u} domainDeclaration :=
  { sourceRealization := subobjectsSetsRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

def containsDeclaration : coreSubobjectsSetsCategory.{u} ⥤ pointPredicatesCategory.{u} :=
  subsetContains
def containsRealization :
    FunctorRealization ContainsExpr coreSubobjectsSetsCategory.{u} pointPredicatesCategory.{u}
      containsDeclaration :=
  { sourceRealization := coreSubobjectsSetsRealization
    targetRealization := pointPredicatesCategoryRealization }

def equalsDeclaration : coreSubobjectsSetsCategory.{u} ⥤ subsetPredicatesCategory.{u} :=
  subsetEquals
def equalsRealization :
    FunctorRealization EqualsExpr coreSubobjectsSetsCategory.{u} subsetPredicatesCategory.{u}
      equalsDeclaration :=
  { sourceRealization := coreSubobjectsSetsRealization
    targetRealization := subsetPredicatesCategoryRealization }

end

end Foundation.Subsets

open Foundation.Subsets

normalized_registry .category
  { id := CategoryId.coreSubobjectsSets
    declaration := `CasCatalogue.Foundation.Subsets.coreSubobjectsSetsCategory
    expression := CoreSubobjectsSets
    realization := `CasCatalogue.Foundation.Subsets.coreSubobjectsSetsRealization }
normalized_registry .functor
  { id := FunctorId.subsetsPointPredicates, source := CoreSubobjectsSets
    target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.Subsets.pointPredicatesDeclaration
    realization := `CasCatalogue.Foundation.Subsets.pointPredicatesRealization
    expression := PointPredicatesExpr }
normalized_registry .functor
  { id := FunctorId.subsetsSubsetPredicates, source := CoreSubobjectsSets
    target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.Subsets.subsetPredicatesDeclaration
    realization := `CasCatalogue.Foundation.Subsets.subsetPredicatesRealization
    expression := SubsetPredicatesExpr }
normalized_registry .category
  { id := CategoryId.subsetPredicates
    declaration := `CasCatalogue.Foundation.Subsets.pointPredicatesCategory
    expression := PointPredicates
    realization := `CasCatalogue.Foundation.Subsets.pointPredicatesCategoryRealization }
normalized_registry .category
  { id := CategoryId.subsetSubsetPredicates
    declaration := `CasCatalogue.Foundation.Subsets.subsetPredicatesCategory
    expression := SubsetPredicates
    realization := `CasCatalogue.Foundation.Subsets.subsetPredicatesCategoryRealization }
normalized_registry .functor
  { id := FunctorId.setsWholeSubset, source := Foundation.Sets
    target := Constructed.SubobjectsSets
    declaration := `CasCatalogue.Foundation.Subsets.wholeDeclaration
    realization := `CasCatalogue.Foundation.Subsets.wholeRealization
    expression := WholeExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.subobjectsSetsDomain, source := Constructed.SubobjectsSets
    target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.Subsets.domainDeclaration
    realization := `CasCatalogue.Foundation.Subsets.domainRealization
    expression := DomainExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.subsetsContains, source := CoreSubobjectsSets
    target := PointPredicates
    declaration := `CasCatalogue.Foundation.Subsets.containsDeclaration
    realization := `CasCatalogue.Foundation.Subsets.containsRealization
    expression := ContainsExpr }
normalized_registry .functor
  { id := FunctorId.subsetsEquals, source := CoreSubobjectsSets
    target := SubsetPredicates
    declaration := `CasCatalogue.Foundation.Subsets.equalsDeclaration
    realization := `CasCatalogue.Foundation.Subsets.equalsRealization
    expression := EqualsExpr }
normalized_registry .method
  { id := ⟨"meth.contains"⟩, name := "contains", owner := Constructed.SubobjectsSets
    functor := FunctorId.subsetsContains, shape := .isoInvariant }
normalized_registry .method
  { id := ⟨"meth.set_eq"⟩, name := "set_eq", owner := Constructed.SubobjectsSets
    functor := FunctorId.subsetsEquals, shape := .isoInvariant }

end CasCatalogue
