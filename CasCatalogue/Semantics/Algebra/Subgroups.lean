/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Algebra.CatalogueRegistration
public import CasCatalogue.Semantics.ConstructorRegistration
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Algebra.Category.Grp.Limits
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.ConstructorCatalogue
public meta import CasCatalogue.Semantics.Algebra.Catalogue.Magmas

@[expose] public section

/-!
# Subgroups are subobjects (CC-UNIV)

A subgroup of `G` is an object of `Subobjects(Grp)` (#54 §1): a monomorphism `H ↪ G`, so every
subgroup carries its inclusion. The generic structure is owned here, above every backend:

* `fun.subobjects_groups.domain : Subobjects(Grp) → Grp` sends a subgroup to the group it is; it is
  structural, so a subgroup inherits everything a group has (`cardinality`, `is_commutative`) with
  no declaration of its own;
* `fun.subobjects_groups.inclusion : Subobjects(Grp) → Arr(Grp)` is the full-subcategory inclusion,
  presented as the method `inclusion`: the retained universal datum, never recomputed;
* intersection and inverse image are Mathlib's `Subobject` lattice and pullback on the same
  semantic value (`GrpCat` has pullbacks); no subgroup-specific wrapper exists.

A realization is an embedding of finite group tables. A backend's subgroup — here a deliberately
ill-structured handle: an unclosed generator list, a claimed "abelian" label, a method inventory —
reaches the user only through `decode`, which must produce the inclusion; its label and methods
are ignored (CC-SEP, CC-PROP).
-/

open CategoryTheory
open LeanCategories LeanCategories.Algebra

namespace CasCatalogue

namespace CategoryId
def subobjectsGroups : CategoryId := ⟨"cat.subobjects_groups"⟩
def arrowsGroups : CategoryId := ⟨"cat.arrows_groups"⟩
end CategoryId

namespace FunctorId
def subobjectsGroupsDomain : FunctorId := ⟨"fun.subobjects_groups.domain"⟩
def subobjectsGroupsInclusion : FunctorId := ⟨"fun.subobjects_groups.inclusion"⟩
end FunctorId

namespace Algebra.Subgroups

universe u

def SubobjectsGroups : CategoryExpr :=
  .construct ConstructorId.subobjects #[.category Algebra.Catalogue.Magmas.Groups]
def ArrowsGroups : CategoryExpr :=
  .construct ConstructorId.arrow #[.category Algebra.Catalogue.Magmas.Groups]
def DomainExpr : FunctorExpr SubobjectsGroups Algebra.Catalogue.Magmas.Groups :=
  .atomic FunctorId.subobjectsGroupsDomain
def InclusionExpr : FunctorExpr SubobjectsGroups ArrowsGroups :=
  .atomic FunctorId.subobjectsGroupsInclusion

noncomputable section

def subobjectsGroupsCategory := Constructors.subobjects Algebra.Groups.{u}
def subobjectsGroupsRealization :
    CategoryRealization SubobjectsGroups subobjectsGroupsCategory.{u} := {}
def arrowsGroupsCategory := Constructors.arrow Algebra.Groups.{u}
def arrowsGroupsRealization : CategoryRealization ArrowsGroups arrowsGroupsCategory.{u} := {}

/-- A subgroup is the group it is: the domain of its inclusion. -/
def domainDeclaration : subobjectsGroupsCategory.{u} ⥤ Algebra.Groups.{u} :=
  (Constructors.isMonoArrow Algebra.Groups.{u}).ι ⋙ Arrow.leftFunc
def domainRealization :
    FunctorRealization DomainExpr subobjectsGroupsCategory.{u} Algebra.Groups.{u}
      domainDeclaration :=
  { sourceRealization := subobjectsGroupsRealization
    targetRealization := CasCatalogue.Algebra.CatalogueRegistration.groupsRealization }

/-- A subgroup's inclusion, as an arrow of groups. -/
def inclusionDeclaration : subobjectsGroupsCategory.{u} ⥤ arrowsGroupsCategory.{u} :=
  (Constructors.isMonoArrow Algebra.Groups.{u}).ι
def inclusionRealization :
    FunctorRealization InclusionExpr subobjectsGroupsCategory.{u} arrowsGroupsCategory.{u}
      inclusionDeclaration :=
  { sourceRealization := subobjectsGroupsRealization
    targetRealization := arrowsGroupsRealization }

end

end Algebra.Subgroups

open Algebra.Subgroups

normalized_registry .category
  { id := CategoryId.subobjectsGroups
    declaration := `CasCatalogue.Algebra.Subgroups.subobjectsGroupsCategory
    expression := SubobjectsGroups
    realization := `CasCatalogue.Algebra.Subgroups.subobjectsGroupsRealization }
normalized_registry .category
  { id := CategoryId.arrowsGroups
    declaration := `CasCatalogue.Algebra.Subgroups.arrowsGroupsCategory
    expression := ArrowsGroups
    realization := `CasCatalogue.Algebra.Subgroups.arrowsGroupsRealization }
normalized_registry .functor
  { id := FunctorId.subobjectsGroupsDomain, source := SubobjectsGroups
    target := Algebra.Catalogue.Magmas.Groups
    declaration := `CasCatalogue.Algebra.Subgroups.domainDeclaration
    realization := `CasCatalogue.Algebra.Subgroups.domainRealization
    expression := DomainExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.subobjectsGroupsInclusion, source := SubobjectsGroups, target := ArrowsGroups
    declaration := `CasCatalogue.Algebra.Subgroups.inclusionDeclaration
    realization := `CasCatalogue.Algebra.Subgroups.inclusionRealization
    expression := InclusionExpr }
normalized_registry .method
  { id := ⟨"meth.inclusion"⟩, name := "inclusion", owner := SubobjectsGroups
    functor := FunctorId.subobjectsGroupsInclusion, shape := .object }

end CasCatalogue
