/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Algebra.Actions
public import CasCatalogue.ConstructorRegistration
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Algebra.Category.Grp.Limits
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.ConstructorCatalogue
public meta import CasCatalogue.Leaves.Algebra.Catalogue.Magmas

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
open LeanCategories LeanCategories.Algebra CasCatalogue.Algebra.Actions

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

/-! ### Realizations: homomorphisms and embeddings of group tables -/

/-- A homomorphism of group tables. -/
structure HomHandle where
  source : GroupTable
  target : GroupTable
  map : Fin source.size → Fin target.size
  map_mul : ∀ a b, map (source.mul a b) = target.mul (map a) (map b)

/-- The monoid homomorphism a table homomorphism denotes. -/
def HomHandle.hom (h : HomHandle) : h.source.Carrier →* h.target.Carrier :=
  MonoidHom.mk' (M := h.source.Carrier) (G := h.target.Carrier) h.map h.map_mul

/-- An injective homomorphism of group tables: a realization of a subgroup of its target. -/
structure SubgroupHandle extends HomHandle where
  injective : ∀ a b, map a = map b → a = b

abbrev arrowRealizer : Realizer := ⟨HomHandle, fun a b => PLift (a = b)⟩
abbrev subgroupRealizer : Realizer := ⟨SubgroupHandle, fun a b => PLift (a = b)⟩

noncomputable def arrowDenotation : Denotation arrowRealizer arrowsGroupsCategory.{0} where
  obj h := Arrow.mk (GrpCat.ofHom h.hom)
  map h := eqToHom (by cases h.down; rfl)

theorem SubgroupHandle.mono (h : SubgroupHandle) :
    Mono (GrpCat.ofHom h.toHomHandle.hom) :=
  (GrpCat.mono_iff_injective _).mpr fun a b e => h.injective a b e

/-- A subgroup handle denotes the subobject `H ↪ G`: the monomorphism, not just `H`. -/
noncomputable def subgroupDenotation :
    Denotation subgroupRealizer subobjectsGroupsCategory.{0} where
  obj h := ⟨Arrow.mk (GrpCat.ofHom h.toHomHandle.hom), h.mono⟩
  map h := eqToHom (by cases h.down; rfl)

/-- The domain action: a subgroup is its own group table. -/
def domainAction : RealizedAction domainDeclaration.{0} subgroupDenotation groupDenotation where
  action := { obj := fun h => h.source, map := fun h => ⟨by cases h.down; rfl⟩ }
  realizes :=
    { obj := fun _ => rfl
      map := fun h => by
        rcases h with ⟨rfl⟩
        simp only [subgroupDenotation, groupDenotation, eqToHom_refl, Functor.map_id,
          Category.id_comp]
        rfl }

/-- The inclusion action: the retained embedding, as an arrow. -/
def inclusionAction :
    RealizedAction inclusionDeclaration.{0} subgroupDenotation arrowDenotation where
  action := { obj := fun h => h.toHomHandle, map := fun h => ⟨by cases h.down; rfl⟩ }
  realizes :=
    { obj := fun _ => rfl
      map := fun h => by
        rcases h with ⟨rfl⟩
        simp only [subgroupDenotation, arrowDenotation, eqToHom_refl, Functor.map_id,
          Category.id_comp]
        rfl }

/-! ### Decoding a hostile backend subgroup -/

/-- What a messy backend hands back for "the subgroup generated by these elements": generators
that are not closed, a label it asserts, and its method inventory. -/
structure HostileSubgroup where
  ambient : GroupTable
  generators : List (Fin ambient.size)
  claimsAbelian : Bool
  methodNames : List String

/-- One closure step: products, inverses. -/
def closureStep (G : GroupTable) (xs : List (Fin G.size)) : List (Fin G.size) :=
  (xs ++ xs.flatMap (fun a => xs.map (G.mul a)) ++ xs.map G.inv).dedup

/-- The subgroup generated by `gens`, as a list (closed after `G.size` steps). -/
def closure (G : GroupTable) (gens : List (Fin G.size)) : List (Fin G.size) :=
  (List.range G.size).foldl (fun xs _ => closureStep G xs) (G.one :: gens).dedup

/-- Re-index a list of elements of `G` as a table on `Fin k`. -/
def reindex (G : GroupTable) (members : List (Fin G.size)) (hk : 0 < members.length)
    (x : Fin G.size) : Fin members.length :=
  ⟨members.idxOf x % members.length, Nat.mod_lt _ hk⟩

/-- Decode a hostile backend subgroup into a subgroup realization: compute the generated
subgroup, its table and its embedding, and check every law. Only the generators are read; the
backend's label and methods are ignored. Fails (returns `none`) if any law fails. -/
def decode (h : HostileSubgroup) : Option SubgroupHandle :=
  let G := h.ambient
  let members := closure G h.generators
  if hk : 0 < members.length then
    let idx := reindex G members hk
    let elt : Fin members.length → Fin G.size := fun i => members.get i
    let mul : Fin members.length → Fin members.length → Fin members.length :=
      fun i j => idx (G.mul (elt i) (elt j))
    let one := idx G.one
    let inv := fun i => idx (G.inv (elt i))
    if assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c) then
    if one_mul : ∀ a, mul one a = a then
    if mul_one : ∀ a, mul a one = a then
    if inv_mul : ∀ a, mul (inv a) a = one then
    if map_mul : ∀ a b, elt (mul a b) = G.mul (elt a) (elt b) then
    if injective : ∀ a b, elt a = elt b → a = b then
      some { source := { size := members.length, mul, assoc, one, one_mul, mul_one, inv, inv_mul }
             target := G, map := elt, map_mul, injective }
    else none else none else none else none else none else none
  else none

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
normalized_registry .action
  { id := ⟨"act.subobjects_groups.domain.table"⟩, edge := .functor FunctorId.subobjectsGroupsDomain
    realization := `CasCatalogue.Algebra.Subgroups.domainAction }
normalized_registry .action
  { id := ⟨"act.subobjects_groups.inclusion.table"⟩
    edge := .functor FunctorId.subobjectsGroupsInclusion
    realization := `CasCatalogue.Algebra.Subgroups.inclusionAction }

normalized_registry .realizer
  { id := ⟨"rz.subobjects_groups.table"⟩, category := ⟨"cat.subobjects_groups"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Subgroups.subgroupDenotation }
normalized_registry .realizer
  { id := ⟨"rz.arrows_groups.table"⟩, category := ⟨"cat.arrows_groups"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Subgroups.arrowDenotation }

end CasCatalogue
