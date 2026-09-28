/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Algebra.CatalogueRegistration
public import CasCatalogue.Leaves.Exceptional.CatalogueRegistration
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.MonCat.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Algebra.Catalogue.Magmas
public meta import CasCatalogue.Leaves.Algebra.Catalogue.Rings

@[expose] public section

/-!
# The two operation ports of a ring (#53 §9)

A ring has two structural routes to monoids, and they are different structure:

* the multiplicative port `Ring → Mon` (Mathlib `forget₂ RingCat SemiRingCat ⋙ forget₂ SemiRingCat
  MonCat`), and
* the additive port `Ring → AddGrp → Grp`, where `AddGrpCat.toGrp` reads the additive group
  multiplicatively (Mathlib's `Multiplicative`, `Grp/EquivalenceGroupAddGroup.lean`).

Below monoids both continue `Mon → Semigrp → Magma` by Mathlib's `forget₂`. All rows are
structural: each forgets structure or re-reads it through a Mathlib equivalence of categories.
The routes are *not* identified here: identification needs a registered comparison (CC-COHERE),
and without one a method reached along both is ambiguous (CC-RESOLVE).
-/

open CategoryTheory
open LeanCategories LeanCategories.Algebra
open CasCatalogue.Algebra.Catalogue.Magmas CasCatalogue.Algebra.Catalogue.Rings
open CasCatalogue.Algebra.CatalogueRegistration

namespace CasCatalogue

namespace FunctorId
def ringsMultiplicative : FunctorId := ⟨"fun.rings.multiplicative_monoid"⟩
def ringsAdditive : FunctorId := ⟨"fun.rings.additive_group"⟩
def additiveGroupsToGroups : FunctorId := ⟨"fun.additive_groups.to_groups"⟩
def groupsMonoid : FunctorId := ⟨"fun.groups.monoid"⟩
def monoidsSemigroup : FunctorId := ⟨"fun.monoids.semigroup"⟩
def semigroupsMagma : FunctorId := ⟨"fun.semigroups.magma"⟩
end FunctorId

namespace Algebra.Ports

universe u

def RingsMultiplicativeExpr : FunctorExpr Rings Monoids := .atomic FunctorId.ringsMultiplicative
def RingsAdditiveExpr : FunctorExpr Rings AdditiveGroups := .atomic FunctorId.ringsAdditive
def AdditiveGroupsToGroupsExpr : FunctorExpr AdditiveGroups Groups :=
  .atomic FunctorId.additiveGroupsToGroups
def GroupsMonoidExpr : FunctorExpr Groups Monoids := .atomic FunctorId.groupsMonoid
def MonoidsSemigroupExpr : FunctorExpr Monoids Semigroups := .atomic FunctorId.monoidsSemigroup
def SemigroupsMagmaExpr : FunctorExpr Semigroups Magmas := .atomic FunctorId.semigroupsMagma

/-- The multiplicative monoid of a ring. -/
def ringsMultiplicative : Algebra.Rings.{u} ⟶ Algebra.Monoids.{u} :=
  (forget₂ RingCat SemiRingCat ⋙ forget₂ SemiRingCat MonCat).toCatHom
/-- The additive group of a ring. -/
def ringsAdditive : Algebra.Rings.{u} ⟶ Algebra.AdditiveGroups.{u} :=
  (forget₂ RingCat AddCommGrpCat ⋙ forget₂ AddCommGrpCat AddGrpCat).toCatHom
/-- An additive group read multiplicatively. -/
def additiveGroupsToGroups : Algebra.AdditiveGroups.{u} ⟶ Algebra.Groups.{u} :=
  AddGrpCat.toGrp.toCatHom
def groupsMonoid : Algebra.Groups.{u} ⟶ Algebra.Monoids.{u} := (forget₂ GrpCat MonCat).toCatHom
def monoidsSemigroup : Algebra.Monoids.{u} ⟶ Algebra.Semigroups.{u} :=
  (forget₂ MonCat Semigrp).toCatHom
def semigroupsMagma : Algebra.Semigroups.{u} ⟶ Algebra.Magmas.{u} :=
  (forget₂ Semigrp MagmaCat).toCatHom

noncomputable def ringsMultiplicativeRealization :
    FunctorRealization RingsMultiplicativeExpr Algebra.Rings.{u} Algebra.Monoids.{u}
      ringsMultiplicative.toFunctor :=
  { sourceRealization := ringsRealization, targetRealization := monoidsRealization }
noncomputable def ringsAdditiveRealization :
    FunctorRealization RingsAdditiveExpr Algebra.Rings.{u} Algebra.AdditiveGroups.{u}
      ringsAdditive.toFunctor :=
  { sourceRealization := ringsRealization, targetRealization := additiveGroupsRealization }
noncomputable def additiveGroupsToGroupsRealization :
    FunctorRealization AdditiveGroupsToGroupsExpr Algebra.AdditiveGroups.{u} Algebra.Groups.{u}
      additiveGroupsToGroups.toFunctor :=
  { sourceRealization := additiveGroupsRealization, targetRealization := groupsRealization }
noncomputable def groupsMonoidRealization :
    FunctorRealization GroupsMonoidExpr Algebra.Groups.{u} Algebra.Monoids.{u}
      groupsMonoid.toFunctor :=
  { sourceRealization := groupsRealization, targetRealization := monoidsRealization }
noncomputable def monoidsSemigroupRealization :
    FunctorRealization MonoidsSemigroupExpr Algebra.Monoids.{u} Algebra.Semigroups.{u}
      monoidsSemigroup.toFunctor :=
  { sourceRealization := monoidsRealization, targetRealization := semigroupsRealization }
noncomputable def semigroupsMagmaRealization :
    FunctorRealization SemigroupsMagmaExpr Algebra.Semigroups.{u} Algebra.Magmas.{u}
      semigroupsMagma.toFunctor :=
  { sourceRealization := semigroupsRealization, targetRealization := magmasRealization }

end Algebra.Ports

normalized_registry .functor
  { id := FunctorId.ringsMultiplicative, source := Rings, target := Monoids
    declaration := `CasCatalogue.Algebra.Ports.ringsMultiplicative
    realization := `CasCatalogue.Algebra.Ports.ringsMultiplicativeRealization
    expression := Algebra.Ports.RingsMultiplicativeExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.ringsAdditive, source := Rings, target := AdditiveGroups
    declaration := `CasCatalogue.Algebra.Ports.ringsAdditive
    realization := `CasCatalogue.Algebra.Ports.ringsAdditiveRealization
    expression := Algebra.Ports.RingsAdditiveExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.additiveGroupsToGroups, source := AdditiveGroups, target := Groups
    declaration := `CasCatalogue.Algebra.Ports.additiveGroupsToGroups
    realization := `CasCatalogue.Algebra.Ports.additiveGroupsToGroupsRealization
    expression := Algebra.Ports.AdditiveGroupsToGroupsExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.groupsMonoid, source := Groups, target := Monoids
    declaration := `CasCatalogue.Algebra.Ports.groupsMonoid
    realization := `CasCatalogue.Algebra.Ports.groupsMonoidRealization
    expression := Algebra.Ports.GroupsMonoidExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.monoidsSemigroup, source := Monoids, target := Semigroups
    declaration := `CasCatalogue.Algebra.Ports.monoidsSemigroup
    realization := `CasCatalogue.Algebra.Ports.monoidsSemigroupRealization
    expression := Algebra.Ports.MonoidsSemigroupExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.semigroupsMagma, source := Semigroups, target := Magmas
    declaration := `CasCatalogue.Algebra.Ports.semigroupsMagma
    realization := `CasCatalogue.Algebra.Ports.semigroupsMagmaRealization
    expression := Algebra.Ports.SemigroupsMagmaExpr
    structural := true }

end CasCatalogue
