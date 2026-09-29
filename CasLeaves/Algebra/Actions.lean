/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasCatalogue.Semantics.Algebra.Ports
public import CasLeaves.Foundation.Actions
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Algebra.Ports
public meta import CasCatalogue.Semantics.Algebra.Catalogue.Magmas

@[expose] public section

/-!
# Lean-native realizations of finite magmas, semigroups, monoids and groups

A finite magma is realized by its multiplication table on `Fin n`; a semigroup, monoid or group
table adds the unit, inverse and the proofs of their laws, checked once when the table is built
(by `decide`). The handle categories are induced (`InducedCategory`): a morphism of tables is a
morphism of the magmas, semigroups, monoids or groups they denote. The forgetful functors
`Grp → Mon → Semigrp → Magma` act by dropping data; the commutativity classifier on magmas
(`clf.magmas.commutative`) is decided by inspecting the table.

Registered presentations of the one property (CC-PROP):
* `is_commutative`, on any receiver with a structural route to magmas;
* `is_abelian`, the same classifier, available on groups only (#53 §12).
-/

open CategoryTheory
open LeanCategories LeanCategories.Algebra

namespace CasCatalogue.Algebra.Actions

/-- A finite magma, by its multiplication table on `Fin size`. -/
structure MagmaTable where
  size : ℕ
  mul : Fin size → Fin size → Fin size

/-- The carrier of a table. -/
def MagmaTable.Carrier (t : MagmaTable) : Type := Fin t.size

instance (t : MagmaTable) : Mul t.Carrier := ⟨t.mul⟩

/-- An associative table. -/
structure SemigroupTable extends MagmaTable where
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

instance (t : SemigroupTable) : Semigroup t.Carrier where
  mul := t.mul
  mul_assoc := t.assoc

/-- An associative table with a two-sided unit. -/
structure MonoidTable extends SemigroupTable where
  one : Fin size
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a

instance (t : MonoidTable) : Monoid t.Carrier where
  mul := t.mul
  mul_assoc := t.assoc
  one := t.one
  one_mul := t.one_mul
  mul_one := t.mul_one

/-- A group table: a monoid table with left inverses. -/
structure GroupTable extends MonoidTable where
  inv : Fin size → Fin size
  inv_mul : ∀ a, mul (inv a) a = one

instance (t : GroupTable) : Group t.Carrier where
  mul := t.mul
  mul_assoc := t.assoc
  one := t.one
  one_mul := t.one_mul
  mul_one := t.mul_one
  inv := t.inv
  inv_mul_cancel := t.inv_mul

/-! ### Realizations: tables, with the morphisms of their denotations (`InducedCategory`) -/

abbrev MagmaTables : Type := InducedCategory MagmaCat.{0} fun t : MagmaTable => MagmaCat.of t.Carrier
abbrev SemigroupTables : Type :=
  InducedCategory Semigrp.{0} fun t : SemigroupTable => Semigrp.of t.Carrier
abbrev MonoidTables : Type := InducedCategory MonCat.{0} fun t : MonoidTable => MonCat.of t.Carrier
abbrev GroupTables : Type := InducedCategory GrpCat.{0} fun t : GroupTable => GrpCat.of t.Carrier

def magmaDenotation : MagmaTables ⥤ Algebra.Magmas.{0} := inducedFunctor _
def semigroupDenotation : SemigroupTables ⥤ Algebra.Semigroups.{0} := inducedFunctor _
def monoidDenotation : MonoidTables ⥤ Algebra.Monoids.{0} := inducedFunctor _
def groupDenotation : GroupTables ⥤ Algebra.Groups.{0} := inducedFunctor _

/-- Group tables are an induced realization, hence fully faithful. -/
def groupDenotationFullyFaithful : groupDenotation.FullyFaithful :=
  fullyFaithfulInducedFunctor _

/-! ### The forgetful actions -/

def groupToMonoid : RealizedAction (forget₂ GrpCat.{0} MonCat) groupDenotation monoidDenotation :=
  RealizedAction.induced _ GroupTable.toMonoidTable fun _ => rfl

def monoidToSemigroup :
    RealizedAction (forget₂ MonCat.{0} Semigrp) monoidDenotation semigroupDenotation :=
  RealizedAction.induced _ MonoidTable.toSemigroupTable fun _ => rfl

def semigroupToMagma :
    RealizedAction (forget₂ Semigrp.{0} MagmaCat) semigroupDenotation magmaDenotation :=
  RealizedAction.induced _ SemigroupTable.toMagmaTable fun _ => rfl

/-- The underlying set of a finite magma: the forgetful functor of the binary-operation
classifier, `Magma → Set`, on tables. -/
def magmaToSet : RealizedAction (forget MagmaCat.{0}) magmaDenotation
    CasCatalogue.Foundation.Actions.setDenotation :=
  RealizedAction.induced _ (fun t => .finite t.size) fun _ => rfl

/-! ### Deciding commutativity from the table -/

/-- Commutativity of a finite magma, decided by inspecting its table. -/
def commutativeDecider : Decider Algebra.commutative.{0} magmaDenotation where
  decide t :=
    if h : ∀ a b, t.mul a b = t.mul b a then
      .proved ⟨⟨⟨magmaDenotation.obj t, h⟩, rfl⟩⟩
    else
      .refuted fun ⟨⟨y, hy⟩⟩ => h fun a b => by
        have hc : IsCommutativeMagma y.obj := y.property
        change y.obj = magmaDenotation.obj t at hy
        rw [hy] at hc
        exact hc a b

end CasCatalogue.Algebra.Actions

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.groups.monoid.table"⟩, edge := .functor FunctorId.groupsMonoid
    realization := `CasCatalogue.Algebra.Actions.groupToMonoid },
  .action
  { id := ⟨"act.monoids.semigroup.table"⟩, edge := .functor FunctorId.monoidsSemigroup
    realization := `CasCatalogue.Algebra.Actions.monoidToSemigroup },
  .action
  { id := ⟨"act.semigroups.magma.table"⟩, edge := .classifierForget ClassifierId.magmasAssociative
    realization := `CasCatalogue.Algebra.Actions.semigroupToMagma },
  .action
  { id := ⟨"act.magmas.set.table"⟩, edge := .classifierForget ClassifierId.setsBinaryOperation
    realization := `CasCatalogue.Algebra.Actions.magmaToSet },
  .decider
  { id := ⟨"dec.magmas.commutative.table"⟩, classifier := ClassifierId.magmasCommutative
    realization := `CasCatalogue.Algebra.Actions.commutativeDecider },
  .realizer
  { id := ⟨"rz.magmas.table"⟩, category := ⟨"cat.magmas"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Actions.magmaDenotation },
  .realizer
  { id := ⟨"rz.semigroups.table"⟩, category := ⟨"cat.semigroups"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Actions.semigroupDenotation },
  .realizer
  { id := ⟨"rz.monoids.table"⟩, category := ⟨"cat.monoids"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Actions.monoidDenotation },
  .realizer
  { id := ⟨"rz.groups.table"⟩, category := ⟨"cat.groups"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Actions.groupDenotation
    fullyFaithful := some `CasCatalogue.Algebra.Actions.groupDenotationFullyFaithful }] }

end CasCatalogue
