/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Algebra.RingTables
public import CasLeaves.Algebra.Actions
public meta import CasCatalogue.Leaf
public meta import LeanCategories.Catalogue.Semantics.Algebra.Ports

@[expose] public section

/-!
# The two ports on ring tables

* The multiplicative monoid of a finite commutative ring (`fun.rings.multiplicative_monoid`): the
  multiplication table with its unit.
* The additive group (`fun.rings.additive_group`): the addition table with zero and negation, an
  additive-group table (`AddGroup.ofLeftAxioms`, as for the ring); `AddGrpCat.toGrp` then reads
  it multiplicatively, as a group table.

With the group, monoid, semigroup and
magma actions this realizes both routes from rings to sets, which the registered comparison
`cmp.rings.carrier` identifies (CC-COHERE): a ring's cardinality is computed along either.
-/

open CategoryTheory
open CasCatalogue.Algebra.Actions

namespace CasCatalogue.Algebra.RingTables

/-- The multiplicative monoid table of a ring table. -/
def RingTable.toMonoidTable (t : RingTable) : MonoidTable where
  size := t.size
  mul := t.mul
  assoc := t.mul_assoc
  one := t.one
  one_mul := t.one_mul
  mul_one a := (t.mul_comm a t.one).trans (t.one_mul a)

/-- The multiplicative port, realized on tables. -/
def ringToMonoid :
    RealizedAction (Algebra.Ports.ringsMultiplicative.{0}).toFunctor ringTableDenotation
      monoidDenotation :=
  RealizedAction.induced _ RingTable.toMonoidTable fun _ => rfl

/-- A finite additive group, by its addition table on `Fin size`; its `AddGroup` structure is
Mathlib's `AddGroup.ofLeftAxioms`, the one a ring table's additive group has. -/
structure AddGroupTable where
  size : ℕ
  add : Fin size → Fin size → Fin size
  zero : Fin size
  neg : Fin size → Fin size
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  neg_add_cancel : ∀ a, add (neg a) a = zero

/-- The carrier of an additive-group table. -/
def AddGroupTable.Carrier (t : AddGroupTable) : Type := Fin t.size

instance (t : AddGroupTable) : AddGroup t.Carrier :=
  letI : Add t.Carrier := ⟨t.add⟩
  letI : Zero t.Carrier := ⟨t.zero⟩
  letI : Neg t.Carrier := ⟨t.neg⟩
  AddGroup.ofLeftAxioms t.add_assoc t.zero_add t.neg_add_cancel

/-- Additive-group tables, with the homomorphisms of their denotations (`InducedCategory`). -/
abbrev AddGroupTables : Type :=
  InducedCategory AddGrpCat.{0} fun t : AddGroupTable => AddGrpCat.of t.Carrier

def additiveGroupDenotation : AddGroupTables ⥤ LeanCategories.Algebra.AdditiveGroups.{0} :=
  inducedFunctor _

/-- The additive group table of a ring table. -/
def RingTable.toAddGroupTable (t : RingTable) : AddGroupTable :=
  { t with }

theorem ringToAdditiveGroup_obj (t : RingTable) :
    additiveGroupDenotation.obj t.toAddGroupTable =
      (Algebra.Ports.ringsAdditive.{0}).toFunctor.obj (ringTableDenotation.obj t) := rfl

/-- The additive port, realized on tables. -/
def ringToAdditiveGroup :
    RealizedAction (Algebra.Ports.ringsAdditive.{0}).toFunctor ringTableDenotation
      additiveGroupDenotation :=
  RealizedAction.induced _ RingTable.toAddGroupTable ringToAdditiveGroup_obj

/-- The group table of an additive-group table, read multiplicatively. -/
def AddGroupTable.toGroupTable (t : AddGroupTable) : GroupTable where
  size := t.size
  mul := t.add
  assoc := t.add_assoc
  one := t.zero
  one_mul := t.zero_add
  mul_one := add_zero (M := t.Carrier)
  inv := t.neg
  inv_mul := t.neg_add_cancel

/-- The two group structures on the carrier — the table's, and `Multiplicative` of the additive
table's — have the same multiplication, hence are equal (`Group.ext`); they differ definitionally
only in their default powers (`npowRec` against `nsmulRec`). -/
theorem additiveGroupToGroup_obj (t : AddGroupTable) :
    groupDenotation.obj t.toGroupTable =
      (Algebra.Ports.additiveGroupsToGroups.{0}).toFunctor.obj (additiveGroupDenotation.obj t) := by
  have h : (inferInstance : Group t.toGroupTable.Carrier) =
      (Multiplicative.group : Group (Multiplicative t.Carrier)) := Group.ext rfl
  exact congrArg (fun i => @GrpCat.of t.toGroupTable.Carrier i) h

/-- `AddGrpCat.toGrp`, realized on tables: an additive-group table read multiplicatively. -/
def additiveGroupToGroup :
    RealizedAction (Algebra.Ports.additiveGroupsToGroups.{0}).toFunctor additiveGroupDenotation
      groupDenotation :=
  RealizedAction.induced _ AddGroupTable.toGroupTable additiveGroupToGroup_obj

end CasCatalogue.Algebra.RingTables

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.rings.multiplicative_monoid.table"⟩, edge := .functor FunctorId.ringsMultiplicative
    realization := `CasCatalogue.Algebra.RingTables.ringToMonoid },
  .action
  { id := ⟨"act.rings.additive_group.table"⟩, edge := .functor FunctorId.ringsAdditive
    realization := `CasCatalogue.Algebra.RingTables.ringToAdditiveGroup },
  .action
  { id := ⟨"act.additive_groups.to_groups.table"⟩, edge := .functor FunctorId.additiveGroupsToGroups
    realization := `CasCatalogue.Algebra.RingTables.additiveGroupToGroup },
  .realizer
  { id := ⟨"rz.additive_groups.table"⟩, category := ⟨"cat.additive_groups"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.RingTables.additiveGroupDenotation }] }

end CasCatalogue
