/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Algebra.RingTables
public import CasLeaves.Algebra.Actions
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Algebra.Ports

@[expose] public section

/-!
# The two ports on ring tables

* The multiplicative monoid of a finite commutative ring (`fun.rings.multiplicative_monoid`): the
  multiplication table with its unit.
* The additive group (`fun.rings.additive_group`): the addition table with zero and negation, an
  additive-group table (`AddGroup.ofLeftAxioms`, as for the ring); `AddGrpCat.toGrp` then reads
  it multiplicatively, as a group table.

A ring-table homomorphism is a homomorphism of both tables. With the group, monoid, semigroup and
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

/-- A ring-table homomorphism, on multiplicative monoids. -/
def RingTableHom.toMonoidTableHom {a b : RingTable} (f : RingTableHom a b) :
    MonoidTableHom a.toMonoidTable b.toMonoidTable where
  map := f.map
  map_mul := f.map_mul
  map_one := f.map_one

/-- The multiplicative port, realized on tables. -/
def ringToMonoid :
    RealizedAction (Algebra.Ports.ringsMultiplicative.{0}).toFunctor ringTableDenotation
      monoidDenotation where
  action := { obj := RingTable.toMonoidTable, map := RingTableHom.toMonoidTableHom }
  realizes :=
    { obj := fun _ => rfl
      map := fun _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl }

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

/-- A homomorphism of additive-group tables. -/
structure AddGroupTableHom (a b : AddGroupTable) where
  map : Fin a.size → Fin b.size
  map_add : ∀ x y, map (a.add x y) = b.add (map x) (map y)

/-- The additive homomorphism a table homomorphism denotes. -/
def AddGroupTableHom.hom {a b : AddGroupTable} (f : AddGroupTableHom a b) :
    a.Carrier →+ b.Carrier :=
  AddMonoidHom.mk' (M := a.Carrier) (G := b.Carrier) f.map f.map_add

abbrev additiveGroupRealizer : Realizer := ⟨AddGroupTable, AddGroupTableHom⟩

noncomputable def additiveGroupDenotation :
    Denotation additiveGroupRealizer LeanCategories.Algebra.AdditiveGroups.{0} where
  obj t := AddGrpCat.of t.Carrier
  map f := AddGrpCat.ofHom f.hom

/-- The additive group table of a ring table. -/
def RingTable.toAddGroupTable (t : RingTable) : AddGroupTable :=
  { t with }

/-- A ring-table homomorphism, on additive groups. -/
def RingTableHom.toAddGroupTableHom {a b : RingTable} (f : RingTableHom a b) :
    AddGroupTableHom a.toAddGroupTable b.toAddGroupTable :=
  ⟨f.map, f.map_add⟩

theorem ringToAdditiveGroup_obj (t : RingTable) :
    additiveGroupDenotation.obj t.toAddGroupTable =
      (Algebra.Ports.ringsAdditive.{0}).toFunctor.obj (ringTableDenotation.obj t) := rfl

/-- The additive port, realized on tables. -/
def ringToAdditiveGroup :
    RealizedAction (Algebra.Ports.ringsAdditive.{0}).toFunctor ringTableDenotation
      additiveGroupDenotation where
  action := { obj := RingTable.toAddGroupTable, map := RingTableHom.toAddGroupTableHom }
  realizes :=
    { obj := ringToAdditiveGroup_obj
      map := fun _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl }

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

/-- A morphism of groups agrees with `g` conjugated by object equalities once it does so on
elements. -/
theorem grp_eq_conj {A B C D : GrpCat.{0}} (h₁ : A = B) (h₂ : C = D) (f : A ⟶ C)
    (g : B ⟶ D) (H : ∀ x : A, g (cast (congrArg (fun Z : GrpCat.{0} => (Z : Type)) h₁) x) =
      cast (congrArg (fun Z : GrpCat.{0} => (Z : Type)) h₂) (f x)) :
    f = eqToHom h₁ ≫ g ≫ eqToHom h₂.symm := by
  subst h₁; subst h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact GrpCat.ext fun x => (H x).symm

/-- `AddGrpCat.toGrp`, realized on tables: an additive-group table read multiplicatively. -/
def additiveGroupToGroup :
    RealizedAction (Algebra.Ports.additiveGroupsToGroups.{0}).toFunctor additiveGroupDenotation
      groupDenotation where
  action :=
    { obj := AddGroupTable.toGroupTable
      map := fun f => { map := f.map, map_mul := f.map_add, map_one := f.hom.map_zero } }
  realizes :=
    { obj := additiveGroupToGroup_obj
      map := fun {a b} _ => grp_eq_conj (additiveGroupToGroup_obj a) (additiveGroupToGroup_obj b) _ _
        fun _ => rfl }

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
