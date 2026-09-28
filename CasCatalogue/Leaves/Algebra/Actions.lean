/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Algebra.Ports
public import CasCatalogue.Decide
public import CasCatalogue.Leaves.Foundation.Actions
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Algebra.Ports
public meta import CasCatalogue.Leaves.Algebra.Catalogue.Magmas

@[expose] public section

/-!
# Lean-native realizations of finite magmas, semigroups, monoids and groups

A finite magma is realized by its multiplication table on `Fin n`; a semigroup, monoid or group
table adds the unit, inverse and the proofs of their laws, checked once when the table is built
(by `decide`). Morphisms are realized by table homomorphisms (maps preserving the multiplication,
and the unit for monoids and groups). The forgetful functors
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

/-! ### Table homomorphisms -/

/-- A homomorphism of magma tables: a map preserving the multiplication. -/
structure MagmaTableHom (a b : MagmaTable) where
  map : Fin a.size → Fin b.size
  map_mul : ∀ x y, map (a.mul x y) = b.mul (map x) (map y)

/-- The identity homomorphism. -/
def MagmaTableHom.id (a : MagmaTable) : MagmaTableHom a a := ⟨fun x => x, fun _ _ => rfl⟩

/-- The multiplicative map a table homomorphism denotes. -/
def MagmaTableHom.hom {a b : MagmaTable} (f : MagmaTableHom a b) : a.Carrier →ₙ* b.Carrier :=
  ⟨f.map, f.map_mul⟩

/-- A homomorphism of monoid tables: it preserves the multiplication and the unit. -/
structure MonoidTableHom (a b : MonoidTable) extends MagmaTableHom a.toMagmaTable b.toMagmaTable where
  map_one : map a.one = b.one

/-- The identity homomorphism. -/
def MonoidTableHom.id (a : MonoidTable) : MonoidTableHom a a :=
  { MagmaTableHom.id a.toMagmaTable with map_one := rfl }

/-- The monoid homomorphism a table homomorphism denotes. -/
def MonoidTableHom.hom {a b : MonoidTable} (f : MonoidTableHom a b) : a.Carrier →* b.Carrier :=
  ⟨⟨f.map, f.map_one⟩, f.map_mul⟩

/-! ### Realizers: tables and their homomorphisms -/

abbrev magmaRealizer : Realizer := ⟨MagmaTable, MagmaTableHom⟩
abbrev semigroupRealizer : Realizer :=
  ⟨SemigroupTable, fun a b => MagmaTableHom a.toMagmaTable b.toMagmaTable⟩
abbrev monoidRealizer : Realizer := ⟨MonoidTable, MonoidTableHom⟩
abbrev groupRealizer : Realizer :=
  ⟨GroupTable, fun a b => MonoidTableHom a.toMonoidTable b.toMonoidTable⟩

noncomputable def magmaDenotation : Denotation magmaRealizer Algebra.Magmas.{0} where
  obj t := MagmaCat.of t.Carrier
  map f := MagmaCat.ofHom f.hom

noncomputable def semigroupDenotation : Denotation semigroupRealizer Algebra.Semigroups.{0} where
  obj t := Semigrp.of t.Carrier
  map f := Semigrp.ofHom f.hom

noncomputable def monoidDenotation : Denotation monoidRealizer Algebra.Monoids.{0} where
  obj t := MonCat.of t.Carrier
  map f := MonCat.ofHom f.hom

noncomputable def groupDenotation : Denotation groupRealizer Algebra.Groups.{0} where
  obj t := GrpCat.of t.Carrier
  map f := GrpCat.ofHom f.hom

/-! ### The forgetful actions -/

def groupToMonoid :
    RealizedAction (forget₂ GrpCat.{0} MonCat) groupDenotation monoidDenotation where
  action := { obj := GroupTable.toMonoidTable, map := fun f => f }
  realizes :=
    { obj := fun _ => rfl
      map := fun _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl }

def monoidToSemigroup :
    RealizedAction (forget₂ MonCat.{0} Semigrp) monoidDenotation semigroupDenotation where
  action := { obj := MonoidTable.toSemigroupTable, map := fun f => f.toMagmaTableHom }
  realizes :=
    { obj := fun _ => rfl
      map := fun _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl }

def semigroupToMagma :
    RealizedAction (forget₂ Semigrp.{0} MagmaCat) semigroupDenotation magmaDenotation where
  action := { obj := SemigroupTable.toMagmaTable, map := fun f => f }
  realizes :=
    { obj := fun _ => rfl
      map := fun _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl }

/-- The underlying set of a finite magma: the forgetful functor of the binary-operation
classifier, `Magma → Set`, on tables. -/
def magmaToSet : RealizedAction (forget MagmaCat.{0}) magmaDenotation
    CasCatalogue.Foundation.Actions.setDenotation where
  action := { obj := fun t => .finite t.size, map := fun f => f.map }
  realizes :=
    { obj := fun _ => rfl
      map := fun _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl }

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

normalized_registry .action
  { id := ⟨"act.groups.monoid.table"⟩, edge := .functor FunctorId.groupsMonoid
    realization := `CasCatalogue.Algebra.Actions.groupToMonoid }
normalized_registry .action
  { id := ⟨"act.monoids.semigroup.table"⟩, edge := .functor FunctorId.monoidsSemigroup
    realization := `CasCatalogue.Algebra.Actions.monoidToSemigroup }
normalized_registry .action
  { id := ⟨"act.semigroups.magma.table"⟩, edge := .classifierForget ClassifierId.magmasAssociative
    realization := `CasCatalogue.Algebra.Actions.semigroupToMagma }
normalized_registry .action
  { id := ⟨"act.magmas.set.table"⟩, edge := .classifierForget ClassifierId.setsBinaryOperation
    realization := `CasCatalogue.Algebra.Actions.magmaToSet }
normalized_registry .property
  { id := ⟨"prop.is_commutative"⟩, name := "is_commutative"
    classifier := ClassifierId.magmasCommutative }
normalized_registry .property
  { id := ⟨"prop.is_abelian"⟩, name := "is_abelian", classifier := ClassifierId.magmasCommutative
    receiver := some Algebra.Catalogue.Magmas.Groups }
normalized_registry .decider
  { id := ⟨"dec.magmas.commutative.table"⟩, classifier := ClassifierId.magmasCommutative
    realization := `CasCatalogue.Algebra.Actions.commutativeDecider }

normalized_registry .realizer
  { id := ⟨"rz.magmas.table"⟩, category := ⟨"cat.magmas"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Actions.magmaDenotation }
normalized_registry .realizer
  { id := ⟨"rz.semigroups.table"⟩, category := ⟨"cat.semigroups"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Actions.semigroupDenotation }
normalized_registry .realizer
  { id := ⟨"rz.monoids.table"⟩, category := ⟨"cat.monoids"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Actions.monoidDenotation }
normalized_registry .realizer
  { id := ⟨"rz.groups.table"⟩, category := ⟨"cat.groups"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.Actions.groupDenotation }

end CasCatalogue
