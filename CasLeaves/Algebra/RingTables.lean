/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Catalogue.Semantics.Exceptional.CatalogueRegistration
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.Algebra.Category.Ring.Basic
public meta import CasCatalogue.Leaf

@[expose] public section

/-!
# Finite commutative rings by tables, and presentations of `𝔽₉` (CC-CARRIER)

A finite commutative ring is realized by its addition and multiplication tables on `Fin n`, its
laws checked once when the table is built; a morphism by a table map preserving both operations
and the unit. The denotation is `RingCat.of` the table's carrier.

`𝔽₉` is presented twice, as `𝔽₃[x]/(x² + 1)` and as `𝔽₃[y]/(y² + y + 2)`: an element `a + b t` is
the index `a + 3b`. The two presentations are two different objects of `Ring` with different
carriers' structures; nothing identifies them by what they are "isomorphic to". A registered
isomorphism (`x ↦ y + 2`, since `(y + 2)² = -1` in the second presentation) relates them and
transports elements.

(`𝔽₄` has only one defining polynomial over `𝔽₂` — `x² + x + 1` is the only monic irreducible
quadratic — so the acceptance's "two defining polynomials" is realized with `𝔽₉`.)
-/

open CategoryTheory

namespace CasCatalogue.Algebra.RingTables

/-- A finite commutative ring, by its tables on `Fin size`. -/
structure RingTable where
  size : ℕ
  add : Fin size → Fin size → Fin size
  mul : Fin size → Fin size → Fin size
  zero : Fin size
  one : Fin size
  neg : Fin size → Fin size
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  neg_add_cancel : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

/-- The carrier of a ring table. -/
def RingTable.Carrier (t : RingTable) : Type := Fin t.size

instance (t : RingTable) : CommRing t.Carrier :=
  letI : Add t.Carrier := ⟨t.add⟩
  letI : Mul t.Carrier := ⟨t.mul⟩
  letI : Neg t.Carrier := ⟨t.neg⟩
  letI : Zero t.Carrier := ⟨t.zero⟩
  letI : One t.Carrier := ⟨t.one⟩
  CommRing.ofMinimalAxioms t.add_assoc t.zero_add t.neg_add_cancel t.mul_assoc t.mul_comm
    t.one_mul t.left_distrib

/-- A ring homomorphism of tables. -/
structure RingTableHom (a b : RingTable) where
  map : Fin a.size → Fin b.size
  map_add : ∀ x y, map (a.add x y) = b.add (map x) (map y)
  map_mul : ∀ x y, map (a.mul x y) = b.mul (map x) (map y)
  map_one : map a.one = b.one
  map_zero : map a.zero = b.zero

/-- The ring homomorphism a table map denotes. -/
def RingTableHom.hom {a b : RingTable} (f : RingTableHom a b) : a.Carrier →+* b.Carrier where
  toFun := f.map
  map_one' := f.map_one
  map_mul' := f.map_mul
  map_zero' := f.map_zero
  map_add' := f.map_add

/-- Ring tables, with the ring homomorphisms between their denotations (`InducedCategory`). -/
abbrev RingTables : Type := InducedCategory RingCat.{0} fun t : RingTable => RingCat.of t.Carrier

/-- A ring table denotes a ring. -/
def ringTableDenotation : RingTables ⥤ LeanCategories.Algebra.Rings.{0} := inducedFunctor _

/-- The elements of a ring table: its underlying set. -/
instance : ElementAction RingTables := ⟨inducedFunctor _ ⋙ forget RingCat⟩

/-- The morphism handle of a table homomorphism. -/
def RingTableHom.toHandle {a b : RingTable} (f : RingTableHom a b) :
    @Quiver.Hom RingTables _ a b :=
  InducedCategory.homMk (RingCat.ofHom f.hom)

/-- `𝔽₃[t]/(t² - c₁ t - c₀)` on `a + 3b ↦ a + b t`. -/
def quadraticMul (c₁ c₀ : ℕ) (x y : Fin 9) : Fin 9 :=
  let a := x.val % 3; let b := x.val / 3; let c := y.val % 3; let d := y.val / 3
  ⟨((a * c + b * d * c₀) % 3) + 3 * ((a * d + b * c + b * d * c₁) % 3), by omega⟩

def quadraticAdd (x y : Fin 9) : Fin 9 :=
  ⟨((x.val % 3 + y.val % 3) % 3) + 3 * ((x.val / 3 + y.val / 3) % 3), by omega⟩

def quadraticNeg (x : Fin 9) : Fin 9 :=
  ⟨((3 - x.val % 3) % 3) + 3 * ((3 - x.val / 3) % 3), by omega⟩

/-- `𝔽₉ = 𝔽₃[x]/(x² + 1)`: `x² = 2`. -/
abbrev f9a : RingTable :=
  { size := 9, add := quadraticAdd, mul := quadraticMul 0 2, zero := 0, one := 1
    neg := quadraticNeg, add_assoc := by decide, zero_add := by decide
    neg_add_cancel := by decide, mul_assoc := by decide, mul_comm := by decide
    one_mul := by decide, left_distrib := by decide }

/-- `𝔽₉ = 𝔽₃[y]/(y² + y + 2)`: `y² = 2y + 1`. -/
abbrev f9b : RingTable :=
  { size := 9, add := quadraticAdd, mul := quadraticMul 2 1, zero := 0, one := 1
    neg := quadraticNeg, add_assoc := by decide, zero_add := by decide
    neg_add_cancel := by decide, mul_assoc := by decide, mul_comm := by decide
    one_mul := by decide, left_distrib := by decide }

/-- `x ↦ y + 2` on indices: `a + b x ↦ (a + 2b) + b y`. -/
def f9aToBMap (x : Fin 9) : Fin 9 :=
  ⟨((x.val % 3 + 2 * (x.val / 3)) % 3) + 3 * (x.val / 3), by omega⟩

/-- `y ↦ x + 1` on indices: `a + b y ↦ (a + b) + b x`. -/
def f9bToAMap (x : Fin 9) : Fin 9 :=
  ⟨((x.val % 3 + x.val / 3) % 3) + 3 * (x.val / 3), by omega⟩

/-- `x ↦ y + 2`. -/
def f9aToB : RingTableHom f9a f9b :=
  { map := f9aToBMap
    map_add := by decide, map_mul := by decide, map_one := by decide, map_zero := by decide }

/-- `y ↦ x + 1`, its inverse. -/
def f9bToA : RingTableHom f9b f9a :=
  { map := f9bToAMap
    map_add := by decide, map_mul := by decide, map_one := by decide, map_zero := by decide }

/-- The registered isomorphism between the two presentations. -/
def f9Iso : @Iso RingTables _ f9a f9b where
  hom := f9aToB.toHandle
  inv := f9bToA.toHandle
  hom_inv_id := by
    apply InducedCategory.hom_ext
    apply RingCat.hom_ext
    ext x
    exact (show ∀ y : Fin 9, f9bToAMap (f9aToBMap y) = y by decide) x
  inv_hom_id := by
    apply InducedCategory.hom_ext
    apply RingCat.hom_ext
    ext x
    exact (show ∀ y : Fin 9, f9aToBMap (f9bToAMap y) = y by decide) x

end CasCatalogue.Algebra.RingTables

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .realizer
  { id := ⟨"rz.rings.table"⟩, category := ⟨"cat.rings"⟩, backend := "lean"
    denotation := `CasCatalogue.Algebra.RingTables.ringTableDenotation },
  .isomorphism
  { id := ⟨"iso.f9.x_to_y_plus_2"⟩, realizer := ⟨"rz.rings.table"⟩
    source := `CasCatalogue.Algebra.RingTables.f9a
    target := `CasCatalogue.Algebra.RingTables.f9b
    evidence := `CasCatalogue.Algebra.RingTables.f9Iso }] }

end CasCatalogue
