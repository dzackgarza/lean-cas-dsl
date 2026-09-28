/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Algebra.Actions
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Logic.Equiv.Fin.Basic
public import CasCatalogue.Leaves.Algebra.RingTables
public import Mathlib.Algebra.QuadraticAlgebra.Defs
public meta import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# Group tables of finite groups (realizations for the notebook surface)

A finite group `G` with a computable enumeration `e : Fin k ≃ G` is realized by the group table on
`Fin k` transported along `e` (`GroupTable.ofEnum`); the laws are `G`'s, carried by `e`. Instances:

* `cyclicTable n`: the additive group `ℤ/(n+1)`, as the multiplicative group
  `Multiplicative (ZMod (n+1))` (the object of `Groups` the additive group is);
* `zmodRingTable n`: the ring `ℤ/(n+1)`, by `RingTable.ofEnum` for finite commutative rings;
* `quadraticTable n a b`: the ring `(ℤ/(n+1))[ω]/(ω² - bω - a)`, Mathlib's
  `QuadraticAlgebra (ZMod (n+1)) a b`, enumerated `re + (n+1)·im ↦ re + im ω`… (by
  `finProdFinEquiv` and `QuadraticAlgebra.equivProd`);
* `dihedralTable n`: Mathlib's dihedral group `DihedralGroup (n+1)` of order `2(n+1)`, enumerated
  rotations first (`DihedralGroup.equivSum`).
-/

namespace CasCatalogue.Algebra.GroupTables

open CasCatalogue.Algebra.Actions CasCatalogue.Algebra.RingTables

/-- The group table of a finite group along an enumeration of its elements. -/
def GroupTable.ofEnum {G : Type} [Group G] (k : ℕ) (e : Fin k ≃ G) : GroupTable where
  size := k
  mul a b := e.symm (e a * e b)
  assoc a b c := by simp [mul_assoc]
  one := e.symm 1
  one_mul a := by simp
  mul_one a := by simp
  inv a := e.symm (e a)⁻¹
  inv_mul a := by simp

/-- `ℤ/(n+1)` under addition, as a group: its elements are those of `Fin (n+1)`. -/
def cyclicEnum (n : ℕ) : Fin (n + 1) ≃ Multiplicative (ZMod (n + 1)) := Multiplicative.ofAdd

/-- The group table of `ℤ/(n+1)`. -/
def cyclicTable (n : ℕ) : GroupTable := GroupTable.ofEnum (n + 1) (cyclicEnum n)

/-- The dihedral group of order `2(n+1)`, rotations `r i` first, then reflections `sr i`. -/
def dihedralEnum (n : ℕ) : Fin ((n + 1) + (n + 1)) ≃ DihedralGroup (n + 1) :=
  finSumFinEquiv.symm.trans (DihedralGroup.equivSum (n := n + 1)).symm

/-- The group table of the dihedral group of order `2(n+1)`. -/
def dihedralTable (n : ℕ) : GroupTable := GroupTable.ofEnum _ (dihedralEnum n)

/-- The ring table of a finite commutative ring along an enumeration of its elements. -/
def RingTable.ofEnum {R : Type} [CommRing R] (k : ℕ) (e : Fin k ≃ R) : RingTable where
  size := k
  add a b := e.symm (e a + e b)
  mul a b := e.symm (e a * e b)
  zero := e.symm 0
  one := e.symm 1
  neg a := e.symm (-e a)
  add_assoc a b c := by simp [add_assoc]
  zero_add a := by simp
  neg_add_cancel a := by simp
  mul_assoc a b c := by simp [mul_assoc]
  mul_comm a b := by simp [mul_comm]
  one_mul a := by simp
  left_distrib a b c := by simp [mul_add]

/-- The ring table of `ℤ/(n+1)`. -/
def zmodRingTable (n : ℕ) : RingTable := RingTable.ofEnum (R := ZMod (n + 1)) (n + 1) (Equiv.refl _)

/-- `(ℤ/(n+1))[ω]/(ω² - bω - a)` enumerated by `Fin ((n+1)·(n+1))`. -/
def quadraticEnum (n : ℕ) (a b : ZMod (n + 1)) :
    Fin ((n + 1) * (n + 1)) ≃ QuadraticAlgebra (ZMod (n + 1)) a b :=
  finProdFinEquiv.symm.trans (QuadraticAlgebra.equivProd (R := ZMod (n + 1)) a b).symm

/-- The ring table of `(ℤ/(n+1))[ω]/(ω² - bω - a)`. -/
def quadraticTable (n : ℕ) (a b : ZMod (n + 1)) : RingTable :=
  RingTable.ofEnum (R := QuadraticAlgebra (ZMod (n + 1)) a b) _ (quadraticEnum n a b)

/-- The same table, from natural-number parameters (the notebook's handle). -/
def quadraticTableNat (n a b : ℕ) : RingTable := quadraticTable n a b

/-- `𝔽₉ = 𝔽₃[x]/(x² + 1)`: `x² = 2`. -/
abbrev f9x : RingTable := quadraticTableNat 2 2 0
/-- `𝔽₉ = 𝔽₃[y]/(y² + y + 2)`: `y² = 1 + 2y`. -/
abbrev f9y : RingTable := quadraticTableNat 2 1 2

/-- `r + i x ↦ (r + 2i) + i y`, i.e. `x ↦ y + 2` (`(y + 2)² = -1`), on indices. -/
def f9xToYMap (k : Fin 9) : Fin 9 :=
  let z := quadraticEnum 2 2 0 k
  (quadraticEnum 2 1 2).symm ⟨z.re + 2 * z.im, z.im⟩

/-- `r + i y ↦ (r + i) + i x`, i.e. `y ↦ x + 1`, on indices. -/
def f9yToXMap (k : Fin 9) : Fin 9 :=
  let z := quadraticEnum 2 1 2 k
  (quadraticEnum 2 2 0).symm ⟨z.re + z.im, z.im⟩

def f9xToY : RingTableHom f9x f9y :=
  { map := f9xToYMap
    map_add := by unfold f9x f9y quadraticTableNat quadraticTable RingTable.ofEnum; decide
    map_mul := by unfold f9x f9y quadraticTableNat quadraticTable RingTable.ofEnum; decide
    map_one := by unfold f9x f9y quadraticTableNat quadraticTable RingTable.ofEnum; decide
    map_zero := by unfold f9x f9y quadraticTableNat quadraticTable RingTable.ofEnum; decide }

def f9yToX : RingTableHom f9y f9x :=
  { map := f9yToXMap
    map_add := by unfold f9x f9y quadraticTableNat quadraticTable RingTable.ofEnum; decide
    map_mul := by unfold f9x f9y quadraticTableNat quadraticTable RingTable.ofEnum; decide
    map_one := by unfold f9x f9y quadraticTableNat quadraticTable RingTable.ofEnum; decide
    map_zero := by unfold f9x f9y quadraticTableNat quadraticTable RingTable.ofEnum; decide }

/-- The registered isomorphism between the two presentations of `𝔽₉`. -/
def f9xyIso : HandleIso ringTableDenotation f9x f9y where
  hom := f9xToY
  inv := f9yToX
  hom_inv := by
    apply RingCat.hom_ext
    ext k
    exact (show ∀ j : Fin 9, f9yToXMap (f9xToYMap j) = j by decide) k
  inv_hom := by
    apply RingCat.hom_ext
    ext k
    exact (show ∀ j : Fin 9, f9xToYMap (f9yToXMap j) = j by decide) k

end CasCatalogue.Algebra.GroupTables

namespace CasCatalogue

normalized_registry .handleIso
  { id := ⟨"iso.f9.quadratic.x_to_y_plus_2"⟩, realizer := ⟨"rz.rings.table"⟩
    source := `CasCatalogue.Algebra.GroupTables.f9x
    target := `CasCatalogue.Algebra.GroupTables.f9y
    evidence := `CasCatalogue.Algebra.GroupTables.f9xyIso }

end CasCatalogue
