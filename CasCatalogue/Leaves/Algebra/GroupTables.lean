/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Algebra.Actions
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Logic.Equiv.Fin.Basic
public import CasCatalogue.Leaves.Algebra.RingTables

@[expose] public section

/-!
# Group tables of finite groups (realizations for the notebook surface)

A finite group `G` with a computable enumeration `e : Fin k ≃ G` is realized by the group table on
`Fin k` transported along `e` (`GroupTable.ofEnum`); the laws are `G`'s, carried by `e`. Instances:

* `cyclicTable n`: the additive group `ℤ/(n+1)`, as the multiplicative group
  `Multiplicative (ZMod (n+1))` (the object of `Groups` the additive group is);
* `zmodRingTable n`: the ring `ℤ/(n+1)`, by `RingTable.ofEnum` for finite commutative rings;
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

end CasCatalogue.Algebra.GroupTables
