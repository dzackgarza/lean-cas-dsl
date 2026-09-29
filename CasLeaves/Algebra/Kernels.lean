/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Catalogue.Semantics.Limits.Registration
public import CasLeaves.Algebra.Actions
public import Mathlib.Data.List.NodupEquivFin
public meta import CasCatalogue.Leaf

@[expose] public section

/-!
# Kernels of homomorphisms of group tables

The apex of the kernel of `f : G → H` (group tables) is presented as the group table on the
enumerated elements `x` with `f x = 1`, its operations transported from `ker f` along the
indexing bijection (`List.Nodup.getEquivOfForallMemList`), so the table is `ker f` by
construction (`kernelMulEquiv`). That is the whole contribution: the inclusion and every mediator
are the core's (`realizedLimitCone`), preimages of Mathlib's `kernelLimitCone`.
-/

open CategoryTheory Limits
open CasCatalogue.Algebra.Actions

namespace CasCatalogue.Algebra.Kernels

/-- Elements of a table are indices: equality is decidable. -/
instance (t : GroupTable) : DecidableEq t.Carrier := inferInstanceAs (DecidableEq (Fin t.size))

variable {t s : GroupTable} (f : t.Carrier →* s.Carrier)

/-- The elements of `ker f`, in increasing order. -/
def kernelList : List f.ker :=
  ((List.finRange t.size).filter fun x => decide (f x = 1)).attach.map
    fun x => ⟨x.1, MonoidHom.mem_ker.mpr (by simpa using (List.mem_filter.mp x.2).2)⟩

theorem kernelList_nodup : (kernelList f).Nodup := by
  refine List.Nodup.map ?_ (List.nodup_attach.mpr ((List.nodup_finRange _).filter _))
  intro a b h
  apply Subtype.ext
  exact congrArg (fun x : f.ker => (x : t.Carrier)) h

theorem mem_kernelList (x : f.ker) : x ∈ kernelList f := by
  refine List.mem_map.mpr ⟨⟨x.1, ?_⟩, List.mem_attach _ _, rfl⟩
  exact List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true (MonoidHom.mem_ker.mp x.2)⟩

/-- Indexing the enumeration: a bijection onto `ker f`. -/
def kernelEquiv : Fin (kernelList f).length ≃ f.ker :=
  List.Nodup.getEquivOfForallMemList _ (kernelList_nodup f) (mem_kernelList f)

/-- The kernel as a group table, its operations transported from `ker f`. -/
def kernelTable : GroupTable where
  size := (kernelList f).length
  mul i j := (kernelEquiv f).symm (kernelEquiv f i * kernelEquiv f j)
  assoc a b c := by simp [mul_assoc]
  one := (kernelEquiv f).symm 1
  one_mul a := by simp
  mul_one a := by simp
  inv i := (kernelEquiv f).symm (kernelEquiv f i)⁻¹
  inv_mul a := by simp

/-- The kernel table is `ker f`. -/
def kernelMulEquiv : (kernelTable f).Carrier ≃* f.ker :=
  { kernelEquiv f with map_mul' := fun i j => (kernelEquiv f).apply_symm_apply _ }

/-- The apex of the kernel of a homomorphism of group tables, with its identification. -/
def tableKernel (t s : GroupTable) (fh : @Quiver.Hom GroupTables _ t s) :
    Σ a : GroupTables, groupDenotation.obj a ≅
      (Limits.Registration.groupsKernel fh.hom).cone.pt :=
  ⟨kernelTable fh.hom.hom, (kernelMulEquiv fh.hom.hom).toGrpIso⟩

end CasCatalogue.Algebra.Kernels

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .limitRealization
  { id := ⟨"limr.groups.kernel.table"⟩, limit := ⟨"lim.groups.kernel"⟩
    realizer := ⟨"rz.groups.table"⟩
    realization := `CasCatalogue.Algebra.Kernels.tableKernel }] }

end CasCatalogue
