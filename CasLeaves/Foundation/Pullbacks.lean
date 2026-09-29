/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Catalogue.Semantics.Limits.Registration
public import CasLeaves.Foundation.Cardinality
public import Mathlib.Data.List.NodupEquivFin
public meta import CasCatalogue.Leaf

@[expose] public section

/-!
# Pullbacks of finite presented sets

The apex of the pullback of `f : Fin m → Fin p` and `g : Fin n → Fin p` is presented as the finite
set `Fin k` of the enumerated pairs `(i, j)` with `f i = g j`; the enumeration has no duplicates
and lists every such pair, so indexing it is a bijection onto Mathlib's explicit pullback
`{(x, y) | f x = g y}` (`List.Nodup.getEquivOfForallMemList`). That is the whole contribution: the
legs and every mediator are the core's (`realizedLimitCone`).
-/

open CategoryTheory Limits
open CasCatalogue.Foundation.Actions

namespace CasCatalogue.Foundation.Pullbacks

variable {m n p : ℕ} (f : Fin m → Fin p) (g : Fin n → Fin p)

/-- The explicit pullback of `f` and `g`: Mathlib's `Types.PullbackObj`, definitionally. -/
abbrev Pairs : Type := {q : Fin m × Fin n // f q.1 = g q.2}

/-- The pairs `(i, j)` with `f i = g j`, in lexicographic order. -/
def pullbackList : List (Pairs f g) :=
  ((List.finRange m ×ˢ List.finRange n).filter fun q => decide (f q.1 = g q.2)).attach.map
    fun q => ⟨q.1, by simpa using (List.mem_filter.mp q.2).2⟩

theorem pullbackList_nodup : (pullbackList f g).Nodup := by
  refine List.Nodup.map ?_ ?_
  · intro a b h
    apply Subtype.ext
    exact congrArg (fun x : Pairs f g => x.val) h
  exact List.nodup_attach.mpr
    (((List.nodup_finRange m).product (List.nodup_finRange n)).filter _)

theorem mem_pullbackList (x : Pairs f g) :
    x ∈ pullbackList f g := by
  refine List.mem_map.mpr ⟨⟨x.1, ?_⟩, List.mem_attach _ _, rfl⟩
  exact List.mem_filter.mpr ⟨List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩,
    decide_eq_true x.2⟩

/-- Indexing the enumeration: a bijection onto the explicit pullback. -/
def pullbackEquiv : Fin (pullbackList f g).length ≃ Pairs f g :=
  List.Nodup.getEquivOfForallMemList _ (pullbackList_nodup f g) (mem_pullbackList f g)

/-- The apex of the pullback of finite presented sets, with its identification. -/
def finitePullback (m n p : ℕ) (f : Fin m → Fin p) (g : Fin n → Fin p) :
    Σ a : SetHandles, setDenotation.obj a ≅
      (Limits.Registration.setsPullback (TypeCat.ofHom f) (TypeCat.ofHom g)).cone.pt :=
  ⟨.finite (pullbackList f g).length, by exact (pullbackEquiv f g).toIso⟩

end CasCatalogue.Foundation.Pullbacks

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .limitRealization
  { id := ⟨"limr.sets.pullback.finite"⟩, limit := ⟨"lim.sets.pullback"⟩
    realizer := ⟨"rz.sets.presented"⟩
    realization := `CasCatalogue.Foundation.Pullbacks.finitePullback }] }

end CasCatalogue
