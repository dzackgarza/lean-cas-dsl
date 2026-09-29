/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Algebra.Actions
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Products of group tables, returned from sets

The forgetful functor from group tables to their elements, `groupDenotation ⋙ forget`, is faithful
and not full. Its morphism rule (sage-categories D183): a map of elements that is the image of a
homomorphism is that homomorphism (`MonoidHom.mk'`, multiplicativity from the image). The leaf
presents the product table on `Fin (m · n)` (`finProdFinEquiv`) and identifies its elements with
the pairs; the core lifts legs and mediators computed on elements (`realizedLiftedLimitCone`).
-/

open CategoryTheory
open CasCatalogue.Algebra.Actions

namespace CasCatalogue.Algebra.Products

/-- The elements of a group table: the denotation followed by Mathlib's forgetful functor. -/
abbrev tableElements : GroupTables ⥤ Type :=
  (inducedFunctor fun t : GroupTable => GrpCat.of t.Carrier) ⋙ forget GrpCat

/-- The morphism rule of `tableElements`. -/
def tableRule : MorphismRule tableElements where
  lift {X Y} g h := InducedCategory.homMk <| GrpCat.ofHom <|
    MonoidHom.mk' (M := X.Carrier) (G := Y.Carrier) (fun x => g x) <| by
      obtain ⟨f, hf⟩ := h
      intro a b
      rw [← hf]
      exact map_mul f.hom.hom a b
  map_lift _ _ := rfl

/-- `G × H` as a table on `Fin (|G| · |H|)`. -/
def prodTable (G H : GroupTable) : GroupTable where
  size := G.size * H.size
  mul a b := finProdFinEquiv
    (G.mul (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1,
      H.mul (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm b).2)
  assoc a b c := by simp [G.assoc, H.assoc]
  one := finProdFinEquiv (G.one, H.one)
  one_mul a := by
    simp only [Equiv.symm_apply_apply, G.one_mul, H.one_mul, Prod.mk.eta, Equiv.apply_symm_apply]
  mul_one a := by
    simp only [Equiv.symm_apply_apply, G.mul_one, H.mul_one, Prod.mk.eta, Equiv.apply_symm_apply]
  inv a := finProdFinEquiv (G.inv (finProdFinEquiv.symm a).1, H.inv (finProdFinEquiv.symm a).2)
  inv_mul a := by simp [G.inv_mul, H.inv_mul]

/-- The first projection of the product table. -/
def fst (G H : GroupTable) : (prodTable G H).Carrier →* G.Carrier :=
  MonoidHom.mk' (fun a => (finProdFinEquiv.symm a).1) fun a b => by
    change (finProdFinEquiv.symm (finProdFinEquiv _)).1 = _
    simp; rfl

/-- The second projection of the product table. -/
def snd (G H : GroupTable) : (prodTable G H).Carrier →* H.Carrier :=
  MonoidHom.mk' (fun a => (finProdFinEquiv.symm a).2) fun a b => by
    change (finProdFinEquiv.symm (finProdFinEquiv _)).2 = _
    simp; rfl

end CasCatalogue.Algebra.Products
