/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public import CasLeaves.Algebra.Products
public import CasLeaves.Foundation.PairDiagrams
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax
public meta import CasLeaves.Algebra.Products
public meta import CasLeaves.Foundation.PairDiagrams

@[expose] public section

/-!
# Acceptance for `cc-lift-faithful` (CC-LIFT; sage-categories D183)

The product `ℤ/2 × ℤ/3` of group tables is computed on elements, as the sections of the pair
diagram (`Δ ⊣ lim` on sets, `constSectionsAdj`), and returned to group tables along the faithful,
non-full functor `tableElements`: the legs and the mediator are the maps of elements, lifted by the
morphism rule. The mediator of the cone `ℤ/6 → ℤ/2, ℤ/6 → ℤ/3` is the Chinese-remainder
isomorphism `x ↦ (x mod 2, x mod 3)`, executed.
-/

open CategoryTheory Limits
open CasCatalogue.Algebra.Actions CasCatalogue.Algebra.Products
open CasCatalogue.Foundation.PairDiagramActions

namespace CasCatalogue.LiftFaithfulProbes

/-- `ℤ/n` by its addition table. -/
def cyclic (n : ℕ) [NeZero n] (h₁ : ∀ a b c : Fin n, a + b + c = a + (b + c))
    (h₂ : ∀ a : Fin n, 0 + a = a) (h₃ : ∀ a : Fin n, a + 0 = a)
    (h₄ : ∀ a : Fin n, -a + a = 0) : GroupTable :=
  { size := n, mul := (· + ·), assoc := h₁, one := 0, one_mul := h₂, mul_one := h₃
    inv := fun a => -a, inv_mul := h₄ }

def z2 : GroupTable := cyclic 2 (by decide) (by decide) (by decide) (by decide)
def z3 : GroupTable := cyclic 3 (by decide) (by decide) (by decide) (by decide)
def z6 : GroupTable := cyclic 6 (by decide) (by decide) (by decide) (by decide)

abbrev D : Discrete WalkingPair ⥤ GroupTables := pair z2 z3

/-- The product of the elements, computed through `Δ ⊣ lim` on sets. -/
noncomputable def L : LimitCone (D ⋙ tableElements) :=
  ⟨coneOfAdj (LeanCategories.Foundation.constSectionsAdj.{0, 0, 0} (Discrete WalkingPair)) _,
    isLimitConeOfAdj _ _⟩

/-- The product table's elements are the pairs. -/
def φ : tableElements.obj (prodTable z2 z3) ≅ L.cone.pt := by
  exact (finProdFinEquiv.symm.trans (pairSections (D ⋙ tableElements))).toIso

/-- The product table, returned to group tables. -/
noncomputable def P : LimitCone D :=
  realizedLiftedLimitCone tableRule L (prodTable z2 z3) φ fun
    | ⟨.left⟩ => ⟨InducedCategory.homMk (GrpCat.ofHom (fst z2 z3)), rfl⟩
    | ⟨.right⟩ => ⟨InducedCategory.homMk (GrpCat.ofHom (snd z2 z3)), rfl⟩

#guard (show GroupTable from exec% P.cone.pt).size == 6
#guard (List.finRange 6).map (fun x => (show Fin 2 from
  (exec% (P.cone.π.app ⟨.left⟩)).hom.hom x)) == [0, 0, 0, 1, 1, 1]
#guard (List.finRange 6).map (fun x => (show Fin 3 from
  (exec% (P.cone.π.app ⟨.right⟩)).hom.hom x)) == [0, 1, 2, 0, 1, 2]


def mod2 : @Quiver.Hom GroupTables _ z6 z2 :=
  InducedCategory.homMk <| GrpCat.ofHom <|
    MonoidHom.mk' (M := z6.Carrier) (G := z2.Carrier) (fun x => Fin.ofNat 2 x.val)
      (show ∀ a b : Fin 6, Fin.ofNat 2 (a + b).val = Fin.ofNat 2 a.val + Fin.ofNat 2 b.val by decide)
def mod3 : @Quiver.Hom GroupTables _ z6 z3 :=
  InducedCategory.homMk <| GrpCat.ofHom <|
    MonoidHom.mk' (M := z6.Carrier) (G := z3.Carrier) (fun x => Fin.ofNat 3 x.val)
      (show ∀ a b : Fin 6, Fin.ofNat 3 (a + b).val = Fin.ofNat 3 a.val + Fin.ofNat 3 b.val by decide)

/-- The competing cone `ℤ/6 → ℤ/2, ℤ/6 → ℤ/3`. -/
noncomputable def s : Cone D := ⟨z6, mapPair mod2 mod3⟩

/-- Its mediator: the Chinese-remainder map, lifted from elements. -/
noncomputable def mediator : @Quiver.Hom GroupTables _ z6 P.cone.pt := P.isLimit.lift s

#guard (List.finRange 6).map (fun x => (show Fin 6 from (exec% mediator).hom.hom x)) ==
  (List.finRange 6).map fun x => finProdFinEquiv (Fin.ofNat 2 x.val, Fin.ofNat 3 x.val)

theorem mediator_fac (j : Discrete WalkingPair) : mediator ≫ P.cone.π.app j = s.π.app j :=
  P.isLimit.fac s j

end CasCatalogue.LiftFaithfulProbes
