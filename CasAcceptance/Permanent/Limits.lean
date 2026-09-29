/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public import CasCatalogue.LimitCallSyntax
public import CasCatalogue.AcceptanceSyntax
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.LimitCallSyntax
public meta import CasCatalogue.AcceptanceSyntax

@[expose] public section

/-!
# Permanent assertions: registered limits and colimits

The cardinalities of the apexes of registered limits and colimits, through `limit%`, `colimit%`
and `value%`. The diagrams are presented by handles:

* the pullback of `f = [0, 1, 1] : Fin 3 → Fin 2` and `g = [1, 0] : Fin 2 → Fin 2` is
  `{(x, y) | f x = g y} = {(0, 1), (1, 0), (2, 0)}`, with 3 elements (Mathlib
  `Types.pullbackLimitCone`), in sets and in finite sets;
* the coproduct `Fin 2 ⊔ Fin 3` has `2 + 3 = 5` elements (Mathlib `Fintype.card_sum`);
* the discriminant group of `A₂`, the cokernel of `A₂ → A₂^♯`, is `ℤ/3` (Conway–Sloane, *SPLAG*
  ch. 4 §6.1: `A_n^*/A_n ≅ ℤ/(n+1)`).
-/

open CategoryTheory Limits CasCatalogue CasCatalogue.Foundation.Actions
open CasCatalogue.Foundation.Cardinality CasCatalogue.Foundation.FiniteSets
open LeanCategories.Modules.Bilinear.Valued CasCatalogue.Modules.Bilinear.Valued.WForms

namespace CasAcceptance.Permanent.Limits

def f : Fin 3 → Fin 2 := ![0, 1, 1]
def g : Fin 2 → Fin 2 := ![1, 0]

def setHom {a b : ℕ} (h : Fin a → Fin b) : @Quiver.Hom SetHandles _ (.finite a) (.finite b) :=
  InducedCategory.homMk (TypeCat.ofHom h)

def finiteHom {a b : ℕ} (h : Fin a → Fin b) : @Quiver.Hom FiniteHandles _ a b :=
  InducedCategory.homMk (FintypeCat.homMk h)

abbrev twoAndThree : Discrete WalkingPair ⥤ SetHandles :=
  pair (SetHandle.finite 2 : SetHandles) (SetHandle.finite 3)

abbrev G : Fin 2 → Fin 2 → ℤ := ![![2, -1], ![-1, 2]]
abbrev A2 : FreeWForm := ⟨2, .int, G⟩
abbrev A2dual : FreeWForm := ⟨2, .rat, ![![2 / 3, 1 / 3], ![1 / 3, 2 / 3]]⟩

/-- `A₂ → A₂^♯`: `x ↦ G x` on carriers, `ℤ ⊆ ℚ` on values. -/
def toDual : FreeHom A2 A2dual where
  matrix := G
  cast := Int.castRingHom ℚ
  cast_eq := rfl
  preserves x y := by
    change ((∑ i, ∑ j, ((x i * y j : ℤ) : ℤ) * G i j : ℤ) : ℚ) =
      ∑ i, ∑ j, (((∑ k, G i k * x k) * (∑ k, G j k * y k) : ℤ) : ℚ) * A2dual.gram i j
    simp [Fin.sum_univ_two, A2dual]
    ring

#accept "limit.sets.pullback.card"
    from "Mathlib Types.pullbackLimitCone: {(x, y) | f x = g y} = {(0,1), (1,0), (2,0)}" :
  (value% cardinality ((limit% pullback (cospan (setHom f) (setHom g)) in "cat.sets").cone.pt)
    in "cat.sets").as = 3 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "limit.finite_sets.pullback.card"
    from "Mathlib Types.pullbackLimitCone, created by FintypeCat ⥤ Type: 3 pairs" :
  (value% cardinality
    ((limit% pullback (cospan (finiteHom f) (finiteHom g)) in "cat.finite_sets").cone.pt)
    in "cat.finite_sets").as = 3 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "colimit.sets.coproduct.card" from "Mathlib Fintype.card_sum: |Fin 2 ⊔ Fin 3| = 5" :
  (value% cardinality ((colimit% coproduct (twoAndThree) in "cat.sets").cocone.pt)
    in "cat.sets").as = 5 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "colimit.bil_wform.a2_discriminant.card"
    from "Conway–Sloane, SPLAG ch. 4 §6.1: A_2^*/A_2 ≅ ℤ/3" :
  (value% cardinality
    ((colimit% cokernel (parallelPair toDual.handle (InducedCategory.homMk 0))
      in "cat.bil_wform").cocone.pt) in "cat.bil_wform").as = 3 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#acceptance_gaps

end CasAcceptance.Permanent.Limits
