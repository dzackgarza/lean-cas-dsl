/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public import CasCatalogue.LimitCallSyntax
public import CasCatalogue.ObjectCallSyntax
public import CasCatalogue.AcceptanceSyntax
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.LimitCallSyntax
public meta import CasCatalogue.ObjectCallSyntax
public meta import CasCatalogue.AcceptanceSyntax

@[expose] public section

/-!
# Permanent assertions through constructors

The assertions of `Permanent/Cardinality` and `Permanent/Limits`, restated with inputs built by
`lean-categories`' named objects (`obj%`), their morphisms taken back along the realizer (`hom%`)
and the registered limits (`limit%`, `colimit%`). The admitted text names no leaf: not a handle
constructor, not a realizer's denotation. The earlier assertions are kept.
-/

open CategoryTheory Limits CasCatalogue CasCatalogue.Foundation.Cardinality
open CasCatalogue.Modules.SageCardinality

namespace CasAcceptance.Permanent.Constructed

def f : Fin 3 → Fin 2 := ![0, 1, 1]
def g : Fin 2 → Fin 2 := ![1, 0]

#accept "obj.card.fin2_times_z3"
    from "Mathlib Fintype.card_prod, Fintype.card_fin, ZMod.card: |Fin 2 × ℤ/3| = 2 · 3" :
  (value% cardinality ((limit% product (pair (obj% "obj.sets.fin" (2) in "cat.sets")
      (obj% "obj.sets.integers_mod" (3) in "cat.sets")) in "cat.sets").cone.pt)
    in "cat.sets").as = 6 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "obj.card.z4_cubed" from "Mathlib Fintype.card_fun, ZMod.card: |(ℤ/n)^k| = n^k" :
  (value% cardinality (obj% "obj.sets.integers_mod_power" (4) (3) in "cat.sets")
    in "cat.sets").as = 64 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "obj.card.z7" from "Mathlib Fintype.card_fun, ZMod.card: |(ℤ/n)^k| = n^k" :
  (value% cardinality (obj% "obj.sets.integers_mod_power" (7) (1) in "cat.sets")
    in "cat.sets").as = 7 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "obj.card.z5_empty_power" from "Mathlib Fintype.card_fun: |X^0| = 1" :
  (value% cardinality (obj% "obj.sets.integers_mod_power" (5) (0) in "cat.sets")
    in "cat.sets").as = 1 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "obj.card.integers" from "Mathlib Cardinal.mk_int: |ℤ| = ℵ₀" :
  (value% cardinality (obj% "obj.sets.integers_mod" (0) in "cat.sets") in "cat.sets").as =
    Cardinal.aleph0 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "obj.finite.integers" from "Mathlib Int.infinite: ℤ is infinite" :
  (ask% is_finite (obj% "obj.sets.integers_mod" (0) in "cat.sets") in "cat.sets").answer =
    some false := by decide +kernel

#accept "obj.finite.fin2_times_z3"
    from "Mathlib Finite.instProd: a product of finite sets is finite" :
  (ask% is_finite ((limit% product (pair (obj% "obj.sets.fin" (2) in "cat.sets")
      (obj% "obj.sets.integers_mod" (3) in "cat.sets")) in "cat.sets").cone.pt)
    in "cat.sets").answer = some true := by decide +kernel

#accept "obj.eq.rev_rev" from "Mathlib Fin.rev_rev: reversing Fin n twice is the identity" :
  (eq% (hom% (TypeCat.ofHom fun i : Fin 3 => i.rev.rev) : (obj% "obj.sets.fin" (3) in "cat.sets")
      ⟶ (obj% "obj.sets.fin" (3) in "cat.sets") in "cat.sets")
    (hom% (𝟙 _) : (obj% "obj.sets.fin" (3) in "cat.sets")
      ⟶ (obj% "obj.sets.fin" (3) in "cat.sets") in "cat.sets") in "cat.sets").answer = some true := by
  decide +kernel

#accept "obj.limit.sets.pullback.card"
    from "Mathlib Types.pullbackLimitCone: {(x, y) | f x = g y} = {(0,1), (1,0), (2,0)}" :
  (value% cardinality ((limit% pullback (cospan
      (hom% (TypeCat.ofHom f) : (obj% "obj.sets.fin" (3) in "cat.sets")
        ⟶ (obj% "obj.sets.fin" (2) in "cat.sets") in "cat.sets")
      (hom% (TypeCat.ofHom g) : (obj% "obj.sets.fin" (2) in "cat.sets")
        ⟶ (obj% "obj.sets.fin" (2) in "cat.sets") in "cat.sets")) in "cat.sets").cone.pt)
    in "cat.sets").as = 3 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "obj.colimit.sets.coproduct.card" from "Mathlib Fintype.card_sum: |Fin 2 ⊔ Fin 3| = 5" :
  (value% cardinality ((colimit% coproduct (pair (obj% "obj.sets.fin" (2) in "cat.sets")
      (obj% "obj.sets.fin" (3) in "cat.sets")) in "cat.sets").cocone.pt) in "cat.sets").as = 5 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept_backend "obj.card.sage.z4_cubed" from "agreement with obj.card.z4_cubed" :
  (sageCardinalityOf 4 3) agrees
    (method% cardinality (obj% "obj.sets.integers_mod_power" (4) (3) in "cat.sets")
      in "cat.sets").as

#acceptance_gaps

end CasAcceptance.Permanent.Constructed
