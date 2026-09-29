/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public import CasCatalogue.AcceptanceSyntax
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.AcceptanceSyntax

@[expose] public section

/-!
# Permanent assertions: cardinalities and finiteness of presented sets

Admitted assertions are permanent (`CasCatalogue.Acceptance`,
`scripts/check_acceptance_permanent.py`). Each states a value of the language (`value%`, `ask%`,
`eq%`) and cites where its expected value comes from. The inputs are presentations: finite sets
`Fin n`, `ℤ/n` (`ℤ` for `n = 0`), `(ℤ/n)^k`, and products.
-/

open CategoryTheory CasCatalogue CasCatalogue.Foundation.Actions
open CasCatalogue.Foundation.Cardinality CasCatalogue.Foundation.FiniteSets
open CasCatalogue.Modules.SageCardinality

namespace CasAcceptance.Permanent.Cardinality

def fin2TimesZ3 : SetHandles := SetHandle.prod (.finite 2) (.zmod 3)
def z4Cubed : SetHandles := SetHandle.zmodPow 4 3
def z7 : SetHandles := SetHandle.zmodPow 7 1
def z5Empty : SetHandles := SetHandle.zmodPow 5 0
def integers : SetHandles := SetHandle.zmod 0
def threePoints : FiniteHandles := (3 : ℕ)
def fin3 : SetHandles := SetHandle.finite 3
def revRev : fin3 ⟶ fin3 := InducedCategory.homMk (TypeCat.ofHom fun i : Fin 3 => i.rev.rev)

#accept "card.fin2_times_z3"
    from "Mathlib Fintype.card_prod, Fintype.card_fin, ZMod.card: |Fin 2 × ℤ/3| = 2 · 3" :
  (value% cardinality (fin2TimesZ3) in "cat.sets").as = 6 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "card.z4_cubed" from "Mathlib Fintype.card_fun, ZMod.card: |(ℤ/n)^k| = n^k" :
  (value% cardinality (z4Cubed) in "cat.sets").as = 64 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "card.z7" from "Mathlib Fintype.card_fun, ZMod.card: |(ℤ/n)^k| = n^k" :
  (value% cardinality (z7) in "cat.sets").as = 7 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "card.z5_empty_power" from "Mathlib Fintype.card_fun: |X^0| = 1" :
  (value% cardinality (z5Empty) in "cat.sets").as = 1 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "card.integers" from "Mathlib Cardinal.mk_int: |ℤ| = ℵ₀" :
  (value% cardinality (integers) in "cat.sets").as = Cardinal.aleph0 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept "finite.integers" from "Mathlib Int.infinite: ℤ is infinite" :
  (ask% is_finite (integers) in "cat.sets").answer = some false := by decide +kernel

#accept "finite.fin2_times_z3" from "Mathlib Finite.instProd: a product of finite sets is finite" :
  (ask% is_finite (fin2TimesZ3) in "cat.sets").answer = some true := by decide +kernel

#accept "eq.rev_rev" from "Mathlib Fin.rev_rev: reversing Fin n twice is the identity" :
  (eq% (revRev) (𝟙 fin3) in "cat.sets").answer = some true := by decide +kernel

-- No action realizes the forgetful functor on finite sets presented by `n`: a recorded gap.
#accept "card.finite_sets.three" from "Mathlib Fintype.card_fin: |Fin 3| = 3" :
  (value% cardinality (threePoints) in "cat.finite_sets").as = 3 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl

#accept_backend "card.sage.z4_cubed" from "agreement with card.z4_cubed" :
  (sageCardinalityOf 4 3) agrees (method% cardinality (z4Cubed) in "cat.sets").as

#accept_backend "card.sage.z5_empty_power" from "agreement with card.z5_empty_power" :
  (sageCardinalityOf 5 0) agrees (method% cardinality (z5Empty) in "cat.sets").as

#acceptance_gaps

end CasAcceptance.Permanent.Cardinality
