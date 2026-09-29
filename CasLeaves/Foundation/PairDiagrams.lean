/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasCatalogue.Semantics.Foundation.PairDiagrams
public import CasLeaves.Foundation.Actions
public import Mathlib.CategoryTheory.Functor.Const
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Foundation.PairDiagrams

@[expose] public section

/-!
# Presented pair diagrams of sets

A pair diagram of presented sets is a functor `Discrete WalkingPair ⥤ SetHandles`; it denotes its
composite with the denotation of sets (`whiskeringRight`), which is fully faithful because the
denotation of sets is (`FullyFaithful.whiskeringRight`).

* `Δ` acts by the constant diagram; its square is Mathlib's `Functor.compConstIso`.
* `lim` acts by the product handle `SetHandle.prod`; its square identifies `a × b` with the
  sections of the pair diagram `(a, b)`.
-/

open CategoryTheory Limits
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.PairDiagrams

namespace CasCatalogue.Foundation.PairDiagramActions

/-- Pair diagrams of presented sets. -/
abbrev PairHandles : Type := Discrete WalkingPair ⥤ SetHandles

/-- A pair diagram of handles denotes the pair diagram of the sets they present. -/
def pairDenotation : PairHandles ⥤ pairDiagramsCategory.{0} :=
  (Functor.whiskeringRight _ _ _).obj setDenotation

def pairDenotationFullyFaithful : pairDenotation.FullyFaithful :=
  setDenotationFullyFaithful.whiskeringRight _

/-- `Δ` on presented sets: the constant diagram. -/
def diagonalAction : RealizedAction diagonalDeclaration.{0} setDenotation pairDenotation :=
  ⟨Functor.const _, ⟨(Functor.compConstIso (Discrete WalkingPair) setDenotation).symm⟩⟩

/-- `a × b ≃ sections (a, b)`: a pair is a section of a pair diagram. -/
def pairSections (D : Discrete WalkingPair ⥤ Type) :
    D.obj ⟨.left⟩ × D.obj ⟨.right⟩ ≃ D.sections where
  toFun p := ⟨fun | ⟨.left⟩ => p.1 | ⟨.right⟩ => p.2, fun {j j'} f => by
    rcases j with ⟨a⟩; rcases j' with ⟨b⟩
    obtain rfl : a = b := Discrete.eq_of_hom f
    rcases a <;> simp [Discrete.functor_map_id]⟩
  invFun s := (s.1 ⟨.left⟩, s.1 ⟨.right⟩)
  left_inv _ := rfl
  right_inv s := Subtype.ext <| funext fun | ⟨.left⟩ => rfl | ⟨.right⟩ => rfl

/-- `lim` on presented pair diagrams: the product of the two presented sets. -/
def limitHandles : PairHandles ⥤ SetHandles where
  obj D := .prod (D.obj ⟨.left⟩) (D.obj ⟨.right⟩)
  map φ := InducedCategory.homMk
    (↾(Prod.map (φ.app ⟨.left⟩).hom (φ.app ⟨.right⟩).hom))
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def limitAction : RealizedAction limitDeclaration.{0} pairDenotation setDenotation :=
  ⟨limitHandles, ⟨NatIso.ofComponents (fun D => (pairSections (D ⋙ setDenotation)).toIso)
    fun φ => by
      apply TypeCat.Hom.ext; apply TypeCat.Fun.ext; funext p
      apply Subtype.ext
      funext j
      rcases j with ⟨_ | _⟩ <;> rfl⟩⟩

end CasCatalogue.Foundation.PairDiagramActions

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .realizer
  { id := ⟨"rz.sets.pair_diagrams.presented"⟩, category := CategoryId.setsPairDiagrams
    backend := "lean"
    denotation := `CasCatalogue.Foundation.PairDiagramActions.pairDenotation
    fullyFaithful := some `CasCatalogue.Foundation.PairDiagramActions.pairDenotationFullyFaithful },
  .action
  { id := ⟨"act.sets.pair_diagonal.presented"⟩, edge := .functor FunctorId.setsPairDiagonal
    realization := `CasCatalogue.Foundation.PairDiagramActions.diagonalAction },
  .action
  { id := ⟨"act.sets.pair_limit.presented"⟩, edge := .functor FunctorId.setsPairLimit
    realization := `CasCatalogue.Foundation.PairDiagramActions.limitAction }] }

end CasCatalogue
