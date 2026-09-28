/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.EqToHom

@[expose] public section

/-!
# Functor actions on realizations (CC-ACTION)

A registered functor `F : C ⥤ D` is its two actions. The semantic functor lives in Mathlib
and has no computational content; execution runs on *realizations* (spec §8):

* a `Realizer` is a type of executable object handles and, for each pair of handles, a type of
  executable morphism handles;
* a `Denotation R C` says which object of `C` a handle is and which morphism of `C` a morphism
  handle is — this is the meaning, kept apart from the handle (CC-SEP);
* an `Action RC RD` is a pair of ordinary Lean functions on handles: the object action and the
  morphism action;
* `Action.Realizes α dC dD F` is the statement that the actions commute with denotation: the
  denotation of `α.obj a` is `F.obj` of the denotation of `a`, and likewise on morphisms up to the
  induced `eqToHom` transports.

`RealizedAction F dC dD` packages an action with that proof. Composition of realized actions is
realized by the composite functor (`RealizedAction.comp`), so a composite's action is formed by
ordinary composition and needs no registration of its own.
-/

open CategoryTheory

namespace CasCatalogue

universe u v u' v' u'' v''

/-- Executable handles for the objects and morphisms of a category. -/
structure Realizer where
  /-- Object handles. -/
  Obj : Type
  /-- Morphism handles between two object handles. -/
  Hom : Obj → Obj → Type

/-- The meaning of a realizer's handles in a category `C`. -/
structure Denotation (R : Realizer) (C : Type u) [Category.{v} C] where
  /-- The object a handle denotes. -/
  obj : R.Obj → C
  /-- The morphism a morphism handle denotes. -/
  map : {a b : R.Obj} → R.Hom a b → (obj a ⟶ obj b)

/-- An executable object action and morphism action between two realizers. -/
structure Action (RC RD : Realizer) where
  /-- The object action on handles. -/
  obj : RC.Obj → RD.Obj
  /-- The morphism action on handles. -/
  map : {a b : RC.Obj} → RC.Hom a b → RD.Hom (obj a) (obj b)

namespace Action

variable {RC RD RE : Realizer}

/-- Apply `α`, then `β`. -/
def comp (α : Action RC RD) (β : Action RD RE) : Action RC RE where
  obj a := β.obj (α.obj a)
  map f := β.map (α.map f)

@[simp] theorem comp_obj (α : Action RC RD) (β : Action RD RE) (a : RC.Obj) :
    (α.comp β).obj a = β.obj (α.obj a) := rfl

@[simp] theorem comp_map (α : Action RC RD) (β : Action RD RE) {a b : RC.Obj}
    (f : RC.Hom a b) : (α.comp β).map f = β.map (α.map f) := rfl

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

/-- The actions of `α` commute with denotation: they realize the functor `F`. -/
structure Realizes (α : Action RC RD) (dC : Denotation RC C) (dD : Denotation RD D)
    (F : C ⥤ D) : Prop where
  obj : ∀ a, dD.obj (α.obj a) = F.obj (dC.obj a)
  map : ∀ {a b : RC.Obj} (f : RC.Hom a b),
    dD.map (α.map f) = eqToHom (obj a) ≫ F.map (dC.map f) ≫ eqToHom (obj b).symm

/-- Realization is closed under composition: `α.comp β` realizes `F ⋙ G`. -/
theorem Realizes.comp {α : Action RC RD} {β : Action RD RE}
    {dC : Denotation RC C} {dD : Denotation RD D} {dE : Denotation RE E}
    {F : C ⥤ D} {G : D ⥤ E} (hα : α.Realizes dC dD F) (hβ : β.Realizes dD dE G) :
    (α.comp β).Realizes dC dE (F ⋙ G) where
  obj a := (hβ.obj (α.obj a)).trans (congrArg G.obj (hα.obj a))
  map f := by
    refine (hβ.map (α.map f)).trans ?_
    rw [hα.map f]
    simp only [Functor.comp_map, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans,
      eqToHom_trans_assoc]
    rfl

end Action

/-- An executable action of `F` on realizations, with the proof that it commutes with denotation.
This is what a registered functor carries (CC-ACTION). -/
structure RealizedAction {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {RC RD : Realizer} (F : C ⥤ D) (dC : Denotation RC C) (dD : Denotation RD D) where
  action : Action RC RD
  realizes : action.Realizes dC dD F

namespace RealizedAction

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {RC RD RE : Realizer}
  {dC : Denotation RC C} {dD : Denotation RD D} {dE : Denotation RE E}
  {F : C ⥤ D} {G : D ⥤ E}

/-- The identity action realizes the identity functor. -/
@[macro_inline] def id (dC : Denotation RC C) : RealizedAction (𝟭 C) dC dC where
  action := { obj := fun a => a, map := fun f => f }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp }

/-- The realized action of a composite functor is the composite of the realized actions.

It is `macro_inline` so that compiled code never receives the denotations, which are meaning
rather than execution and are in general noncomputable. -/
@[macro_inline] def comp (α : RealizedAction F dC dD) (β : RealizedAction G dD dE) :
    RealizedAction (F ⋙ G) dC dE where
  action := α.action.comp β.action
  realizes := α.realizes.comp β.realizes

/-- The object action of a realized action. -/
@[macro_inline, reducible] def obj (α : RealizedAction F dC dD) : RC.Obj → RD.Obj := α.action.obj

/-- The morphism action of a realized action. -/
@[macro_inline, reducible] def map (α : RealizedAction F dC dD) {a b : RC.Obj} (f : RC.Hom a b) :
    RD.Hom (α.obj a) (α.obj b) := α.action.map f

/-- The denotation of the image handle is the image of the denotation. -/
theorem obj_denote (α : RealizedAction F dC dD) (a : RC.Obj) :
    dD.obj (α.obj a) = F.obj (dC.obj a) := α.realizes.obj a

end RealizedAction

end CasCatalogue
