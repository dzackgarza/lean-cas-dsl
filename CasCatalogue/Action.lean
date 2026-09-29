/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# Functor actions on realizations (CC-ACTION)

A realization of a category `C` is a category `R` of executable handles together with a functor
`d : R ⥤ C`, its denotation: which object a handle is, which morphism a morphism handle is
(CC-SEP). A realized action of `F : C ⥤ D` is a functor `a : R_C ⥤ R_D` on handles together with a
2-commutative square `a ⋙ d_D ≅ d_C ⋙ F` (Mathlib's `CatCommSq`): executing `a` and then reading
off the meaning agrees with reading off the meaning and then applying `F`, coherently in the
morphisms. Composites are Mathlib's pasting of squares (`CatCommSq.hComp'`); no composite is
registered. Every structure here is Mathlib's; this file only names the pair (functor on handles,
square) that a registry row points to.
-/

open CategoryTheory

namespace CasCatalogue

universe u v u' v' u'' v'' w w' w'' x x' x''

/-- A realized action of `F : C ⥤ D` along the denotations `dC` and `dD`: a functor on handles and
the 2-commutative square `action ⋙ dD ≅ dC ⋙ F`. -/
structure RealizedAction {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {RC : Type w} [Category.{x} RC] {RD : Type w'} [Category.{x'} RD]
    (F : C ⥤ D) (dC : RC ⥤ C) (dD : RD ⥤ D) where
  action : RC ⥤ RD
  square : CatCommSq action dC dD F

namespace RealizedAction

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {RC : Type w} [Category.{x} RC] {RD : Type w'} [Category.{x'} RD]
  {RE : Type w''} [Category.{x''} RE]
  {dC : RC ⥤ C} {dD : RD ⥤ D} {dE : RE ⥤ E} {F : C ⥤ D} {G : D ⥤ E}

/-- The identity action realizes the identity functor (`CatCommSq.hId`). -/
def id (dC : RC ⥤ C) : RealizedAction (𝟭 C) dC dC := ⟨𝟭 RC, CatCommSq.hId dC⟩

/-- The realized action of `F ⋙ G`: the composite functor on handles and the pasted square. -/
def comp (α : RealizedAction F dC dD) (β : RealizedAction G dD dE) :
    RealizedAction (F ⋙ G) dC dE :=
  ⟨α.action ⋙ β.action, CatCommSq.hComp' α.square β.square⟩

/-- The object action on handles. -/
abbrev obj (α : RealizedAction F dC dD) (a : RC) : RD := α.action.obj a

/-- The morphism action on handles. -/
abbrev map (α : RealizedAction F dC dD) {a b : RC} (f : a ⟶ b) : α.obj a ⟶ α.obj b :=
  α.action.map f

/-- The denotation of an image handle is isomorphic to the image of the denotation. -/
def objIso (α : RealizedAction F dC dD) (a : RC) : dD.obj (α.obj a) ≅ F.obj (dC.obj a) :=
  α.square.iso.app a

/-- A realized action of `P ⋙ G` along `dC` is one of `G` along `dC ⋙ P`: the same square,
reassociated (`Functor.associator`). -/
def pull {B : Type u''} [Category.{v''} B] {P : C ⥤ B} {G : B ⥤ D}
    (α : RealizedAction (P ⋙ G) dC dD) : RealizedAction G (dC ⋙ P) dD :=
  ⟨α.action, ⟨α.square.iso ≪≫ (Functor.associator _ _ _).symm⟩⟩

/-- A realized action whose square commutes strictly. -/
def ofEq (action : RC ⥤ RD) (h : action ⋙ dD = dC ⋙ F) : RealizedAction F dC dD :=
  ⟨action, ⟨eqToIso h⟩⟩

section Induced

variable {A : Type w} {B : Type w'} {f : A → C} {g : B → D}

/-- A functor `Φ : C ⥤ D` on handles of induced realizations (`InducedCategory`, handles whose
morphisms are the morphisms of their denotations), given its object action `o` on handles: the
lift of `inducedFunctor f ⋙ Φ` through the fully faithful `inducedFunctor g`. -/
def inducedAction (Φ : C ⥤ D) (o : A → B) (h : ∀ a, g (o a) = Φ.obj (f a)) :
    InducedCategory C f ⥤ InducedCategory D g where
  obj := o
  map {a b} φ := InducedCategory.homMk (eqToHom (h a) ≫ Φ.map φ.hom ≫ eqToHom (h b).symm)
  map_id a := by ext; simp
  map_comp φ ψ := by ext; simp

/-- The realized action of `Φ` between induced realizations; its square commutes strictly. -/
def induced (Φ : C ⥤ D) (o : A → B) (h : ∀ a, g (o a) = Φ.obj (f a)) :
    RealizedAction Φ (inducedFunctor f) (inducedFunctor g) :=
  ofEq (inducedAction Φ o h) (Functor.ext h fun a b φ => by simp [inducedAction])

end Induced

/-- The realized action of `F` on a discrete realization (handles with only identities): the
object action `o`, and the objectwise equalities `h` of the square. -/
def discrete {A : Type w} (dC : Discrete A ⥤ C) (o : A → RD)
    (h : ∀ a, dD.obj (o a) = F.obj (dC.obj ⟨a⟩)) : RealizedAction F dC dD :=
  ⟨Discrete.functor o, ⟨Discrete.natIso fun a => eqToIso (h a.as)⟩⟩

end RealizedAction

end CasCatalogue
