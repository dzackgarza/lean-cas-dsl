/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Action
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Whiskering

@[expose] public section

/-!
# Limits on realizations (CC-UNIV)

A limit of a registered diagram is Mathlib's: a `LimitCone` (apex, legs, `IsLimit` with its
mediator `IsLimit.lift`). A backend presents the apex: a handle whose denotation it identifies with
the apex. Over a fully faithful realization, that is all a backend supplies; the legs on handles
and every mediator on handles are preimages of Mathlib's, and the result is Mathlib's `LimitCone`
of the diagram of handles (`IsLimit.ofFaithful`, with the realization's explicit preimage, so the
mediators compute). Mathlib's own reflection of limits along fully faithful functors goes through
`Functor.preimage`, a choice, and would not.
-/

open CategoryTheory Limits

namespace CasCatalogue

universe v u v' u' w w'

variable {J : Type w} [Category.{w'} J] {R : Type u} [Category.{v} R] {C : Type u'}
  [Category.{v'} C]

/-- A limit cone of `G`, transported to a diagram `F ≅ G` (`IsLimit.postcomposeInvEquiv`). -/
def limitConeOfIso {F G : J ⥤ C} (α : F ≅ G) (L : LimitCone G) : LimitCone F :=
  ⟨(Cones.postcompose α.inv).obj L.cone, (IsLimit.postcomposeInvEquiv α L.cone).symm L.isLimit⟩

variable {d : R ⥤ C} {D : J ⥤ R}

/-- The realized limit of a diagram of handles `D` over a fully faithful realization `d`: the
apex handle `a`, whose denotation `φ` identifies with the apex of a limit cone `L` of `D ⋙ d`,
with legs the preimages of `φ` followed by the legs of `L`, is a limit cone of `D`. -/
def realizedLimitCone (hd : d.FullyFaithful) (L : LimitCone (D ⋙ d)) (a : R)
    (φ : d.obj a ≅ L.cone.pt) : LimitCone D :=
  let c : Cone D :=
    { pt := a
      π :=
        { app := fun j => hd.preimage (φ.hom ≫ L.cone.π.app j)
          naturality := fun j k f => by
            apply hd.map_injective
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.map_comp, Functor.FullyFaithful.map_preimage, Category.assoc]
            rw [← Functor.comp_map, L.cone.w f] } }
  have hc : IsLimit (d.mapCone c) :=
    IsLimit.ofIsoLimit L.isLimit (Cones.ext φ fun j => by simp [c]).symm
  haveI := hd.faithful
  ⟨c, IsLimit.ofFaithful d hc (fun s => hd.preimage (hc.lift (d.mapCone s))) fun _ => by simp⟩

theorem realizedLimitCone_pt (hd : d.FullyFaithful) (L : LimitCone (D ⋙ d)) (a : R)
    (φ : d.obj a ≅ L.cone.pt) : (realizedLimitCone hd L a φ).cone.pt = a := rfl

/-- The denotation of a leg of the realized limit is the leg of `L` after `φ`. -/
theorem realizedLimitCone_leg (hd : d.FullyFaithful) (L : LimitCone (D ⋙ d)) (a : R)
    (φ : d.obj a ≅ L.cone.pt) (j : J) :
    d.map ((realizedLimitCone hd L a φ).cone.π.app j) = φ.hom ≫ L.cone.π.app j := by
  simp [realizedLimitCone]

/-- The realized limit of `D` computed through an adjunction `Δ ⊣ L`: the apex is the image of `D`
under the realized action of the right adjoint `L`, and the limit cone of `D ⋙ d` is Mathlib's
(`coneOfAdj`, legs the counit, mediators the transposes, `isLimitConeOfAdj`). -/
noncomputable def realizedLimitConeOfAdj (hd : d.FullyFaithful) {L : (J ⥤ C) ⥤ C}
    (adj : Functor.const J ⊣ L) (aL : RealizedAction L ((Functor.whiskeringRight J R C).obj d) d)
    (D : J ⥤ R) : LimitCone D :=
  realizedLimitCone hd ⟨coneOfAdj adj (D ⋙ d), isLimitConeOfAdj adj (D ⋙ d)⟩ (aL.obj D)
    (aL.objIso D)

end CasCatalogue
