/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Iso

@[expose] public section

/-!
# Lifts of subobjects along a functor (CC-LIFT)

An operation computed on `U(x)` that must return to the source side — a subobject of the
*original* structured object — needs `U` to lift subobjects: for every monomorphism
`i : K ↪ U(X)` an object `X'` over `K` and a map `X' → X` over `i`. These are the cartesian lifts
of monomorphisms (for the forgetful functor of formed modules, restriction of the form). A
`MonoLift U` is that data; a registered `.lift` row supplies it for one route step, and without
one the operation reports the missing lift instead of returning the bare `U`-side result.
-/

open CategoryTheory

namespace CasCatalogue

universe v₁ v₂ u₁ u₂

/-- Lifts of monomorphisms along `U`, up to the canonical isomorphism over the base. -/
structure MonoLift {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (U : C ⥤ D) where
  /-- The lifted object over `K`. -/
  obj : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → C
  /-- Its map to `X`. -/
  hom : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → obj X i ⟶ X
  /-- It lies over `K`. -/
  iso : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → U.obj (obj X i) ≅ K
  /-- Its map lies over `i`. -/
  fac : ∀ (X : C) {K : D} (i : K ⟶ U.obj X) [Mono i], U.map (hom X i) = (iso X i).hom ≫ i

end CasCatalogue
