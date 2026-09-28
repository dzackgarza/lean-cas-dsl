/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.OneCat.Universes
public import Mathlib.CategoryTheory.Comma.Arrow
public import LeanCategories.CategoryTheory.OneCat.KernelFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Category

@[expose] public section

/-!
# Semantics of the typed category constructors (#54 §1, CC-CALC)

Each registered constructor denotes one of these Lean definitions, and each is an existing
Mathlib construction: the arrow category (`Arrow`), the core (`Core`), slices and coslices
(`Over`, `Under`), categories of elements (`Functor.Elements`), functor categories, and the
category of subobjects of `C`, the full subcategory of `Arrow C` on monomorphisms with commutative
squares as morphisms (#54 §1). Registration checks that a category built by a constructor is
definitionally its semantics applied to the registered denotations of its arguments.
-/

namespace CasCatalogue.Constructors
open LeanCategories

open CategoryTheory

universe u v w x

/-- `Arr(C)`: the arrow category. -/
def arrow (C : ObjCat.{u, v}) : ObjCat.{max u v, v} := Cat.of (Arrow C)

/-- `Arr(F)`: a functor acts on arrows (Mathlib `Functor.mapArrow`). -/
def arrowMap {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} (F : C ⥤ D) : arrow C ⥤ arrow D :=
  F.mapArrow

/-- `Core(C)`: the maximal subgroupoid. -/
def core (C : ObjCat.{u, v}) : ObjCat.{max u v, v} := Cat.of (Core C)

/-- `Core(F)`: a functor acts on cores (Mathlib `Functor.core`). -/
def coreMap {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} (F : C ⥤ D) : core C ⥤ core D :=
  F.core

/-- `Slice(C, X)`: the category of objects over `X`. -/
def slice (C : ObjCat.{u, v}) (X : C) : ObjCat.{max u v, v} := Cat.of (Over X)

/-- `Coslice(C, X)`: the category of objects under `X`. -/
def coslice (C : ObjCat.{u, v}) (X : C) : ObjCat.{max u v, v} := Cat.of (Under X)

/-- `Elements(U)`: the category of elements of a set-valued functor. -/
def elements (C : ObjCat.{u, v}) (U : C ⥤ Type v) : ObjCat.{max u v, v} :=
  Cat.of U.Elements

/-- The monomorphism property on arrows (owned by `LeanCategories.isMonoArrow`). -/
abbrev isMonoArrow (C : ObjCat.{u, v}) : ObjectProperty (Arrow C) := LeanCategories.isMonoArrow C

/-- `Subobjects(C)`: the full subcategory of `Arr(C)` on monomorphisms. -/
def subobjects (C : ObjCat.{u, v}) : ObjCat.{max u v, v} :=
  Cat.of (isMonoArrow C).FullSubcategory

/-- `Fun(C, D)`: the functor category. -/
def functorCategory (C : ObjCat.{u, v}) (D : ObjCat.{w, x}) :
    ObjCat.{max u v w x, max u v x} :=
  Cat.of (C ⥤ D)

end CasCatalogue.Constructors
