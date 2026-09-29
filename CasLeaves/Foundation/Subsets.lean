/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasCatalogue.Semantics.ConstructorRegistration
public import CasLeaves.Foundation.Actions
public import LeanCategories.Foundation.Subsets
public import CasCatalogue.Semantics.Foundation.Subsets
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.ConstructorCatalogue
public meta import CasCatalogue.Semantics.Foundation.Subsets

@[expose] public section

/-!
# Lean-native realizations for `CasCatalogue.Semantics.Foundation.Subsets`

The leaf half of `CasCatalogue.Semantics.Foundation.Subsets`: handles, their denotations and the actions of the registered functors on
them, contributed through `register_leaf`.
-/

open CategoryTheory
open LeanCategories LeanCategories.Foundation CasCatalogue.Foundation.Actions
open CasCatalogue.Catalogue.ConstructorRegistration

namespace CasCatalogue

namespace Foundation.Subsets

universe u

/-! ### Lean-native realization of whole subsets -/

/-- Presented subsets: for now, a presented set as its own largest subset. A morphism handle is a
function of ambient sets (for whole subsets every function maps the subset into the subset). -/
inductive SubsetHandle
  | whole (ambient : SetHandle)
  deriving DecidableEq, Repr

/-- The ambient set of a presented subset. -/
abbrev SubsetHandle.ambient : SubsetHandle → SetHandle
  | .whole X => X

abbrev subsetRealizer : Realizer := ⟨SubsetHandle, fun a b => a.ambient.carrier → b.ambient.carrier⟩

/-- A whole subset denotes `𝟙 : X ↪ X`. -/
noncomputable def subsetDenotation : Denotation subsetRealizer subobjectsSetsCategory.{0} where
  obj a := match a with
    | .whole X => wholeDeclaration.obj X.carrier
  map {a b} f := match a, b, f with
    | .whole _, .whole _, f => wholeDeclaration.map (TypeCat.ofHom f)

/-- `whole_subset` on presented sets. -/
def wholeAction : RealizedAction wholeDeclaration.{0} setDenotation subsetDenotation where
  action := { obj := .whole, map := fun f => f }
  realizes := { obj := fun _ => rfl, map := fun _ => by simp; rfl }

/-- `domain` on presented subsets: a whole subset is its ambient set. -/
def domainAction : RealizedAction domainDeclaration.{0} subsetDenotation setDenotation where
  action := { obj := SubsetHandle.ambient, map := fun {a b} f => match a, b, f with
    | .whole _, .whole _, f => f }
  realizes :=
    { obj := fun a => by cases a; rfl
      map := fun {a b} f => by cases a; cases b; simp; rfl }

end Foundation.Subsets

open Foundation.Subsets

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.sets.whole_subset.presented"⟩, edge := .functor FunctorId.setsWholeSubset
    realization := `CasCatalogue.Foundation.Subsets.wholeAction },
  .action
  { id := ⟨"act.subobjects_sets.domain.presented"⟩, edge := .functor FunctorId.subobjectsSetsDomain
    realization := `CasCatalogue.Foundation.Subsets.domainAction },
  .realizer
  { id := ⟨"rz.subobjects_sets.presented"⟩, category := CategoryId.subobjectsSets
    backend := "lean", denotation := `CasCatalogue.Foundation.Subsets.subsetDenotation }] }

end CasCatalogue
