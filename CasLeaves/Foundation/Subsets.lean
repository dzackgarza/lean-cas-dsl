/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import CasLeaves.Foundation.Actions
public import LeanCategories.Foundation.Subsets
public import LeanCategories.Catalogue.Semantics.Foundation.Subsets
public meta import CasCatalogue.Leaf
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Semantics.Foundation.Subsets

@[expose] public section

/-!
# Lean-native realizations for `LeanCategories.Catalogue.Semantics.Foundation.Subsets`

The leaf half of `LeanCategories.Catalogue.Semantics.Foundation.Subsets`: handles, their denotations and the actions of the registered functors on
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

/-- Presented subsets, with the morphisms of `Subobjects(Sets)` between their denotations. -/
abbrev SubsetHandles : Type :=
  InducedCategory subobjectsSetsCategory.{0} fun a : SubsetHandle =>
    wholeDeclaration.obj a.ambient.carrier

/-- A whole subset denotes `𝟙 : X ↪ X`. -/
def subsetDenotation : SubsetHandles ⥤ subobjectsSetsCategory.{0} := inducedFunctor _

/-- `whole_subset` on presented sets. -/
def wholeAction : RealizedAction wholeDeclaration.{0} setDenotation subsetDenotation :=
  RealizedAction.induced wholeDeclaration .whole fun _ => rfl

/-- `domain` on presented subsets: a whole subset is its ambient set. -/
def domainAction : RealizedAction domainDeclaration.{0} subsetDenotation setDenotation :=
  RealizedAction.induced domainDeclaration SubsetHandle.ambient fun a => by cases a; rfl

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
