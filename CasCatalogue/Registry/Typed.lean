/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Registry.Entry
public import CasCatalogue.Interpretation

@[expose] public section

/-!
# Typed registry evidence

`Registry.Entry` contains the persistent part of a registry row.  Its
declaration and realization fields are `Name` values because environment
extensions and JSON manifests persist names, not dependent proofs.

This module provides the in-memory part.  A typed row carries an actual
category or functor and its `CategoryRealization` or `FunctorRealization`.
The constructors from `SelectedRealization` are the only route from a
selected semantic model to this evidence.  They do not reconstruct proofs
from names read from JSON.
-/

namespace CasCatalogue
open LeanCategories

universe uObj uHom

open CategoryTheory

/-- A named category row together with its checked semantic denotation. -/
structure TypedCategoryEntry where
  metadata : NamedCategoryEntry
  denotation : EvaluatedCategory.{uObj, uHom} metadata.expression

/-- A named functor row together with its checked semantic denotation. -/
structure TypedFunctorEntry where
  metadata : FunctorEntry
  denotation : EvaluatedFunctor.{uObj, uHom} metadata.expression

namespace TypedCategoryEntry

def id (entry : TypedCategoryEntry) : CategoryId := entry.metadata.id

def declaration (entry : TypedCategoryEntry) : Lean.Name :=
  entry.metadata.declaration

def realization (entry : TypedCategoryEntry) : Lean.Name :=
  entry.metadata.realization

def category (entry : TypedCategoryEntry) : ObjCat.{uObj, uHom} :=
  entry.denotation.category

end TypedCategoryEntry

namespace TypedFunctorEntry

def id (entry : TypedFunctorEntry) : FunctorId := entry.metadata.id

def declaration (entry : TypedFunctorEntry) : Lean.Name :=
  entry.metadata.declaration

def realization (entry : TypedFunctorEntry) : Lean.Name :=
  entry.metadata.realization

def sourceCategory (entry : TypedFunctorEntry) : ObjCat.{uObj, uHom} :=
  entry.denotation.sourceCategory

def targetCategory (entry : TypedFunctorEntry) : ObjCat.{uObj, uHom} :=
  entry.denotation.targetCategory

def functor (entry : TypedFunctorEntry) :
    entry.sourceCategory ⥤ entry.targetCategory := entry.denotation.functor

end TypedFunctorEntry

/-! ## Resolution in a selected model -/

namespace CategoryPrimitive

/-- Every category expression is a primitive expression in the current syntax. -/
def ofExpr : (expression : CategoryExpr) → CategoryPrimitive expression
  | .atom id => .atom id
  | .familyApp family arguments => .familyApp family arguments
  | .familyTotal family => .familyTotal family
  | .construct constructor arguments => .construct constructor arguments
  | .classifierTotal classifier => .classifierTotal classifier
  | .refine base classifier => .refine base classifier
  | .opaque id => .opaque id

end CategoryPrimitive

/-- Resolve a persistent category row in a selected semantic model. -/
noncomputable def SelectedRealization.resolveCategory
    (selected : SelectedRealization)
    (metadata : NamedCategoryEntry) : Option (TypedCategoryEntry.{uObj, uHom}) :=
  match selected.category (CategoryPrimitive.ofExpr metadata.expression) with
  | some denotation => some { metadata := metadata, denotation := denotation }
  | none => none

/-- Resolve a persistent functor row in a selected semantic model. -/
noncomputable def SelectedRealization.resolveFunctor
    (selected : SelectedRealization)
    (metadata : FunctorEntry) : Option (TypedFunctorEntry.{uObj, uHom}) :=
  match evalFunctor selected metadata.expression with
  | some denotation => some { metadata := metadata, denotation := denotation }
  | none => none

/-!
The typed rows retain the persistent identifiers only as metadata.  In
particular, these projections do not claim that a `Name` or a JSON string is
itself a category, functor, or proof.
-/

end CasCatalogue
