/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Realization
public import Mathlib.CategoryTheory.Functor.Category

@[expose] public section

/-!
# Interpretation of typed catalogue expressions

This module evaluates the typed syntax in Catalogue.Syntax in one selected
semantic realization. Primitive entries carry the existing
CategoryRealization and FunctorRealization witnesses. Composition is then
performed by Mathlib's category-theory operations, after checking that the
selected endpoint denotations agree.

The evaluator does not inspect names, cast between unrelated categories, or
provide an untyped dynamic value language.
-/

namespace CasCatalogue
open LeanCategories

open CategoryTheory

universe uObj uHom

/-! ## Primitive proof-carrying denotations -/

/-- The non-composite constructors of the current category expression syntax. -/
inductive CategoryPrimitive : CategoryExpr → Type
  | atom (id : CategoryId) : CategoryPrimitive (.atom id)
  | construct (constructor : ConstructorId) (arguments : Array ConstructorArg) :
      CategoryPrimitive (.construct constructor arguments)
  | familyApp (family : CategoryFamilyId) (arguments : Array ParameterExpr) :
      CategoryPrimitive (.familyApp family arguments)
  | familyTotal (family : CategoryFamilyId) : CategoryPrimitive (.familyTotal family)
  | classifierTotal (classifier : ClassifierId) :
      CategoryPrimitive (.classifierTotal classifier)
  | refine (base : CategoryExpr) (classifier : ClassifierId) :
      CategoryPrimitive (.refine base classifier)
  | opaque (id : CategoryId) : CategoryPrimitive (.opaque id)

/-- The non-composite constructors of the typed functor expression syntax. -/
inductive FunctorPrimitive :
    {source target : CategoryExpr} → FunctorExpr source target → Type
  | atomic {source target : CategoryExpr} (id : FunctorId) :
      FunctorPrimitive (FunctorExpr.atomic (source := source) (target := target) id)
  | classifierForget (classifier : ClassifierId) (host : CategoryExpr) :
      FunctorPrimitive (.classifierForget classifier host)
  | opaquePort {source target : CategoryExpr} (port : OpaquePortId) :
      FunctorPrimitive
        (FunctorExpr.opaquePort (source := source) (target := target) port)
  | familyFibreInclusion (family : CategoryFamilyId) (arguments : Array ParameterExpr) :
      FunctorPrimitive (.familyFibreInclusion family arguments)
  | familyReindex (family : CategoryFamilyId) (morphism : ParameterMorphismId)
      (source target : Array ParameterExpr) :
      FunctorPrimitive (.familyReindex family morphism source target)

/-- The non-composite constructors of the typed natural-transformation syntax. -/
inductive NatTransPrimitive {source target : CategoryExpr}
    {left right : FunctorExpr source target} :
    NatTransExpr left right → Type
  | atomic (id : NaturalTransformationId) :
      NatTransPrimitive (.atomic id)

/-- A concrete category together with its proof-carrying symbolic realization. -/
structure EvaluatedCategory (expression : CategoryExpr) where
  category : ObjCat.{uObj, uHom}
  realization : CategoryRealization.{uObj, uHom, uObj, uHom} expression category

/-- A concrete functor together with its proof-carrying symbolic realization. -/
structure EvaluatedFunctor {source target : CategoryExpr}
    (expression : FunctorExpr source target) where
  sourceCategory : ObjCat.{uObj, uHom}
  targetCategory : ObjCat.{uObj, uHom}
  functor : sourceCategory ⥤ targetCategory
  realization :
    FunctorRealization.{uObj, uHom, uObj, uHom, uObj, uHom, uObj, uHom}
      expression sourceCategory targetCategory functor

/-- A concrete natural transformation with proof-carrying endpoint realizations. -/
structure EvaluatedNatTrans {source target : CategoryExpr}
    {left right : FunctorExpr source target}
    (expression : NatTransExpr left right) where
  sourceCategory : ObjCat.{uObj, uHom}
  targetCategory : ObjCat.{uObj, uHom}
  leftFunctor : sourceCategory ⥤ targetCategory
  rightFunctor : sourceCategory ⥤ targetCategory
  transformation : leftFunctor ⟶ rightFunctor
  sourceRealization : CategoryRealization.{uObj, uHom, uObj, uHom} source sourceCategory
  targetRealization : CategoryRealization.{uObj, uHom, uObj, uHom} target targetCategory
  leftRealization :
    FunctorRealization.{uObj, uHom, uObj, uHom, uObj, uHom, uObj, uHom}
      left sourceCategory targetCategory leftFunctor
  rightRealization :
    FunctorRealization.{uObj, uHom, uObj, uHom, uObj, uHom, uObj, uHom}
      right sourceCategory targetCategory rightFunctor

/-!
A selected realization supplies values only for primitive syntax. The type of
each field preserves the syntax index, the concrete endpoints, and the
corresponding repository-owned realization witness.
-/
structure SelectedRealization where
  category : ∀ {expression : CategoryExpr},
    CategoryPrimitive expression →
      Option (EvaluatedCategory.{uObj, uHom} expression)
  functor : ∀ {source target : CategoryExpr}
    {expression : FunctorExpr source target},
    FunctorPrimitive expression →
      Option (EvaluatedFunctor.{uObj, uHom} expression)
  naturalTransformation : ∀ {source target : CategoryExpr}
    {left right : FunctorExpr source target}
    {expression : NatTransExpr left right},
    NatTransPrimitive expression →
      Option (EvaluatedNatTrans.{uObj, uHom} expression)

/-- A realization with no primitive denotations. -/
def SelectedRealization.empty : SelectedRealization where
  category _ := none
  functor _ := none
  naturalTransformation _ := none

/-! ## Category evaluation -/

/-- Evaluate a category expression by its selected primitive denotation. -/
noncomputable def evalCategory (selected : SelectedRealization) :
    (expression : CategoryExpr) → Option (EvaluatedCategory.{uObj, uHom} expression)
  | .atom id => selected.category (.atom id)
  | .construct constructor arguments => selected.category (.construct constructor arguments)
  | .familyApp family arguments => selected.category (.familyApp family arguments)
  | .familyTotal family => selected.category (.familyTotal family)
  | .classifierTotal classifier => selected.category (.classifierTotal classifier)
  | .refine base classifier => selected.category (.refine base classifier)
  | .opaque id => selected.category (.opaque id)

/-! ## Functor evaluation -/

/-- Retain a primitive functor only when its concrete endpoints realize its syntax. -/
noncomputable def alignFunctor
    (selected : SelectedRealization)
    {source target : CategoryExpr} {expression : FunctorExpr source target}
    (candidate : EvaluatedFunctor.{uObj, uHom} expression) :
    Option (EvaluatedFunctor.{uObj, uHom} expression) := by
  classical
  match evalCategory selected source, evalCategory selected target with
  | some sourceValue, some targetValue =>
      if candidate.sourceCategory = sourceValue.category ∧
          candidate.targetCategory = targetValue.category then
        exact some candidate
      else
        exact none
  | _, _ => exact none

/-- Evaluate a typed functor expression in the selected realization. -/
noncomputable def evalFunctor (selected : SelectedRealization)
    {source target : CategoryExpr} :
    (expression : FunctorExpr source target) →
      Option (EvaluatedFunctor.{uObj, uHom} expression)
  | .identity category =>
      match evalCategory selected category with
      | some value =>
          some
            { sourceCategory := value.category
              targetCategory := value.category
              functor := 𝟭 value.category
              realization :=
                { sourceRealization := value.realization
                  targetRealization := value.realization } }
      | none => none
  | .atomic id =>
      match selected.functor (source := source) (target := target)
          (expression := .atomic id)
          (FunctorPrimitive.atomic (source := source) (target := target) id) with
      | some candidate => alignFunctor selected candidate
      | none => none
  | .classifierForget classifier host =>
      match selected.functor (FunctorPrimitive.classifierForget classifier host) with
      | some candidate => alignFunctor selected candidate
      | none => none
  | .opaquePort port =>
      match selected.functor (source := source) (target := target)
          (expression := .opaquePort port)
          (FunctorPrimitive.opaquePort (source := source) (target := target) port) with
      | some candidate => alignFunctor selected candidate
      | none => none
  | .familyFibreInclusion family arguments =>
      match selected.functor (FunctorPrimitive.familyFibreInclusion family arguments) with
      | some candidate => alignFunctor selected candidate
      | none => none
  | .familyReindex family morphism source target =>
      match selected.functor
          (FunctorPrimitive.familyReindex family morphism source target) with
      | some candidate => alignFunctor selected candidate
      | none => none
  | .comp left right =>
      match evalFunctor selected left, evalFunctor selected right with
      | some leftValue, some rightValue => by
          classical
          rcases leftValue with ⟨leftSource, leftMiddle, leftFunctor, leftRealization⟩
          rcases rightValue with ⟨rightSource, rightTarget, rightFunctor, rightRealization⟩
          if h : leftMiddle = rightSource then
            cases h
            exact some
              { sourceCategory := leftSource
                targetCategory := rightTarget
                functor := leftFunctor ⋙ rightFunctor
                realization :=
                  { sourceRealization := leftRealization.sourceRealization
                    targetRealization := rightRealization.targetRealization } }
          else
            exact none
      | _, _ => none

/-! ## Natural-transformation evaluation -/

/-- Retain a natural transformation only when both typed endpoints agree. -/
noncomputable def alignNatTrans
    (selected : SelectedRealization)
    {source target : CategoryExpr}
    {left right : FunctorExpr source target}
    {expression : NatTransExpr left right}
    (candidate : EvaluatedNatTrans.{uObj, uHom} expression) :
    Option (EvaluatedNatTrans.{uObj, uHom} expression) := by
  classical
  match evalFunctor selected left, evalFunctor selected right with
  | some _, some _ => exact some candidate
  | _, _ => exact none

/-- Evaluate a typed natural-transformation expression in the selected realization. -/
noncomputable def evalNatTrans (selected : SelectedRealization)
    {source target : CategoryExpr}
    {left right : FunctorExpr source target} :
    (expression : NatTransExpr left right) →
      Option (EvaluatedNatTrans.{uObj, uHom} expression)
  | .identity functor =>
      match evalFunctor selected functor with
      | some value =>
          some
            { sourceCategory := value.sourceCategory
              targetCategory := value.targetCategory
              leftFunctor := value.functor
              rightFunctor := value.functor
              transformation := 𝟙 value.functor
              sourceRealization := value.realization.sourceRealization
              targetRealization := value.realization.targetRealization
              leftRealization := value.realization
              rightRealization := value.realization }
      | none => none
  | .atomic id =>
      match selected.naturalTransformation (NatTransPrimitive.atomic id) with
      | some candidate => alignNatTrans selected candidate
      | none => none
  | .vcomp first second =>
      match evalNatTrans selected first, evalNatTrans selected second with
      | some firstValue, some secondValue => by
          classical
          rcases firstValue with
            ⟨firstSource, firstTarget, firstLeft, firstMiddle, firstTransformation,
              firstSourceRealization, firstTargetRealization, firstLeftRealization,
              firstMiddleRealization⟩
          rcases secondValue with
            ⟨secondSource, secondTarget, secondMiddle, secondRight, secondTransformation,
              secondSourceRealization, secondTargetRealization, secondMiddleRealization,
              secondRightRealization⟩
          if hSource : firstSource = secondSource then
            cases hSource
            if hTarget : firstTarget = secondTarget then
              cases hTarget
              if hMiddle : firstMiddle = secondMiddle then
                cases hMiddle
                exact some
                  { sourceCategory := firstSource
                    targetCategory := firstTarget
                    leftFunctor := firstLeft
                    rightFunctor := secondRight
                    transformation :=
                      NatTrans.vcomp firstTransformation secondTransformation
                    sourceRealization := firstSourceRealization
                    targetRealization := firstTargetRealization
                    leftRealization := firstLeftRealization
                    rightRealization := secondRightRealization }
              else
                exact none
            else
              exact none
          else
            exact none
      | _, _ => none
  | .hcomp first second =>
      match evalNatTrans selected first, evalNatTrans selected second with
      | some firstValue, some secondValue => by
          classical
          rcases firstValue with
            ⟨firstSource, firstMiddle, firstLeft, firstRight, firstTransformation,
              firstSourceRealization, firstMiddleRealization, firstLeftRealization,
              firstRightRealization⟩
          rcases secondValue with
            ⟨secondMiddle, secondTarget, secondTop, secondBottom, secondTransformation,
              secondMiddleRealization, secondTargetRealization, secondTopRealization,
              secondBottomRealization⟩
          if hMiddle : firstMiddle = secondMiddle then
            cases hMiddle
            exact some
              { sourceCategory := firstSource
                targetCategory := secondTarget
                leftFunctor := firstLeft ⋙ secondTop
                rightFunctor := firstRight ⋙ secondBottom
                transformation := firstTransformation ◫ secondTransformation
                sourceRealization := firstSourceRealization
                targetRealization := secondTargetRealization
                leftRealization :=
                  { sourceRealization := firstLeftRealization.sourceRealization
                    targetRealization := secondTopRealization.targetRealization }
                rightRealization :=
                  { sourceRealization := firstRightRealization.sourceRealization
                    targetRealization := secondBottomRealization.targetRealization } }
              else
                exact none
      | _, _ => none

end CasCatalogue
