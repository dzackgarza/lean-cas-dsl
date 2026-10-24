/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.DirectConstruction
public import CasCatalogue.CategoryContext
public import CasCatalogue.InterpretationFailure
public import LeanCategories.Catalogue.FamilyFibration

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.ReindexAction

/-- A complete accepted family transport, selected at its actual base morphism.
The family realization is independent of every computational representation. -/
structure Plan where
  entry : FunctorEntry
  family : CategoryFamilyEntry
  parameters : Array Expr
  action : Expr
  realization : Expr
  baseMorphism : Expr
  source : CategoryContext
  target : CategoryContext
  total : CategoryContext

/-- Instantiate a registered reindexing without dropping its original base map,
even when that map is absent from the resulting object's type. -/
def select (entry : FunctorEntry) (parameters : Array Term) (baseMorphism : Expr)
    (context : CategoryContext) : TermElabM Plan := do
  let .familyReindex familyId := entry.expression.registrationKind
    | throwStratum .invalid "the selected functor is not a registered family reindexing"
  let state ← registryState
  let some family := state.categoryFamily? familyId
    | throwStratum .invalid "the selected reindexing has no accepted family realization"
  let application ← DirectConstruction.instantiate entry.declaration parameters
  let baseType ← inferType baseMorphism
  let mut baseArguments : Array Expr := #[]
  for argument in application.explicit do
    if ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType argument) baseType) then
      if ← withoutModifyingState (withTransparency .all <| isDefEq argument baseMorphism) then
        baseArguments := baseArguments.push argument
  let #[baseArgument] := baseArguments
    | if baseArguments.isEmpty then
        throwStratum .invalid "the reindexing has no matching complete base-morphism argument"
      else
        throwSemanticAmbiguity "the reindexing has several possible base-morphism arguments"
  unless ← withTransparency .all <| isDefEq baseArgument baseMorphism do
    throwStratum .invalid "the reindexing changes its original selected base morphism"
  let realization ← mkConstWithFreshMVarLevels family.realization
  let canonical ← mkAppHere ``CasCatalogue.CategoryFamilyRealization.reindexFunctor
    #[realization, baseMorphism]
  let action ← Semantic.asFunctor application.value
  unless ← withTransparency .all <| isDefEq action canonical do
    throwStratum .invalid "the selected action differs from its accepted family transport"
  let (sourceBundle, _) ← functorCategoryBundles action
  unless ← withTransparency .all <| isDefEq sourceBundle context.bundle do
    throwStratum .invalid "the reindexing has a different complete source fibre"
  let application ← DirectConstruction.close application
  let action ← instantiateMVars (← Semantic.asFunctor application.value)
  let realization ← instantiateMVars realization
  let (sourceBundle, targetBundle) ← functorCategoryBundles action
  let totalBundle ← mkAppM ``CasCatalogue.CategoryFamilyRealization.totalCat #[realization]
  let totalBundle ← instantiateMVars totalBundle
  if realization.hasMVar || realization.hasLevelMVar ||
      totalBundle.hasMVar || totalBundle.hasLevelMVar then
    throwStratum .invalid "the family transport has incomplete total-category parameters"
  return {
    entry, family, parameters := application.explicit, action, realization, baseMorphism
    source := { context with bundle := (← instantiateMVars sourceBundle) }
    target := { expression := entry.target, bundle := (← instantiateMVars targetBundle) }
    total := { expression := .familyTotal familyId, bundle := totalBundle } }

/-- Every applicable registered selection participates. Declaration order is not a
choice of family transport. -/
def resolve (baseMorphism : Expr) (context : CategoryContext) : TermElabM Plan := do
  let state ← registryState
  let mut plans : Array Plan := #[]
  for entry in state.functors do
    unless entry.expression.registrationKind matches .familyReindex .. do continue
    let candidate ← try
      withoutModifyingState (some <$> select entry #[] baseMorphism context)
    catch error =>
      if Exception.interpretationKind error == .invalid then pure none else throw error
    if let some plan := candidate then plans := plans.push plan
  let #[plan] := plans
    | if plans.isEmpty then
        throwStratum .invalid "no registered reindexing accepts this complete fibre and base map"
      else throwSemanticAmbiguity m!"several registered family reindexings apply: \
        {plans.map (·.entry.id.raw)}"
  return plan

def object (plan : Plan) (receiver : Expr) : TermElabM Expr := do
  CategoryContext.checkObject plan.source receiver
  let result ← Semantic.objOf plan.action receiver
  CategoryContext.checkObject plan.target result
  return result

def map (plan : Plan) (receiver : Expr) : TermElabM Expr := do
  let type ← whnfR (← inferType receiver)
  unless type.isAppOf ``Quiver.Hom && type.getAppArgs.size >= 2 do
    throwStratum .invalid "reindexing a whole map requires its complete categorical endpoints"
  let source := type.getAppArgs[type.getAppArgs.size - 2]!
  let target := type.getAppArgs.back!
  CategoryContext.checkMorphism plan.source receiver source target
  let result ← Semantic.mapOf plan.action receiver
  CategoryContext.checkMorphism plan.target result
    (← object plan source) (← object plan target)
  return result

/-- The accepted pseudofunctor fixes the entire canonical cartesian map. No
computational output, carrier comparison or per-family rule enters its construction. -/
def cartesian (plan : Plan) (receiver : Expr) : TermElabM (Expr × Expr × Expr) := do
  CategoryContext.checkObject plan.source receiver
  let transport ← mkAppM ``CasCatalogue.CategoryFamilyRealization.transport #[plan.realization]
  let baseType ← whnfR (← inferType plan.baseMorphism)
  unless baseType.isAppOf ``Quiver.Hom && baseType.getAppArgs.size >= 2 do
    throwStratum .invalid "the selected base map has no complete categorical endpoints"
  let baseSource := baseType.getAppArgs[baseType.getAppArgs.size - 2]!
  let baseTarget := baseType.getAppArgs.back!
  let value ← mkAppOptM ``CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift
    #[none, none, some transport, some baseSource, some baseTarget,
      some receiver, some plan.baseMorphism]
  let value ← instantiateMVars value
  let type ← whnfR (← inferType value)
  unless type.isAppOf ``Quiver.Hom && type.getAppArgs.size >= 2 do
    throwStratum .invalid "the accepted cartesian lift lost its complete total-category type"
  let source := type.getAppArgs[type.getAppArgs.size - 2]!
  let target := type.getAppArgs.back!
  CategoryContext.checkMorphism plan.total value source target
  if value.hasMVar || value.hasLevelMVar then
    throwStratum .invalid "the accepted cartesian lift has unresolved original parameters"
  return (value, source, target)

end CasCatalogue.ReindexAction
