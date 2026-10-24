/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.DirectConstruction
public import CasCatalogue.CategoryContext

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.CellAction

structure Action where
  entry : CellEntry
  parameters : Array Expr
  constructors : Array ConstructorId
  inverse : Bool
  transformation : Expr
  isomorphism : Option Expr
  left : Expr
  right : Expr
  source : CategoryExpr
  target : CategoryExpr
  sourceBundle : Expr
  targetBundle : Expr
  leftRoute : Array EdgeRef
  rightRoute : Array EdgeRef
  leftApplications : Array Expr
  rightApplications : Array Expr

/-- Apply only the registered cell and the registered constructors' comparison actions.
Complete declaration parameters and both functor actions remain attached to the result. -/
def assemble (entry : CellEntry) (application : DirectConstruction.Application)
    (constructors : Array ConstructorId)
    (inverse : Bool) (receiver : Expr) : TermElabM Action := do
  let state ← registryState
  let mut comparison := application.value
  let mut source := entry.source
  let mut target := entry.target
  let mut leftRoute := entry.left
  let mut rightRoute := entry.right
  let ((left, initialLeft), (right, initialRight)) ←
    Semantic.routeComparisonApplications state leftRoute rightRoute
  let (initialSource, initialTarget) ← functorCategoryBundles left
  let mut sourceBundle := (← CategoryContext.presented
    { expression := source, bundle := initialSource }).bundle
  let mut targetBundle := (← CategoryContext.presented
    { expression := target, bundle := initialTarget }).bundle
  let mut leftApplications := initialLeft
  let mut rightApplications := initialRight
  if entry.invertible then Semantic.checkRouteComparison comparison left right
  if inverse && !entry.invertible then
    throwStratum .invalid "the selected cell has no registered inverse"
  unless constructors.isEmpty || entry.invertible do
    throwStratum .invalid "the registered constructor action requires an invertible comparison"
  for constructor in constructors.reverse do
    let some row := state.constructor? constructor
      | throwStratum .invalid "the selected cell names an unregistered category constructor"
    let some action := row.comparisonAction
      | throwStratum .invalid "the category constructor has no accepted comparison action"
    let comparisonType ← whnfR (← inferType comparison)
    unless comparisonType.isAppOf ``CategoryTheory.Iso do
      throwStratum .invalid "the selected constructor input is not a complete natural isomorphism"
    let some functorAction := row.functorialAction
      | throwStratum .invalid "the category constructor has no accepted functor action"
    let (sourceCategory, targetCategory) ← functorCategoryBundles comparisonType.getAppArgs[2]!
    let leftExpansion ← Semantic.constructorRouteComparison state constructor leftRoute
      comparisonType.getAppArgs[2]!
    let rightExpansion ← Semantic.constructorRouteComparison state constructor rightRoute
      comparisonType.getAppArgs[3]!
    let mapped ← applyConstructorInterface action #[sourceCategory, targetCategory] #[comparison]
    comparison ← mkAppM ``CategoryTheory.Iso.trans #[
      ← mkAppM ``CategoryTheory.Iso.trans #[← mkAppM ``CategoryTheory.Iso.symm #[leftExpansion], mapped],
      rightExpansion]
    leftRoute := leftRoute.map (.constructMap constructor)
    rightRoute := rightRoute.map (.constructMap constructor)
    leftApplications ← leftApplications.mapM fun value =>
      Semantic.applyConstructorFunctor functorAction value
    rightApplications ← rightApplications.mapM fun value =>
      Semantic.applyConstructorFunctor functorAction value
    source := .construct constructor #[.category source]
    target := .construct constructor #[.category target]
    sourceBundle ← applyConstructorInterface row.semantics #[sourceBundle] #[sourceBundle]
    targetBundle ← applyConstructorInterface row.semantics #[targetBundle] #[targetBundle]
  let isomorphism ← if entry.invertible then
    pure (some (← if inverse then mkAppM ``CategoryTheory.Iso.symm #[comparison]
      else pure comparison))
    else pure none
  let transformation ← match isomorphism with
    | some comparison => mkAppM ``CategoryTheory.Iso.hom #[comparison]
    | none => pure comparison
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, receiver]
  let transformation ← instantiateMVars transformation
  let component ← instantiateMVars component
  unless ← isTypeCorrect component do
    throwStratum .invalid "the selected cell has incompatible complete endpoint data"
  let type ← whnfR (← inferType transformation)
  unless type.isAppOf ``CategoryTheory.NatTrans do
    throwStratum .invalid "the registered cell does not retain its natural transformation"
  let arguments := type.getAppArgs
  let (selectedLeftRoute, selectedRightRoute, selectedLeftApplications,
      selectedRightApplications) := if inverse then
    (rightRoute, leftRoute, rightApplications, leftApplications)
    else (leftRoute, rightRoute, leftApplications, rightApplications)
  return {
    entry
    parameters := (← application.explicit.mapM instantiateMVars)
    constructors, inverse, transformation
    isomorphism := (← isomorphism.mapM instantiateMVars)
    left := arguments[arguments.size - 2]!
    right := arguments.back!
    source, target
    sourceBundle := (← instantiateMVars sourceBundle)
    targetBundle := (← instantiateMVars targetBundle)
    leftRoute := selectedLeftRoute
    rightRoute := selectedRightRoute
    leftApplications := (← selectedLeftApplications.mapM instantiateMVars)
    rightApplications := (← selectedRightApplications.mapM instantiateMVars) }

/-- Close the complete selected application before recording its mathematical meaning. -/
def select (entry : CellEntry) (parameters : Array Term) (constructors : Array ConstructorId)
    (inverse : Bool) (receiver : Expr) : TermElabM Action := do
  let application ← DirectConstruction.instantiate entry.declaration parameters
  let action ← assemble entry application constructors inverse receiver
  let application ← DirectConstruction.close application
  let transformation ← instantiateMVars action.transformation
  if transformation.hasMVar || transformation.hasLevelMVar then
    throwStratum .invalid "the selected cell has unresolved complete parameters"
  return { action with
    parameters := application.explicit
    transformation
    isomorphism := (← action.isomorphism.mapM instantiateMVars)
    left := (← instantiateMVars action.left)
    right := (← instantiateMVars action.right)
    sourceBundle := (← instantiateMVars action.sourceBundle)
    targetBundle := (← instantiateMVars action.targetBundle)
    leftApplications := (← action.leftApplications.mapM instantiateMVars)
    rightApplications := (← action.rightApplications.mapM instantiateMVars) }

/-- Component at the exact selected object; constructor-induced cells may themselves
be arrows, core isomorphisms, or other complete structured morphisms. -/
def component (action : Action) (receiver : Expr) : TermElabM Expr :=
  mkAppM ``CategoryTheory.NatTrans.app #[action.transformation, receiver]

/-- The accepted isomorphism itself, for constructions whose source is a core category. -/
def componentIso (action : Action) (receiver : Expr) : TermElabM Expr := do
  let some comparison := action.isomorphism
    | throwStratum .invalid "this component has no accepted invertible interface"
  mkAppM ``CategoryTheory.Iso.app #[comparison, receiver]

/-- Both object images are retained rather than identifying equal carriers. -/
def objects (action : Action) (receiver : Expr) : TermElabM (Expr × Expr) := do
  return (← Semantic.objOf action.left receiver, ← Semantic.objOf action.right receiver)

/-- Map actions of both selected endpoint functors use the original complete morphism. -/
def maps (action : Action) (morphism : Expr) : TermElabM (Expr × Expr) := do
  return (← Semantic.mapOf action.left morphism, ← Semantic.mapOf action.right morphism)

end CasCatalogue.CellAction
