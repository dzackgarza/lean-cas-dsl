module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.Surface
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering

public section

namespace CasCompiler

open Lean Meta CasCatalogue


private def checkNativeCell (source target left right transformation : Expr) : MetaM Unit := do
  let (leftSource, leftTarget) ← functorCategoryBundles left
  let (rightSource, rightTarget) ← functorCategoryBundles right
  unless ← isDefEq leftSource source <&&> isDefEq rightSource source <&&>
      isDefEq leftTarget target <&&> isDefEq rightTarget target do
    throwError "the selected cell has different complete native categories"
  let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
  unless ← isDefEq (← inferType transformation) expected do
    throwError "the selected cell has different complete native functor endpoints"




def nativeSourceCell (entry : CellEntry) (application : Expr) (inverse : Bool := false) :
    MetaM NativeSourceCell := do
  let state ← semanticState
  let #[original] := state.cells.filter (·.id == entry.id)
    | throwError "a source cell requires its unique registered declaration"
  unless original.declaration == entry.declaration && original.invertible == entry.invertible &&
      original.source.syntacticEq entry.source && original.target.syntacticEq entry.target &&
      original.left == entry.left && original.right == entry.right do
    throwError "the selected cell changed its accepted registration"
  if inverse && !entry.invertible then
    throwStratum .invalid "the source cell has no registered inverse"
  discard <| checkedDeclaration entry.declaration
  let application ← instantiateMVars application
  unless application.consumeMData.getAppFn.isConstOf entry.declaration do
    throwError "the selected cell lost its original declaration application"
  let transformation ← if entry.invertible then
      mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[application]
    else pure application
  let type ← whnfR (← inferType transformation)
  let declaredLeft ← if type.isAppOfArity ``Quiver.Hom 4 then
      pure type.getAppArgs[2]!
    else if type.isAppOfArity ``CategoryTheory.NatTrans 6 then
      pure type.getAppArgs[4]!
    else throwError "the applied cell has no complete native transformation interface"
  let (source, target) ← functorCategoryBundles declaredLeft
  let left ← nativeEdgePathFunctor state entry.left source
  let right ← nativeEdgePathFunctor state entry.right source
  let (left, right) := if inverse then (right, left) else (left, right)
  checkNativeCell source target left.functor right.functor transformation
  let isomorphism ← if entry.invertible then do
      let directed ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[application]
        else pure application
      pure (some directed)
    else pure none
  let mut references : Array SelectedSourceReference := #[.cell entry]
  for edge in entry.left ++ entry.right do
    references := references ++ (← sourceActionReferences state edge)
  return {
    entry := entry
    references := references
    application := application
    inverse := inverse
    source := entry.source
    sourceBundle := source
    target := entry.target
    targetBundle := target
    left := left
    right := right
    transformation := transformation
    isomorphism := isomorphism }

private def selectedConstructorApplication (entry : ConstructorEntry) (field : Name)
    (categories arguments : Array Expr) : MetaM Expr := do
  discard <| checkedDeclaration field
  let value ← applyConstructorInterface field categories arguments
  return value

private def checkNativeIso (left right value : Expr) : MetaM Unit := do
  let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
  unless ← isDefEq (← inferType value) expected do
    throwError "the selected constructor comparison changed its complete native endpoints"




private def mapCellRoute (entry : ConstructorEntry) (source : Expr)
    (route : NativeRouteFunctor) : MetaM (NativeRouteFunctor × Expr) := do
  let some action := entry.functorialAction
    | throwStratum .invalid "the selected constructor has no declared functor action"
  let some identity := entry.identityComparison
    | throwStratum .invalid "the selected constructor has no declared identity comparison"
  let some composition := entry.compositionComparison
    | throwStratum .invalid "the selected constructor has no declared composition comparison"
  let mappedSource ← selectedConstructorApplication entry entry.semantics #[source] #[source]
  let mappedTarget ← selectedConstructorApplication entry entry.semantics
    #[route.target] #[route.target]
  let whole ← selectedConstructorApplication entry action #[source, route.target] #[route.functor]
  if route.actions.isEmpty then
    let result ← categoryIdentity mappedSource
    let comparison ← selectedConstructorApplication entry identity #[source] #[source]
    checkNativeIso whole result comparison
    return (⟨result, mappedTarget, #[]⟩, comparison)
  let first := route.actions[0]!
  let (firstSource, firstTarget) ← functorCategoryBundles first
  unless ← isDefEq firstSource source do
    throwError "the selected cell route lost its original starting category"
  let mapped ← selectedConstructorApplication entry action #[source, firstTarget] #[first]
  let mut original := first
  let mut originalTarget := firstTarget
  let mut expanded := mapped
  let mut actions := #[mapped]
  let mut comparison ← mkAppM ``CategoryTheory.Iso.refl #[mapped]
  for next in route.actions.extract 1 route.actions.size do
    let (nextSource, nextTarget) ← functorCategoryBundles next
    unless ← isDefEq nextSource originalTarget do
      throwError "the selected cell route lost an original intermediate category"
    let mappedNext ← selectedConstructorApplication entry action
      #[originalTarget, nextTarget] #[next]
    let step ← selectedConstructorApplication entry composition
      #[source, originalTarget, nextTarget] #[original, next]
    let carried ← mkAppM ``CategoryTheory.Functor.isoWhiskerRight #[comparison, mappedNext]
    comparison ← mkAppM ``CategoryTheory.Iso.trans #[step, carried]
    original ← mkFunctorComp original next
    originalTarget := nextTarget
    expanded ← mkFunctorComp expanded mappedNext
    actions := actions.push mappedNext
  checkNativeIso whole expanded comparison
  return (⟨expanded, mappedTarget, actions⟩, comparison)



def NativeSourceCell.construct (cell : NativeSourceCell) (id : ConstructorId) :
    MetaM NativeSourceCell := do
  let some entry := (← semanticState).constructor? id
    | throwStratum .invalid "the source comparison constructor is absent"
  unless entry.signature == #[.category] do
    throwStratum .invalid "the source comparison constructor does not have a unary category interface"
  let some action := entry.comparisonAction
    | throwStratum .invalid "the source comparison constructor has no declared comparison action"
  let some original := cell.isomorphism
    | throwStratum .invalid "the source constructor comparison requires an invertible cell"
  let source ← selectedConstructorApplication entry entry.semantics
    #[cell.sourceBundle] #[cell.sourceBundle]
  let target ← selectedConstructorApplication entry entry.semantics
    #[cell.targetBundle] #[cell.targetBundle]
  let (left, leftExpansion) ← mapCellRoute entry cell.sourceBundle cell.left
  let (right, rightExpansion) ← mapCellRoute entry cell.sourceBundle cell.right
  let mapped ← selectedConstructorApplication entry action
    #[cell.sourceBundle, cell.targetBundle] #[original]
  let reverseLeft ← mkAppM ``CategoryTheory.Iso.symm #[leftExpansion]
  let comparison ← mkAppM ``CategoryTheory.Iso.trans #[reverseLeft, mapped]
  let comparison ← mkAppM ``CategoryTheory.Iso.trans #[comparison, rightExpansion]
  checkNativeIso left.functor right.functor comparison
  let transformation ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
  checkNativeCell source target left.functor right.functor transformation
  return { cell with
    constructors := #[id] ++ cell.constructors
    references := #[.constructor entry, .constructorInterface entry .functorialAction,
      .constructorInterface entry .comparisonAction,
      .constructorInterface entry .identityComparison,
      .constructorInterface entry .compositionComparison] ++ cell.references
    source := .construct id #[.category cell.source]
    sourceBundle := source
    target := .construct id #[.category cell.target]
    targetBundle := target
    left := left
    right := right
    transformation := transformation
    isomorphism := some comparison }



def NativeSourceCell.component (cell : NativeSourceCell) (receiver : NativeSourceJudgement) :
    MetaM (SourceSelection Expr) := do
  if let some category := receiver.category then
    unless category.role == .object && category.expression.syntacticEq cell.source do
      throwStratum .invalid "the source cell receiver has a different selected category"
    unless ← isDefEq category.bundle cell.sourceBundle do
      throwStratum .invalid "the source cell receiver has different complete native category parameters"
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[cell.sourceBundle]
  unless ← isDefEq (← inferType receiver.value) carrier do
    throwStratum .invalid "the source cell receiver is outside its complete declared domain"
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[cell.transformation, receiver.value]
  check component
  return {
    value := component
    reference := some (.cell cell.entry)
    originalApplication := some cell.application
    cell := some ⟨cell, receiver.value, component⟩
    category := some ⟨.morphism, cell.target, ← instantiateMVars cell.targetBundle, none, none⟩ }



def sourceCellComponent? (context : OpenContext) (scope : SourceSelectionScope Expr)
    (value : Expr) : MetaM (Option NativeSourceCellComponent) := do
  let some selected := scope.findAt? context value.getAppFn | return none
  unless selected.formalBindings.size == value.getAppNumArgs do return none
  return (← selected.specialize value.getAppArgs).cell

end CasCompiler
