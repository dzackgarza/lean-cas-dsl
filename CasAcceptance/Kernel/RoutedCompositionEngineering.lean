/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.RoutedResultPlan
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.RoutedResultPlan
meta import LeanCategories.Catalogue.Semantics

/-! Engineering control for the complete schema of an existing dependent
two-action route. The accepted Arrow action on bilinear-module forgetting and
the accepted module-kernel method share a selected ring. No mathematical row,
leaf, expected mathematical answer, or protected assertion is introduced here.

Calling the full selector is essential: enumerating parameter slots alone
does not exercise composition of the two independently dependent telescopes.
The returned ambient field also exposes a prefix output in the fused reply;
it must retain that producer's position rather than borrow another evaluation.
-/

open Lean Meta Elab Term CasCatalogue

private def samePath (left right : ComputationalData.RecordFieldPath) : Bool :=
  left.size == right.size && (left.zip right).all fun (first, second) =>
    first.sameDeclaration second

run_elab do
  let state ← registryState
  let some kernel := state.functor? ⟨"fun.arrows_modules.kernel"⟩
    | throwError "the composition control requires the existing module-kernel declaration"
  let #[method] := state.methods.filter (·.functor == kernel.id)
    | throwError "the composition control requires its unique existing method"
  let receiver ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ ℤ ℤ))) none
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[receiver]
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let edge := EdgeRef.constructMap ConstructorId.arrow (.functor FunctorId.bilinModuleForget)
  let prefixAction ← Semantic.edgeFunctor state edge
  let transported ← Semantic.objOf prefixAction arrow
  let action ← registeredFunctorInstance kernel
  let expected ← Semantic.objOf action (← methodArgument method transported)
  let action ← instantiateMVars action
  let prefixAction ← instantiateMVars prefixAction
  let (sourceBundle, _) ← functorCategoryBundles (← Semantic.asFunctor prefixAction)
  let (_, targetBundle) ← functorCategoryBundles (← Semantic.asFunctor action)
  let some source := state.selectedEdgeSource? edge
    | throwError "the composition control lost its accepted complete source category"
  let sourceContext : CategoryContext := { expression := source, bundle := sourceBundle }
  let resultContext : CategoryContext := { expression := kernel.target, bundle := targetBundle }
  let plan ← RoutedResultPlan.select method action arrow sourceContext resultContext
    #[(edge, prefixAction)]
  unless plan.prefixActions.size == 1 && (← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType plan.formal) (← inferType expected) <&&>
        isDefEq plan.formal expected)) do
    throwError "the full composition schema changed its accepted two-action result"
  let some first := (plan.parameters.filter (·.actionIndex == 0))[0]?
    | throwError "the full composition omitted the prefix's original ring position"
  let some second := (plan.parameters.filter (·.actionIndex == 1))[0]?
    | throwError "the full composition omitted the method's original ring position"
  unless first.actionIndex != second.actionIndex && first.dataIndex == 0 && second.dataIndex == 0 &&
      (← withoutModifyingState (withTransparency .all <|
        isDefEq first.expectedType second.expectedType <&&> isDefEq first.formal second.formal)) do
    throwError "the dependent composition collapsed two equal-valued parameter occurrences"
  let sourcePath ← withLocalDeclD `prefixResult (← inferType transported) fun symbolic => do
    let field ← mkAppM ``CategoryTheory.Arrow.left #[symbolic]
    let some path ← ComputationalData.recordFieldPath? symbolic field
      | throwError "the control lost its accepted public Arrow source projection"
    return path
  let #[ambientPath] := plan.producedPaths 0 sourcePath
    | throwError "the fused reply did not expose the exact prefix-produced ambient occurrence"
  let #[ambient] := plan.slots.filter (fun slot => samePath slot.replyPath ambientPath)
    | throwError "the fused reply lost the ambient field's exact final output position"
  unless ambient.node matches .returned do
    throwError "a prefix-produced ambient was replaced by an original input packet"
  let some origin := ambient.producedBy
    | throwError "the returned ambient lost its original prefix-action provenance"
  unless origin.actionIndex == 0 && samePath origin.replyPath sourcePath do
    throwError "the returned ambient changed its selected prefix output field"
  unless plan.stages.size == 2 do
    throwError "the composition control lost an independently compiled action boundary"
  let prefix ← plan.stage 0
  let finalStage ← plan.stage 1
  unless prefix.edge == edge && finalStage.actionIndex == 1 &&
      prefix.completions.size == prefix.slots.size do
    throwError "the completion table changed its original action or slot ordinals"
  let some output := prefix.slots[prefix.output]?
    | throwError "the prefix completion lost its complete public result"
  let .record .arrow #[sourceIndex, targetIndex, mapIndex] := output.node
    | throwError "the existing Arrow action lost its public three-field codec"
  unless sourceIndex != targetIndex && sourceIndex < mapIndex && targetIndex < mapIndex do
    throwError "the intermediate map merged its distinct declared image endpoint positions"
  let some sourceField := prefix.slots[sourceIndex]?
    | throwError "the prefix completion lost its source image field"
  let some targetField := prefix.slots[targetIndex]?
    | throwError "the prefix completion lost its target image field"
  let some mapField := prefix.slots[mapIndex]?
    | throwError "the prefix completion lost its map image field"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq sourceField.formal targetField.formal) do
    throwError "the endpoint occurrence control no longer exercises equal closed formal values"
  let actionAt (index : Nat) : TermElabM RoutedResultPlan.FieldCompletionAction := do
    let some completion := prefix.completions[index]?
      | throwError "the intermediate field has no aligned completion position"
    let .action selected := completion
      | throwError "the intermediate field lost its complete accepted object or map action"
    return selected
  let sourceCompletion ← actionAt sourceIndex
  let targetCompletion ← actionAt targetIndex
  let mapCompletion ← actionAt mapIndex
  unless sourceCompletion.kind matches .object do
    throwError "the missing source image changed its complete object action role"
  unless targetCompletion.kind matches .object do
    throwError "the missing target image changed its complete object action role"
  let .map actualSource actualTarget := mapCompletion.kind
    | throwError "the missing callable changed its complete map action role"
  unless actualSource == sourceIndex && actualTarget == targetIndex do
    throwError "the map completion changed its exact chosen image endpoint slots"
  let (originalSourcePath, originalTargetPath, originalMapPath) ← withLocalDeclD
      `originalArrow (← inferType arrow) fun symbolic => do
    let pathFor (projection : Name) : TermElabM ComputationalData.RecordFieldPath := do
      let field ← mkAppM projection #[symbolic]
      let some path ← ComputationalData.recordFieldPath? symbolic field
        | throwError "the completion control lost an original public callable field"
      return path
    return (← pathFor ``CategoryTheory.Arrow.left,
      ← pathFor ``CategoryTheory.Arrow.right, ← pathFor ``CategoryTheory.Arrow.hom)
  let checkOriginal (completion : RoutedResultPlan.FieldCompletionAction)
      (path : ComputationalData.RecordFieldPath) : TermElabM Unit := do
    let .retained .receiver (.input selectedPath) := completion.source
      | throwError "an intermediate completion changed its exact original input supplier"
    unless samePath selectedPath path do
      throwError "an intermediate completion changed its original public field occurrence"
    let #[selected] := completion.steps
      | throwError "the existing single field action changed its selected declaration boundary"
    unless selected.edge == .functor FunctorId.bilinModuleForget do
      throwError "the missing field selected a different complete registered action"
  checkOriginal sourceCompletion originalSourcePath
  checkOriginal targetCompletion originalTargetPath
  checkOriginal mapCompletion originalMapPath
  unless (plan.producedPaths 0 targetField.replyPath).isEmpty &&
      (plan.producedPaths 0 mapField.replyPath).isEmpty do
    throwError "the partial-completion control no longer requires missing target and callable fields"
  unless prefix.projectionActions.any (fun selected =>
      selected.parentSlot == prefix.output && selected.fieldSlot == sourceIndex) do
    throwError "the intermediate boundary lost its selected public projection comparison"
  logInfo "PASS: dependent route stages preserve exact fused suppliers and positional completion actions"
