/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.RoutedResultPlan
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.RoutedResultPlan
meta import LeanCategories.Catalogue.Semantics

/-! Engineering controls of selected public result positions and scoped data.
The deliberately opaque packets below claim no mathematical answers. Existing
accepted kernel and forgetful declarations supply the independent typed roles;
the control adds no mathematical registration or leaf implementation. -/

open Lean Meta Elab Term CasCatalogue

private def opaque (token : String) (owner : String) (session : Nat) : DataOwnership.Data :=
  DataOwnership.Data.capture
    (Json.mkObj [("ctor", toJson "opaqueData"), ("args", Json.arr #[toJson token])])
    (owner, session)

private def ctor (name : String) (fields : Array DataOwnership.Data) :
    TermElabM DataOwnership.Data := do
  let .ok data := DataOwnership.Data.ctor name fields
    | throwError "the schema control lost its exact positioned suppliers"
  return data

private def selectedMethod (state : RegistryState) (id : FunctorId) : TermElabM MethodEntry := do
  let #[method] := state.methods.filter (·.functor == id)
    | throwError "the schema control requires its existing unique declared method"
  return method

run_elab do
  let state ← registryState
  let some kernel := state.functor? ⟨"fun.arrows_groups.kernel"⟩
    | throwError "the schema control requires the existing group kernel functor"
  let method ← selectedMethod state kernel.id
  let sign ← elabTermAndSynthesize (← `(CasCatalogue.Algebra.FiniteGroups.sign 3)) none
  let signArrow ← mkAppM ``CategoryTheory.Arrow.mk #[sign]
  let object ← mkAppM ``CategoryTheory.Arrow.left #[signArrow]
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let receiver ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let action ← registeredFunctorInstance kernel
  let argument ← methodArgument method receiver
  discard <| Semantic.objOf action argument
  let action ← instantiateMVars action
  let (source, target) ← functorCategoryBundles (← Semantic.asFunctor action)
  let sourceContext : CategoryContext := { expression := kernel.source, bundle := source }
  let resultContext : CategoryContext := { expression := kernel.target, bundle := target }
  let plan ← RoutedResultPlan.select method action receiver sourceContext resultContext
  unless plan.parameters.isEmpty do
    throwError "the existing group-kernel control acquired an unaccounted data parameter"
  let first ← mkAppM ``CategoryTheory.Arrow.left #[receiver]
  let second ← mkAppM ``CategoryTheory.Arrow.right #[receiver]
  unless ← withoutModifyingState (withTransparency .all <| isDefEq first second) do
    throwError "the schema control no longer has equal formal endpoint values"
  -- The two endpoint positions intentionally have identical bytes and different
  -- supplying sessions. The kernel's retained ambient is the original source
  -- position; equal formal values or bytes cannot select the target supplier.
  let originalSource := opaque "same endpoint bytes" "schema-source" 71
  let originalTarget := opaque "same endpoint bytes" "schema-target" 72
  let originalHom := opaque "original defining map" "schema-input-map" 73
  let input ← ctor "arrow" #[originalSource, originalTarget, originalHom]
  let allocated ← IO.mkRef (0, 0)
  let values ← plan.foldData
    (fun root => match root with
      | .receiver => pure input
      | .parameter .. => throwError "the schema control invented a declaration parameter")
    (fun index slot earlier => do
      match slot.role with
      | .object _ =>
          allocated.modify fun (objects, arrows) => (objects + 1, arrows)
          pure (opaque s!"returned object {index}" "schema-output-object" (100 + index))
      | .map _ _ _ =>
          let some (domain, codomain) := slot.endpoints? earlier
            | throwError "the schema allocated a map before its exact endpoint slots"
          allocated.modify fun (objects, arrows) => (objects, arrows + 1)
          ctor "typedMap" #[domain, codomain,
            opaque s!"returned map {index}" "schema-output-map" (200 + index)]
      | .value => throwError "the complete kernel interface acquired an undeclared scalar port")
  unless (← allocated.get) == (1, 1) do
    throwError "the kernel schema did not retain its ambient and allocate only apex and defining map"
  let some output := plan.outputData? values
    | throwError "the schema lost its complete assembled result"
  let .ok ambient := output.project #[.field "args", .index 1]
    | throwError "the complete kernel result omitted its ambient position"
  unless ambient == originalSource && ambient != originalTarget do
    throwError "the routed result schema substituted an equal-valued endpoint supplier"
  let some projected ← plan.projectData? output
    | throwError "the complete schema could not project its own public field positions"
  unless projected == values do
    throwError "prospective assembly and actual projection disagree on exact scoped fields"
  -- Projection must preserve a changed supplier as changed data. The consuming
  -- result validator compares this exact retained slot to originalSource.
  let .ok apex := output.project #[.field "args", .index 0]
    | throwError "the complete result omitted its returned apex"
  let .ok inclusion := output.project #[.field "args", .index 2]
    | throwError "the complete result omitted its returned defining map"
  let changed ← ctor "arrow" #[apex, originalTarget, inclusion]
  if let some changedFields ← plan.projectData? changed then
    let mut foundRetainedDifference := false
    for ((slot, original), changed) in (plan.slots.zip projected).zip changedFields do
      if slot.node matches .retained .receiver _ then
        if original != changed then foundRetainedDifference := true
    unless foundRetainedDifference do
      throwError "the schema projection hid a changed supplier in a retained result field"
  logInfo "PASS: routed result positions preserve the retained ambient supplier and exact map endpoint order"

run_elab do
  let state ← registryState
  let some kernel := state.functor? ⟨"fun.arrows_modules.kernel"⟩
    | throwError "the schema control requires the existing module kernel functor"
  let method ← selectedMethod state kernel.id
  let receiver ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ ℤ ℤ))) none
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[receiver]
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let edge := EdgeRef.constructMap ConstructorId.arrow (.functor FunctorId.bilinModuleForget)
  let prefixAction ← Semantic.edgeFunctor state edge
  let transported ← Semantic.objOf prefixAction arrow
  let action ← registeredFunctorInstance kernel
  discard <| Semantic.objOf action (← methodArgument method transported)
  let action ← instantiateMVars action
  let prefixAction ← instantiateMVars prefixAction
  let slots ← RoutedResultPlan.parameterSlots method action #[(edge, prefixAction)]
  let first := slots.filter (·.actionIndex == 0)
  let second := slots.filter (·.actionIndex == 1)
  let some first := first[0]?
    | throwError "the accepted structural route omitted its original ring parameter"
  let some second := second[0]?
    | throwError "the accepted kernel method omitted its original ring parameter"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq first.expectedType second.expectedType <&&> isDefEq first.formal second.formal) do
    throwError "the parameter-position control no longer has the same complete ring parameter"
  unless first.actionIndex != second.actionIndex && first.dataIndex == 0 && second.dataIndex == 0 do
    throwError "equal declaration values collapsed distinct routed parameter positions"
  logInfo "PASS: equal routed parameter values keep their independent action and declaration positions"
