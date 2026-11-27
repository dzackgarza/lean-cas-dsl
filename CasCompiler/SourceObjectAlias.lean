module

public import CasCompiler.Surface
public import CasCompiler.FamilyConversion

public section

namespace CasCompiler

open Lean Meta CasCatalogue




def sourceNamedObjectAlias (category : CategoryId) (source : SourceSelection Expr) :
    MetaM (SourceSelection Expr) := do


  if source.value.isFVar || !source.formalBindings.isEmpty ||
      source.reference.isSome || source.observation.isSome || source.originalApplication.isSome ||
      source.application.isSome || source.admission.isSome || source.category.isSome ||
      source.typeOrigin.isSome || source.elementOwner.isSome || source.pointOrigin.isSome ||
      source.pointRequest.isSome || source.isoOrigin.isSome || source.field.isSome ||
      source.endpoint.isSome || source.limit.isSome || source.leg.isSome || source.cell.isSome ||
      source.cartesian.isSome || source.presentationEndpoints.isSome || source.routedInputs.isSome ||
      source.legOrdinal.isSome || !source.carrierRoutes.isEmpty || source.preferredRoute.isSome ||
      source.creationOwner.isSome then return source
  let state ← semanticState
  let #[categoryEntry] := state.categories.filter (·.id == category)
    | throwSemanticAmbiguity "the native object alias requires one complete registered category"
  let body := source.value
  let .const declaration levels := body.getAppFn | return source
  let original ← checkedDeclaration declaration
  let direct := state.objects.filter fun row =>
    row.category == category && row.declaration == declaration
  if let #[row] := direct then
    return { source with reference := some (.named (.registered (.inl row) categoryEntry)) }
  unless direct.isEmpty do
    throwSemanticAmbiguity "the native object declaration has several registered source names"
  let names ← original.levelParams.mapM fun _ => mkFreshUserName `objectAliasUniverse
  let rigid := mkConst declaration (names.map Level.param)
  let mut aliases : Array (ObjectEntry × Expr) := #[]
  for row in state.objects do
    unless row.category == category do continue
    let candidate ← withoutModifyingState do
      let info ← checkedDeclaration row.declaration
      let universes ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      let aliasTerm := mkConst row.declaration universes
      unless ← isDefEq (← inferType rigid) (← inferType aliasTerm) do return none
      let aliasTerm ← instantiateMVars aliasTerm
      if aliasTerm.hasMVar || aliasTerm.hasLevelMVar then return none
      let some _ ← sourceFamilyConversion rigid aliasTerm #[] | return none
      return some aliasTerm
    if let some aliasTerm := candidate then aliases := aliases.push (row, aliasTerm)
  match aliases with
  | #[] => return source
  | #[(row, aliasTerm)] =>
    unless names.length == levels.length do
      throwError "the native object alias lost its complete universe parameters"
    let named := mkAppN (aliasTerm.instantiateLevelParams names levels) body.getAppArgs
    unless ← isDefEq named source.value do
      throwError "the registered object alias changed its original native arguments"
    return { source with
      value := named
      reference := some (.named (.registered (.inl row) categoryEntry)) }
  | _ => throwSemanticAmbiguity "the native object family has several authored registered aliases"

end CasCompiler
