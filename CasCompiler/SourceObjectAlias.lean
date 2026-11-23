module

public import CasCompiler.Surface
public import CasCompiler.FamilyConversion

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- Name an authored native object alias only after comparing its entire family under rigid
universes. The unchanged original arguments are applied after that check. A retained object
reference is never selected or replaced by native carrier equality. -/
def sourceNamedObjectAlias (category : CategoryId) (value : Expr) : MetaM Expr := do
  if (← sourceObjectReference? value).isSome then return value
  -- A whole-value mark or selection already denotes an actual source occurrence.
  -- Naming an unbound declaration cannot rewrite that occurrence's representation.
  if let .mdata _ _ := value then return value
  let state ← semanticState
  let body := value
  let .const declaration levels := body.getAppFn | return value
  let original ← checkedDeclaration declaration
  let direct := state.objects.filter fun row =>
    row.category == category && row.declaration == declaration
  if let #[row] := direct then
    return sourceReference ``ObjectEntry row.id.raw row.declaration value
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
  | #[] => return value
  | #[(row, aliasTerm)] =>
    unless names.length == levels.length do
      throwError "the native object alias lost its complete universe parameters"
    let named := mkAppN (aliasTerm.instantiateLevelParams names levels) body.getAppArgs
    unless ← isDefEq named value do
      throwError "the registered object alias changed its original native arguments"
    return sourceReference ``ObjectEntry row.id.raw row.declaration named
  | _ => throwSemanticAmbiguity "the native object family has several authored registered aliases"

end CasCompiler
