module

public import Lean.Meta.Structure

public section

namespace CasCompiler

open Lean Meta

/-- An exact field of one source-selected construction. Metadata is ignored by conversion;
the selection and projection identify a computational use, not a mathematical equality.
Reuse: Lean MData, as for sourceReference and retained runtime-value marks. -/
def selectedField (selection projection : Name) (value : Expr) : Expr :=
  .mdata (KVMap.empty.setName `CasCompiler.selection selection
    |>.setName `CasCompiler.selection.field projection) value

def selectedField? (data : MData) : Option (Name × Name) := do
  let selection := data.getName `CasCompiler.selection
  let field := data.getName `CasCompiler.selection.field
  if selection.isAnonymous || field.isAnonymous then none else some (selection, field)

/-- Rebuild the same checked record with exact selected identities on its callable results.
Its constructor supplies dependent field types; no endpoint or expression search is used.
Callers apply these actions only to the fixed input telescope of this source selection.
A different application requires a different selection identity. -/
def selectRecordActions (selection : Name) (record : Expr) : MetaM Expr := do
  let type ← whnf (← inferType record)
  let .const owner levels := type.getAppFn
    | throwError "a selected interface must be a record"
  let some info := getStructureInfo? (← getEnv) owner
    | throwError "a selected interface must have declared fields"
  let constructor := getStructureCtor (← getEnv) owner
  let mut result := mkAppN (mkConst constructor.name levels)
    (type.getAppArgs.extract 0 constructor.numParams)
  for field in info.fieldNames, index in [:info.fieldNames.size] do
    let some projection := info.getProjFn? index
      | throwError "a selected interface lost its projection"
    let value ← mkProjection record field
    let value ← forallTelescope (← inferType value) fun arguments _ => do
      mkLambdaFVars arguments (selectedField selection projection (mkAppN value arguments))
    result := mkApp result value
  check result
  return result

end CasCompiler
