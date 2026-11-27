module

public import CasCompiler.Layout

public section

namespace CasCompiler

open Lean Meta




private partial def fieldTypeAt (context : OpenContext) (type actual : Expr) (path : List Name)
    (nativePrefix : Array Name) (replacements : Array (Array Name × Expr)) : MetaM Expr := do
  match path with
  | [] => return type
  | projection :: rest =>
    let normalized ← whnf type
    let .const name levels := normalized.getAppFn
      | throwError "a field type prefix lost its native record declaration"
    let some information := getStructureInfo? (← getEnv) name
      | throwError "a field type prefix requires its original native record"
    let some index := (Array.range information.fieldNames.size).find? fun index =>
        information.getProjFn? index == some projection
      | throwError "a field type prefix selected an undeclared native projection"
    let constructor := getStructureCtor (← getEnv) name
    let applied := mkAppN (mkConst constructor.name levels)
      (normalized.getAppArgs.extract 0 constructor.numParams)
    forallTelescope (← inferType applied) fun fields _ => do
      unless fields.size == information.fieldNames.size do
        throwError "a native field type prefix changed its full constructor telescope"
      let mut previous := #[]
      for earlier in [:index] do
        let original ← mkProjection actual information.fieldNames[earlier]!
        let some declaration := information.getProjFn? earlier
          | throwError "a native field type prefix lost an original projection declaration"
        let position := nativePrefix.push declaration
        let replacement := (replacements.find? (·.1 == position)).map (·.2) |>.getD original
        let expected := (← inferType fields[earlier]!).replaceFVars
          (fields.extract 0 earlier) previous
        unless ← context.withOriginalSources #[← inferType replacement, expected] fun types =>
            isDefEq types[0]! types[1]! do
          throwError "an earlier native field binder has an incompatible declared type"
        previous := previous.push replacement
      let originalType ← inferType fields[index]!
      let fieldType := originalType.replaceFVars (fields.extract 0 index) previous
      let free := collectFVars {} fieldType
      if fields.any (fun field => free.fvarSet.contains field.fvarId!) then
        throwError "a native field type prefix leaked an abstract constructor field"
      check fieldType
      let next ← mkProjection actual information.fieldNames[index]!
      unless ← context.withOriginalSources #[← inferType next, fieldType] fun types =>
          isDefEq types[0]! types[1]! do
        throwError "native field type instantiation changed its original declared interface"
      fieldTypeAt context fieldType next rest (nativePrefix.push projection) replacements



opaque SourceLayout.fieldTypeInContext (source target : SourceLayout) (context : OpenContext)
    (replacements : Array (Array Name × Expr)) : MetaM Expr := do
  let path ← source.projectionPathTo target
  let expression ← source.source.inContext context
  let type ← fieldTypeAt context (← inferType expression) expression path.toList #[] replacements
  let target ← target.source.inContext context
  unless ← context.withOriginalSources #[← inferType target, type] fun types =>
      isDefEq types[0]! types[1]! do
    throwError "a field prefix changed its already prepared native target"
  return type

end CasCompiler
