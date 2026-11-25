module

public import CasCompiler.Layout

public section

namespace CasCompiler

open Lean Meta

/-- Reopen only native constructor type telescopes along an already selected record path.
Earlier field terms are the original source projections; annotations are attached at the
declared projection positions before substituting them into the field's native type family.
No returned data or reconstructed record enters this type-schema traversal. -/
private partial def annotatedFieldTypeAt (type actual : Expr) (path : List Name)
    (nativePrefix : Array Name) (marks : Array (Array Name × Nat)) : MetaM Expr := do
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
        let original := match marks.find? (·.1 == position) with
          | none => original
          | some (_, key) => .mdata (KVMap.empty.setNat `CasCompiler.lower.value key) original
        previous := previous.push original
      let originalType ← inferType fields[index]!
      let fieldType := originalType.replaceFVars (fields.extract 0 index) previous
      let free := collectFVars {} fieldType
      if fields.any (fun field => free.fvarSet.contains field.fvarId!) then
        throwError "a native field type prefix leaked an abstract constructor field"
      check fieldType
      let next ← mkProjection actual information.fieldNames[index]!
      unless ← isDefEq (← inferType next) fieldType do
        throwError "native field type instantiation changed its original declared interface"
      annotatedFieldTypeAt fieldType next rest (nativePrefix.push projection) marks

/-- A checked type-only view at an exact native descendant. Original proof/implicit field
positions are retained during traversal; only explicitly supplied native paths are annotated. -/
opaque SourceLayout.annotatedFieldType (source target : SourceLayout)
    (marks : Array (Array Name × Nat)) : MetaM ClosedTerm := do
  let path ← source.projectionPathTo target
  source.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let type ← annotatedFieldTypeAt (← inferType expression) expression path.toList #[] marks
    let target ← target.source.inContext context
    unless ← isDefEq (← inferType target) type do
      throwError "a field prefix changed its already prepared native target"
    context.close type

end CasCompiler
