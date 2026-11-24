module

public import CasCompiler.SelectedMorphism
public import LeanCategories.Catalogue.Registry.Entry

public section

namespace CasCompiler

open Lean Meta

/-- Retain an actual selected catalogue reference beside its complete native expression.
Reuse: Lean MData/KVMap, preserved by native closure and ignored by kernel conversion. -/
def sourceReference (kind : Name) (id : String) (declaration : Name) (value : Expr) : Expr :=
  .mdata (KVMap.empty |>.setName `CasCompiler.source.kind kind
    |>.setString `CasCompiler.source.id id
    |>.setName `CasCompiler.source.declaration declaration) value

/-- Retain the source-visible selection of a derived value. Its actual computation already
has its own reference on the exact declaration application used to form this value; this
outer observation does not select or retag any native subexpression during lowering. -/
def sourceDerivedReference (kind : Name) (id : String) (declaration : Name)
    (value : Expr) : Expr :=
  .mdata (KVMap.empty |>.setName `CasCompiler.source.kind kind
    |>.setString `CasCompiler.source.id id
    |>.setName `CasCompiler.source.declaration declaration
    |>.setBool `CasCompiler.source.derived true) value

/-- Keep the actual registered application beside the value formed from it. The typed
`Function.const` argument survives native context closure and substitution; its value remains
definitionally unchanged. No declaration occurrence is recovered from the value's subterms. -/
def retainSourceApplication (declaration : Name) (application value : Expr) : MetaM Expr := do
  let application ← instantiateMVars application
  unless application.consumeMData.getAppFn.isConstOf declaration do
    throwError "the source application does not retain its actual registered declaration"
  let body ← mkAppM ``Function.const #[← inferType application, value, application]
  return .mdata (KVMap.empty.setName `CasCompiler.source.application declaration) body

/-- Read only the application retained at formation. Surrounding metadata may be skipped;
native aliases, equal carriers and nested occurrences never choose another application. -/
partial def sourceApplication? (declaration : Name) (value : Expr) : MetaM (Option Expr) := do
  let value ← instantiateMVars value
  let .mdata data body := value | return none
  let retained := data.getName `CasCompiler.source.application
  if retained.isAnonymous then return ← sourceApplication? declaration body
  unless retained == declaration && body.isAppOfArity ``Function.const 4 do
    throwError "the source application lost its original registered declaration"
  let application := body.getAppArgs[3]!
  unless application.consumeMData.getAppFn.isConstOf declaration do
    throwError "the retained source application has a different declaration"
  return some application

/-- A selected named value with the exact native application that formed it. -/
def sourceReferenceAt (kind : Name) (id : String) (declaration : Name)
    (application value : Expr) : MetaM Expr := do
  return sourceReference kind id declaration
    (← retainSourceApplication declaration application value)

/-- Read an object reference through original native aliases and verify its retained declaration. -/
partial def sourceObjectReference? (value : Expr) : MetaM (Option (CasCatalogue.ObjectId × Name)) := do
  if let some endpoint := selectedEndpoint? (← instantiateMVars value) then
    return ← sourceObjectReference? endpoint
  let value ← instantiateMVars value
  match value with
  | .mdata data body =>
    if data.getName `CasCompiler.source.kind == ``CasCatalogue.ObjectEntry then
      let declaration := data.getName `CasCompiler.source.declaration
      unless body.consumeMData.getAppFn.constName? == some declaration do
        throwError "the source object reference does not retain its actual declaration"
      return some (⟨data.getString `CasCompiler.source.id⟩, declaration)
    sourceObjectReference? body
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => sourceObjectReference? value
    | none => pure none
  | _ =>
    if value.isAppOfArity ``Function.const 4 then
      return ← sourceObjectReference? value.getAppArgs[2]!
    let reduced := value.headBeta
    if reduced == value then return none
    sourceObjectReference? reduced

end CasCompiler
