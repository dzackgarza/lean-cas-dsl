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
    let reduced := value.headBeta
    if reduced == value then return none
    sourceObjectReference? reduced

end CasCompiler
