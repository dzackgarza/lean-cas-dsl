module

public import CasCompiler.SourceTypeOrigin

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The construction explicitly retained by source formation, together with this exact
receiver occurrence. The native interface is supplied by that construction's producer;
neither an equal apex nor a row/diagram search can create this selection. -/
structure NativeLimitSelection where
  private mk ::
  source : NativeSourceLimitSelection
  receiver : Expr

/-- One original cone component. Its index is the actual native diagram object selected by
the source reader, including a Discrete wrapper or dependent Fin evidence when present. -/
structure NativeLimitLegSelection where
  private mk ::
  construction : NativeLimitSelection
  index : Expr
  value : Expr

private def applicationValue (declaration : Name) (value : Expr) : MetaM Expr := do
  let .mdata data body := value
    | throwError "the construction lost its original typed application witness"
  unless data.getName `CasCompiler.source.application == declaration &&
      body.isAppOfArity ``Function.const 4 do
    throwError "the construction changed its original typed application witness"
  let application := body.getAppArgs[3]!
  unless application.consumeMData.getAppFn.isConstOf declaration do
    throwError "the construction changed its original registered declaration"
  return body.getAppArgs[2]!

/-- Inspect only authored metadata and known identity wrappers. A declaration body,
constructor matcher, arbitrary subterm or native alias never supplies a selection. -/
private partial def envelope? (key : Name) (value : Expr) :
    MetaM (Option (MData × Expr)) := do
  match ← instantiateMVars value with
  | .mdata data body =>
    if data.contains key then return some (data, body)
    let declaration := data.getName `CasCompiler.source.application
    if !declaration.isAnonymous then
      return ← envelope? key (← applicationValue declaration (.mdata data body))
    envelope? key body
  | value =>
    if value.isAppOfArity ``id 2 then
      return ← envelope? key value.getAppArgs[1]!
    return none

private def originalOwner (identity : Name) (owner : Expr) :
    MetaM NativeLimitSelection := do
  unless !identity.isAnonymous do
    throwError "the original construction has no shared selection identity"
  let some (category, receiver) ← sourceObjectOrigin? owner
    | throwError "the construction lost its original typed receiver"
  let some source := category.limit
    | throwError "the original receiver lost its selected construction"
  unless source.construction == identity do
    throwError "the receiver belongs to a different original construction selection"
  return ⟨source, receiver⟩

/-- Retain the original construction once at formation. Its complete native source owner
uses the existing typed owner envelope; the outer named descriptor remains unchanged. -/
opaque retainLimitConstruction (judgement : NativeSourceJudgement) :
    MetaM NativeSourceJudgement := do
  let some category := judgement.category
    | throwError "a selected construction requires its original category"
  let some selection := category.limit
    | throwError "a selected construction requires its original interface"
  unless !selection.construction.isAnonymous do
    throwError "a selected construction requires its formation identity"
  let .mdata data body := judgement.value
    | throwError "a selected construction requires its original source reference"
  unless data.getName `CasCompiler.source.kind == ``LimitEntry &&
      data.getName `CasCompiler.source.declaration == selection.declaration &&
      data.getString `CasCompiler.source.id == selection.row do
    throwError "the construction changed its original source reference"
  let some application ← sourceApplication? selection.declaration body
    | throwError "the construction lost its original registered application"
  let owner ← annotateSourceObject category judgement.value
  let body ← retainSourceApplication selection.declaration application owner
  let value := Expr.mdata
    (data.setName `CasCompiler.source.limit.construction selection.construction) body
  return { judgement with value }

/-- Read only the complete source selection retained by retainLimitConstruction. -/
opaque NativeLimitSelection.ofExpr? (value : Expr) :
    MetaM (Option NativeLimitSelection) := do
  let some (data, body) ← envelope? `CasCompiler.source.limit.construction value
    | return none
  let declaration := data.getName `CasCompiler.source.declaration
  let selected ← originalOwner (data.getName `CasCompiler.source.limit.construction)
    (← applicationValue declaration body)
  unless selected.source.declaration == declaration &&
      selected.source.row == data.getString `CasCompiler.source.id do
    throwError "the construction envelope changed its original named reference"
  return some selected

/-- Retain the exact receiver and exact typed index beside this unchanged native component.
Function.const transports both fields through closure/substitution without evaluating them. -/
opaque retainLimitLeg (category : NativeSourceCategory) (receiver index value : Expr) :
    MetaM Expr := do
  let some selection := category.limit
    | throwError "a selected leg requires its receiver's original construction"
  unless !selection.construction.isAnonymous do
    throwError "a selected leg requires its receiver's original selection identity"
  let owner ← annotateSourceObject category receiver
  let mut body := Expr.mdata
    (KVMap.empty.setBool `CasCompiler.source.limit.leg.payload true) value
  for field in #[owner, index].reverse do
    body ← mkAppM ``Function.const #[← inferType field, body, field]
  return .mdata
    (KVMap.empty.setName `CasCompiler.source.limit.leg selection.construction) body

/-- Read the two typed fields from the original component envelope. The receiver remains
its exact source occurrence and the index remains a native term, never a port ordinal. -/
opaque NativeLimitLegSelection.ofExpr? (value : Expr) :
    MetaM (Option NativeLimitLegSelection) := do
  let some (data, body) ← envelope? `CasCompiler.source.limit.leg value
    | return none
  unless body.isAppOfArity ``Function.const 4 do
    throwError "the selected leg lost its original typed receiver"
  let owner := body.getAppArgs[3]!
  let body := body.getAppArgs[2]!
  unless body.isAppOfArity ``Function.const 4 do
    throwError "the selected leg lost its original typed index"
  let index := body.getAppArgs[3]!
  let .mdata delimiter original := body.getAppArgs[2]!
    | throwError "the selected leg lost its original component boundary"
  unless delimiter.size == 1 &&
      (delimiter.get? `CasCompiler.source.limit.leg.payload : Option Bool) == some true do
    throwError "the selected leg changed its original typed field count"
  let construction ← originalOwner (data.getName `CasCompiler.source.limit.leg) owner
  return some ⟨construction, index, original⟩

/-- Form a component on an explicitly supplied cone and native index. The caller supplies
the actual retained parent; conversion only checks its declared type and never chooses it.
No projection is reduced and no mathematical declaration or matcher is evaluated. -/
opaque NativeLimitSelection.legAt (selection : NativeLimitSelection) (cone index : Expr) :
    MetaM Expr := do
  unless ← isDefEq (← inferType cone) (← inferType selection.source.cone) do
    throwError "the retained cone has a different complete native interface"
  let transformation ← mkAppM (if selection.source.colimit then
    ``CategoryTheory.Limits.Cocone.ι else ``CategoryTheory.Limits.Cone.π) #[cone]
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation]
  let value := mkApp component index
  check value
  return value

end CasCompiler
