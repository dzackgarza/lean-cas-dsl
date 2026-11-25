module

public import CasCompiler.Surface
public import LeanCategories.Catalogue.FamilyFibration

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The original selected reindexing, its actual base map and receiver, and their one
native cartesian arrow. Neither endpoint is reconstructed by a separate object action. -/
structure NativeSourceCartesian where
  entry : FunctorEntry
  application : Expr
  realization : Expr
  baseMap : Expr
  receiver : Expr
  totalBundle : Expr
  arrow : Expr

/-- Open only the selected declaration's source aliases until its accepted canonical
reindexing interface is visible. Delta and beta substitution retain the original argument
positions. No recursor, matcher or mathematical operation is evaluated. -/
private partial def reindexApplication (expression : Expr)
    (seen : Std.HashSet Name := {}) : MetaM Expr := do
  let expression := expression.consumeMData.headBeta
  if expression.getAppFn.isConstOf ``CategoryFamilyRealization.reindexFunctor ||
      expression.getAppFn.isConstOf ``CategoryFamilyRealization.reindex then
    return expression
  if let .letE _ _ value body _ := expression then
    return ← reindexApplication (body.instantiate1 value) seen
  let .const name _ := expression.getAppFn
    | throwUnsupportedSource "the selected reindexing has no native canonical source application"
  if seen.contains name then
    throwUnsupportedSource "the selected reindexing requires computation to expose its source"
  let .defnInfo _ ← getConstInfo name
    | throwUnsupportedSource "the selected reindexing is not a native declaration alias"
  let some body ← withOptions (fun options => options.setBool `smartUnfolding false) <|
      unfoldDefinition? expression.getAppFn
    | throwUnsupportedSource "the selected reindexing has no available source definition"
  reindexApplication (body.betaRev expression.getAppRevArgs (preserveMData := true))
    (seen.insert name)

private def reindexInputs (application : Expr) : MetaM (Expr × Expr) := do
  let canonical ← reindexApplication application
  let info ← getFunInfoNArgs canonical.getAppFn canonical.getAppNumArgs
  let mut explicit := #[]
  for argument in canonical.getAppArgs, index in [:canonical.getAppNumArgs] do
    if (info.paramInfo[index]?.map (·.isExplicit)).getD false then
      explicit := explicit.push argument
  let #[realization, baseMap] := explicit
    | throwError "the canonical reindexing changed its native realization and base-map slots"
  return (realization, baseMap)

private def cartesianValue (realization receiver baseMap : Expr) : MetaM Expr := do
  let transport ← mkAppM ``CategoryFamilyRealization.transport #[realization]
  mkAppOptM ``CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift
    #[none, none, some transport, none, none, some receiver, some baseMap]

/-- Consume an accepted reindex declaration and its actual receiver through the canonical
family fibration. The registered declaration selects the family; its exact source spine
supplies the base map. Conversion checks validate those fixed choices and select nothing. -/
def sourceCartesian (entry : FunctorEntry) (application receiver : Expr) : MetaM Expr := do
  let state ← semanticState
  let #[original] := state.functors.filter (·.id == entry.id)
    | throwError "the cartesian source requires its unique registered reindexing"
  let .familyReindex family := original.expression.registrationKind
    | throwError "the cartesian source requires a registered family-reindex action"
  unless original.declaration == entry.declaration &&
      original.source.syntacticEq entry.source && original.target.syntacticEq entry.target do
    throwError "the cartesian source changed its accepted reindexing"
  discard <| checkedDeclaration entry.declaration
  let application ← instantiateMVars application
  unless application.consumeMData.getAppFn.isConstOf entry.declaration do
    throwError "the cartesian source lost its original declaration application"
  let functor ← sourceFunctorValue application
  let (source, _) ← functorCategoryBundles functor
  let domain ← mkAppM ``CategoryTheory.Bundled.α #[source]
  unless ← isDefEq (← inferType receiver) domain do
    throwError "the cartesian receiver is outside its complete selected source fibre"
  let (realization, baseMap) ← reindexInputs application
  let #[familyEntry] := state.categoryFamilies.filter (·.id == family)
    | throwError "the cartesian source lost its accepted family"
  let registered ← mkConstWithFreshMVarLevels familyEntry.realization
  unless ← isDefEq realization registered do
    throwError "the cartesian source changed its complete registered family realization"
  let arrow ← cartesianValue realization receiver baseMap
  let totalBundle ← mkAppM ``CategoryFamilyRealization.totalCat #[realization]
  let arrow ← selectMorphism arrow (some totalBundle)
  let mut retained := arrow
  for input in #[realization, baseMap, receiver, totalBundle, application.consumeMData] do
    retained ← mkAppM ``Function.const #[← inferType input, retained, input]
  return .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``NativeSourceCartesian
    |>.setString `CasCompiler.source.id entry.id.raw
    |>.setName `CasCompiler.source.declaration entry.declaration
    |>.setName `CasCompiler.source.application entry.declaration
    |>.setBool `CasCompiler.source.cartesian true) retained

/-- Recover only the complete original typed cartesian envelope. Scoped aliases retain
that envelope; equal endpoint types or other declaration occurrences cannot replace it. -/
partial def sourceCartesian? (value : Expr) : MetaM (Option NativeSourceCartesian) := do
  let expression ← instantiateMVars value
  match expression with
  | .mdata data body =>
    if !data.getBool `CasCompiler.source.cartesian then return ← sourceCartesian? body
    let #[entry] := (← semanticState).functors.filter
      (·.id.raw == data.getString `CasCompiler.source.id)
      | throwError "the retained cartesian source lost its original reindexing"
    unless data.getName `CasCompiler.source.kind == ``NativeSourceCartesian &&
        data.getName `CasCompiler.source.declaration == entry.declaration &&
        data.getName `CasCompiler.source.application == entry.declaration do
      throwError "the retained cartesian source changed its declaration witness"
    let mut current := body
    let mut fields := #[]
    for _ in [:5] do
      unless current.isAppOfArity ``Function.const 4 do
        throwError "the retained cartesian source lost an original native input"
      fields := fields.push current.getAppArgs[3]!
      current := current.getAppArgs[2]!
    let #[application, totalBundle, receiver, baseMap, realization] := fields
      | throwError "the retained cartesian source changed its complete native layout"
    unless application.consumeMData.getAppFn.isConstOf entry.declaration do
      throwError "the retained cartesian source changed its actual declaration application"
    let (originalRealization, originalBase) ← reindexInputs application
    unless realization == originalRealization && baseMap == originalBase do
      throwError "the retained cartesian source replaced an original source input"
    let expected ← sourceCartesian entry application receiver
    unless ← isDefEq current expected <&&>
        isDefEq totalBundle (← mkAppM ``CategoryFamilyRealization.totalCat #[realization]) do
      throwError "the retained cartesian source changed its native arrow or total category"
    return some ⟨entry, application, realization, baseMap, receiver, totalBundle, current⟩
  | .fvar id =>
    match (← id.getDecl).value? with
    | some original => sourceCartesian? original
    | none => pure none
  | .letE _ _ original body _ => sourceCartesian? (body.instantiate1 original)
  | _ =>
    if expression.isAppOfArity ``id 2 then sourceCartesian? expression.getAppArgs[1]!
    else pure none

end CasCompiler
