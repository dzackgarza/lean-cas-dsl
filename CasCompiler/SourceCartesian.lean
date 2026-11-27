module

public import CasCompiler.SelectionData

public import CasCompiler.Surface
public import LeanCategories.Catalogue.FamilyFibration

public section

namespace CasCompiler

open Lean Meta CasCatalogue





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




def sourceCartesian (entry : FunctorEntry) (application receiver : Expr) :
    MetaM (SourceSelection Expr) := do
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
  return {
    value := arrow
    category := some ⟨.morphism, .familyTotal family, totalBundle, none, none⟩
    observation := some (.functor entry)
    originalApplication := some application
    cartesian := some ⟨entry, application, realization, baseMap, receiver, totalBundle, arrow⟩ }

end CasCompiler
