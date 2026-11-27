module

public import CasCompiler.PreparedCreationFamily
public import CasCompiler.LimitUniversalFamily

public section

namespace CasCompiler

open Lean Meta CasCatalogue



opaque PreparedCreationFamily.completionSource
    [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (prepared : PreparedCreationFamily) (identities : CasRuntime.IdentitySupply)
    (context : OpenContext) (selections : SourceSelectionScope Expr) (owner : Expr)
    (action : OpenContext → SourceSelectionScope Expr → Expr → m α) : m α := do
  let (targetOwner, parameters, coneSource, selections) ← liftM (m := MetaM) do
    let targetOwner ← prepared.targetOwner.mapM (·.inContext context)
    let parameters ← prepared.inputs.target.arguments.mapM fun argument =>
      argument.source.source.inContext context
    let coneSource ← prepared.target.selectedAtOwner targetOwner
      prepared.targetUniverses parameters
    let selections ← SourceSelectionScope.merge selections (← prepared.selections.inContext context)
    pure (targetOwner, parameters, coneSource, selections)
  SourceSelectionScope.withBinding identities selections context coneSource
      fun context selections cone => do
    let (universalSource, universalType) ← liftM (m := MetaM) do
      let family ← LimitUniversalFamily.forId prepared.target.entry.id
      unless (SelectedApplicationFamily.limit family.presentation).exactlyMatches
          (.limit prepared.target) do
        throwError "the creation target universal changed its complete accepted presentation"
      let universalSource ← family.selectedAtOwner targetOwner prepared.targetUniverses parameters
        (fun _ _ => throwError "the explicit creation cone cannot be replaced") (some cone)
      let universalType ← mkAppM
        (if prepared.target.entry.colimit then
          ``CategoryTheory.Limits.IsColimit else ``CategoryTheory.Limits.IsLimit) #[cone]
      pure (universalSource, universalType)
    SourceSelectionScope.withBinding identities selections context universalSource
        (fun context selections universal => do
          let selected ← liftM (m := MetaM) <|
            prepared.selectedArguments context owner cone universal
          SourceSelectionScope.withBinding identities selections context selected action)
        (declaredType := some universalType)


opaque creationResultCone (result : Expr) : MetaM Expr := do
  let lifted ← mkAppM ``CategoryTheory.LiftsToLimit.toLiftableCone #[result]
  mkAppM ``CategoryTheory.LiftableCone.liftedCone #[lifted]


opaque PreparedCreationFamily.coneSource
    [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (prepared : PreparedCreationFamily) (identities : CasRuntime.IdentitySupply)
    (context : OpenContext) (selections : SourceSelectionScope Expr) (owner : Expr)
    (action : OpenContext → SourceSelectionScope Expr → Expr → m α) : m α :=
  prepared.completionSource identities context selections owner fun context selections result => do
    let cone ← liftM (m := MetaM) <| creationResultCone result
    let selected : SourceSelection Expr := {
      value := cone
      field := some {
        selection := prepared.construction
        projection := ``CategoryTheory.Limits.LimitCone.cone
        owner } }
    SourceSelectionScope.withBinding identities selections context selected action



opaque deferredLimitConeSource (owner : Expr) (source : SourceSelection Expr) :
    MetaM (Option (SourceSelection Expr)) := do
  let some selected := source.limit | return none
  let projection := if selected.source.colimit then
    ``CategoryTheory.Limits.ColimitCocone.cocone else ``CategoryTheory.Limits.LimitCone.cone
  return some {
    value := selected.source.cone
    field := some {
      selection := selected.source.construction
      projection
      owner
      deferredCone := true } }


opaque limitConeSource [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (identities : CasRuntime.IdentitySupply) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (owner : Expr) (source : SourceSelection Expr)
    (action : OpenContext → SourceSelectionScope Expr → Option Expr → m α) : m α := do
  let some selected := source.limit | return ← action context selections none
  if let some (family, target) := source.creationOwner then
    let prepared ← liftM (m := MetaM) do
      let some prepared ← PreparedCreationFamily.ofSelection context owner selected
          family target selections
        | throwError "the selected created cone lost its complete original creation"
      pure prepared
    return ← prepared.coneSource identities context selections owner fun context selections cone =>
      action context selections (some cone)
  let cone ← liftM (m := MetaM) do
    let some original := selected.source.ownerFamily
      | throwError "the selected cone lost its exact original owner-template binding"
    let template ← SelectedLimitOwner.ofBinding context selections original
    let some family := source.limitFamily
      | throwError "the selected cone lost its complete original limit family"
    let some cone ← LimitFamily.wholeFrom family selected template
      | throwError "the original construction lost its complete native cone source"
    let some (.limit entry) := source.reference.orElse (fun _ => source.observation)
      | throwError "the selected cone lost its full independently selected limit row"
    let some application := cone.application
      | throwError "the selected cone lost its complete accepted family"
    let .limit family := application.family
      | throwError "the selected cone changed its original accepted family"
    unless reprStr entry == reprStr family.entry do
      throwError "the selected cone changed its complete independent limit row"
    let projection := if selected.source.colimit then
      ``CategoryTheory.Limits.ColimitCocone.cocone else ``CategoryTheory.Limits.LimitCone.cone
    pure { cone with field := some { selection := selected.source.construction, projection, owner } }
  SourceSelectionScope.withBinding identities selections context cone
    fun context selections value => action context selections (some value)

end CasCompiler
