module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.LimitFamily

public section

namespace CasCompiler

open Lean Meta CasCatalogue


def LimitUniversalFamily.operation (family : LimitUniversalFamily) : String :=
  family.presentation.operation ++ "#" ++ family.projection.getString!

def LimitUniversalFamily.input (family : LimitUniversalFamily) : String :=
  family.operation ++ "#input"

def LimitUniversalFamily.universeParams (family : LimitUniversalFamily) : List Name :=
  family.presentation.universeParams

def LimitUniversalFamily.parameterCount (family : LimitUniversalFamily) : Nat :=
  family.presentation.parameterCount


def LimitUniversalFamily.path (family : LimitUniversalFamily) : Array Name :=
  #[family.projection]



opaque LimitUniversalFamily.forId (id : LimitId) : MetaM LimitUniversalFamily :=
    withLCtx {} #[] do
  let presentation ← LimitFamily.forId id
  let projection := if presentation.entry.colimit then
    ``CategoryTheory.Limits.ColimitCocone.isColimit
    else ``CategoryTheory.Limits.LimitCone.isLimit
  forallTelescopeReducing (← inferType presentation.presentationFamily) fun parameters _ => do
    unless parameters.size == presentation.parameterCount do
      throwError "the universal family changed its complete original parameter telescope"
    let selected := mkAppN presentation.presentationFamily parameters
    let universal ← mkAppM projection #[selected]
    if ← isProof universal then
      throwError "the original universal interface was replaced by a proof"
    let family ← mkLambdaFVars parameters universal
      (usedOnly := false) (usedLetOnly := false)
    check family
    if family.hasMVar || family.hasLevelMVar then
      throwError "the universal family has an unresolved original native parameter"
    return ⟨presentation, projection, family, ← inferType family⟩



def LimitUniversalFamily.selectedAtOwner [Monad m] [MonadLiftT MetaM m]
    (family : LimitUniversalFamily) (owner : SelectedLimitOwner Expr)
    (levels : List Level) (parameters : Array Expr)
    (select : SourceSelection Expr → Option Expr → m Expr)
    (cone : Option Expr := none) : m (SourceSelection Expr) := do
  unless levels.length == family.universeParams.length &&
      parameters.size == family.parameterCount do
    liftM (m := MetaM) <| throwError "the universal request changed its complete native parameter telescope"
  let presentation := mkAppN
    (family.presentation.presentationFamily.instantiateLevelParams
      family.universeParams levels) parameters
  liftM (m := MetaM) <| check presentation
  if presentation.hasMVar || presentation.hasLevelMVar then
    liftM (m := MetaM) <| throwError "the universal request has unresolved original native parameters"
  let selected ← liftM (m := MetaM) <| family.presentation.ownerAt owner parameters
  unless selected.source.interface.presentation.equal presentation do
    liftM (m := MetaM) <| throwError "the universal request changed its original target presentation"
  let universal ← liftM (m := MetaM) <| mkAppM family.projection #[selected.source.interface.presentation]
  let nativeCone ← liftM (m := MetaM) <|
    mkAppM family.presentation.coneProjection #[selected.source.interface.presentation]
  let cone ← match cone with
    | some cone => pure cone
    | none => do
      let cone ← liftM (m := MetaM) <| family.presentation.selectedAtOwner owner levels parameters
      select cone none
  liftM (m := MetaM) <| check cone
  unless ← liftM (m := MetaM) <| isDefEq (← inferType cone) (← inferType nativeCone) do
    liftM (m := MetaM) <| throwError "the retained universal input changed its original native cone interface"
  if cone.hasMVar || cone.hasLevelMVar then
    liftM (m := MetaM) <| throwError "the retained universal cone has unresolved native parameters"
  return {
    value := universal
    observation := some (.limit family.presentation.entry)
    originalApplication := some presentation
    application := some {
      family := .limitUniversal family, universes := levels, parameters,
      arguments := #[cone], owner := some selected.receiver, ownerSelection := some owner }
    limit := some selected }

end CasCompiler
