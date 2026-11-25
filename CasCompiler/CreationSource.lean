module

public import CasCompiler.PreparedCreationFamily
public import CasCompiler.LimitUniversalFamily
public import CasCompiler.SelectedField

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- Build the complete fixed creation demand from the retained formal owner. The source
let-bindings preserve one actual target cone and its exact universal record when lowered.
No provider is called while this source plan is formed. -/
opaque PreparedCreationFamily.completionSource (prepared : PreparedCreationFamily)
    (context : OpenContext) (owner : Expr) : MetaM Expr := do
  let selected ← prepared.selection context
  let some targetOwner := selected.source.ownerFamily
    | throwError "the created source lost its original target owner family"
  let parameters ← prepared.inputs.target.arguments.mapM fun argument =>
    argument.source.source.inContext context
  let coneSource ← prepared.target.markSelected targetOwner prepared.targetUniverses parameters
  let universalFamily ← LimitUniversalFamily.forId prepared.target.entry.id
  withLetDecl `targetCone (← inferType coneSource) coneSource fun cone => do
    let universalSource ← universalFamily.markSelected targetOwner
      prepared.targetUniverses parameters (some cone)
    withLetDecl `targetUniversal (← inferType universalSource) universalSource fun universal => do
      let source ← prepared.markArguments context owner cone universal
      let source ← mkLetFVars #[cone, universal] source
        (usedLetOnly := false) (generalizeNondepLet := false)
      check source
      if source.hasMVar || source.hasLevelMVar then
        throwError "the complete creation source has unresolved native inputs"
      return source

/-- Select the original native source cone from the complete LiftsToLimit record.
These are the declared structure projections, not another computation address.
Source: Mathlib/CategoryTheory/Limits/Creates.lean, LiftableCone and LiftsToLimit. -/
opaque creationResultCone (result : Expr) : MetaM Expr := do
  let lifted ← mkAppM ``CategoryTheory.LiftsToLimit.toLiftableCone #[result]
  mkAppM ``CategoryTheory.LiftableCone.liftedCone #[lifted]

/-- Complete the fixed creation once before selecting its actual source-cone field.
Ordinary lowering and native result projection retain the full predecessor chain. -/
opaque PreparedCreationFamily.coneSource (prepared : PreparedCreationFamily)
    (context : OpenContext) (owner : Expr) : MetaM Expr := do
  let cone ← creationResultCone (← prepared.completionSource context owner)
  selectedFieldAt prepared.construction ``CategoryTheory.Limits.LimitCone.cone owner cone

/-- Retain a whole-cone demand without preparing its computational constructor. The
original typed cone supplies only its native interface here. Lowering this owned marker
on a concrete native demand prepares the same complete raw or created source request. -/
opaque deferredLimitConeSource (owner : Expr) : MetaM (Option Expr) := do
  let some selected ← NativeLimitSelection.ofExpr? owner | return none
  let projection := if selected.source.colimit then
    ``CategoryTheory.Limits.ColimitCocone.cocone else
    ``CategoryTheory.Limits.LimitCone.cone
  let .mdata data body ← selectedFieldAt selected.source.construction projection owner
      selected.source.cone
    | throwError "the deferred cone lost its exact typed owner envelope"
  return some (.mdata (data.setBool `CasCompiler.selection.deferredCone true) body)

/-- The original complete cone plan of one explicit formal owner. This reuses the retained
source selection and its declared family; no equal native apex or diagram finds an owner. -/
opaque limitConeSource (context : OpenContext) (owner : Expr) : MetaM (Option Expr) := do
  let some selected ← NativeLimitSelection.ofExpr? owner | return none
  if let some creation ← PreparedCreationFamily.ofSelection context owner then
    return some (← creation.coneSource context owner)
  let some cone ← LimitFamily.wholeFrom owner
    | throwError "the original construction lost its complete native cone source"
  let projection := if selected.source.colimit then
    ``CategoryTheory.Limits.ColimitCocone.cocone else
    ``CategoryTheory.Limits.LimitCone.cone
  return some (← selectedFieldAt selected.source.construction projection owner cone)

end CasCompiler
