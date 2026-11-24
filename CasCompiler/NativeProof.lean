module

public import CasCompiler.Declaration
public import Lean.Elab.MutualDef

public section

namespace CasCompiler

open Lean Meta Elab Term

/-- Finish only the native recursive declarations formed by the current proof. Native
closure conversion owns their captured locals, instances, recursion and termination hints.
The ordinary declaration pipeline then fixes universes and checks their actual bodies.
Source: Lean v4.33.0 `MutualDef.elabMutualDef` and `PreDefinition.Main.addPreDefinitions`. -/
private def finishProofLetRecs (proof : Expr) : TermElabM Expr := do
  let pending ← getLetRecsToLift
  if pending.isEmpty then return proof
  let docContext := (← getLCtx, ← getLocalInstances)
  let declarations ← MutualClosure.main #[] #[] #[] #[] pending
  let declarations ← withLevelNames [] <| levelMVarToParamTypesPreDecls declarations
  let declarations ← instantiateMVarsAtPreDecls declarations
  let declarations ← shareCommonPreDefs declarations
  let declarations ← fixLevelParams declarations (← getLevelNames) []
  addPreDefinitions docContext declarations
  -- Native declaration elaboration may log an error and recover with a sorry. Preserve
  -- every native error before inspecting the declarations, including an unused let-rec.
  let errors := (← Core.getMessageLog).reportedPlusUnreported.toList.filter fun message =>
    message.severity matches .error
  unless errors.isEmpty do
    throwError (MessageData.joinSep (errors.map (·.data)) Format.line)
  for declaration in declarations do
    discard <| checkedDeclaration declaration.declName
  -- `fixLevelParams` updates predefinitions. A standalone proof is not a new main
  -- declaration, so apply that same exact declaration-name substitution to its original
  -- instantiated expression. No helper body or source local is unfolded or substituted.
  let levels : NameMap (List Level) := declarations.foldl (init := {}) fun result declaration =>
    result.insert declaration.declName (declaration.levelParams.map mkLevelParam)
  let proof ← instantiateMVars proof
  return proof.replace fun expression =>
    match expression with
    | .const name _ => (levels.find? name).map (mkConst name)
    | _ => none

/-- Complete one formal proof through Lean's native declaration machinery before it is
closed into a source term. The caller's pending let-recs are isolated and restored; an
invalid proof rolls back its native declarations while retaining its original diagnostics.
Successful completion preserves the current environment and the exact original proof. -/
opaque completeNativeProof (proposition : Expr) (elaborate : TermElabM Expr) : TermElabM Expr := do
  let saved : Term.SavedState ← saveState
  let outerPending ← getLetRecsToLift
  let outerMessages ← Core.getMessageLog
  modify fun state => { state with letRecsToLift := [] }
  Core.resetMessageLog
  try
    let proof ← withoutExporting do
      let name ← mkAuxDeclName (kind := `_sourceProof)
      withDeclName name <| withOptions (Elab.async.set · false) do
        finishProofLetRecs (← elaborate)
    let messages ← Core.getMessageLog
    let errors := messages.reportedPlusUnreported.toList.filter fun message =>
      message.severity matches .error
    unless errors.isEmpty do
      throwError (MessageData.joinSep (errors.map (·.data)) Format.line)
    check proof
    unless ← isDefEq (← inferType proof) proposition do
      throwError (← mkTypeMismatchError none proof (← inferType proof) proposition)
    modify fun state => { state with letRecsToLift := outerPending }
    Core.setMessageLog (outerMessages ++ messages)
    return proof
  catch error =>
    let messages ← Core.getMessageLog
    saved.restore
    Core.setMessageLog (outerMessages ++ messages)
    throw error

end CasCompiler
