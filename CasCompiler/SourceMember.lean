module

public import CasCompiler.Surface
public import Lean.Meta.Structure
public import Lean.Meta.Sym.SymM

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

-- Reuse Language.bindSelectedReceiver's native structure telescope. All fields remain
-- metavariables until the complete receiver type determines them; no instance is chosen.
private def bindReceiver (row : MorphismEntry) (receiver : Expr) (slot : Nat) :
    MetaM (Option Expr) := do
  discard <| checkedDeclaration row.declaration
  let declaration ← mkConstWithFreshMVarLevels row.declaration
  let (parameters, binders, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let some parameter := parameters[slot]? | return none
  unless binders[slot]!.isExplicit do return none
  withConfig (fun config => { config with zetaDelta := false }) do
    unless ← expandSourceStructures (parameters.take slot) do return none
    unless ← isDefEq (← inferType parameter) (← inferType receiver) <&&>
        isDefEq parameter receiver do return none
    return some (← instantiateMVars (mkAppN declaration parameters))

/-- Prepare the unique registered family indexed by the actual selected receiver.
Reuse: Language.invariantOf's unique typed receiver rule, native declaration telescopes,
Lean.Meta.etaStructReduce and the registered morphism boundary check. -/
opaque sourceMemberFamily (receiver : NativeSourceJudgement) (name : String)
    (qualification : Option String := none) : TermElabM (Option NativeSourceJudgement) := do
  let some selected := receiver.category
    | return none
  let state ← semanticState
  let qualified ← qualification.mapM (selectCategory state)
  let mut candidates : Array (MorphismEntry × Nat) := #[]
  for row in state.morphisms do
    unless row.name == name && qualified.all (·.id == row.category) do continue
    discard <| checkedDeclaration row.declaration
    let info ← getConstInfo row.declaration
    let (_, binders, _) ← forallMetaTelescopeReducing info.type
    for slot in [:binders.size] do
      unless binders[slot]!.isExplicit do continue
      let applicable ← withoutModifyingState do
        return (← bindReceiver row receiver.value slot).isSome
      if applicable then candidates := candidates.push (row, slot)
  if candidates.isEmpty then return none
  let #[(row, slot)] := candidates
    | throwSemanticAmbiguity "several declared member parameters accept this selected receiver"
  let some original ← bindReceiver row receiver.value slot
    | throwError "the selected member changed its complete receiver boundary"
  let original ← instantiateMVars original
  if original.hasMVar || original.hasLevelMVar then
    throwUnsupportedSource "the selected member requires its complete declaration parameters"
  -- Contract only native structure eta terms back to their original projected owners.
  -- Lean.Meta.Structure.etaStructReduce requires the same actual owner in every field.
  let parameters ← original.getAppArgs.mapM fun parameter => do
    let parameter ← instantiateMVars parameter
    let some constructor ← isConstructorApp? parameter | return parameter
    unless isStructure (← getEnv) constructor.induct do return parameter
    let fields ← parameter.getAppArgs.mapM fun field =>
      withConfig (fun config => { config with zetaDelta := false }) <| withReducible (whnf field)
    let parameter ← Sym.foldProjs (mkAppN parameter.getAppFn fields)
    etaStructReduce parameter (fun _ => true)
  let #[category] := state.categories.filter (·.id == row.category)
    | throwError "the member family requires one complete result category"
  let (bundle, value) ← registeredExpressions (.inr row) category fun function _ => do
    unless ← isDefEq function original.getAppFn do
      throwError "the member family changed its whole source declaration"
    return mkAppN function parameters
  let value ← instantiateMVars value
  let proof ← mkExpectedTypeHint (← mkEqRefl original) (← mkEq original value)
  checkWithKernel proof
  let value ← withLetDecl (← mkFreshUserName `memberParameterAgreement) (← inferType proof) proof
    fun binding => mkLetFVars #[binding] value
      (usedLetOnly := false) (generalizeNondepLet := false)
  -- Keep the receiver's full chosen category beside the application as native data.
  let value ← withLetDecl (← mkFreshUserName `memberReceiverCategory)
    (← inferType selected.bundle) selected.bundle fun binding => mkLetFVars #[binding] value
      (usedLetOnly := false) (generalizeNondepLet := false)
  return some ⟨value, some ⟨.morphism, category.expression, bundle, none⟩⟩

end CasCompiler
