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
    for earlier in parameters.take slot do
      let earlier ← instantiateMVars earlier
      unless earlier.isMVar do continue
      let type ← whnfR (← inferType earlier)
      let some name := type.getAppFn.constName? | continue
      unless isStructure (← getEnv) name do continue
      let .inductInfo info ← getConstInfo name | continue
      let [constructor] := info.ctors | continue
      discard <| checkedDeclaration constructor
      let constructor ← mkConstWithFreshMVarLevels constructor
      let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
      unless ← isDefEq result type do return none
      unless ← isDefEq earlier (mkAppN constructor fields) do return none
    unless ← isDefEq (← inferType parameter) (← inferType receiver) <&&>
        isDefEq parameter receiver do return none
    return some (← instantiateMVars (mkAppN declaration parameters))

/-- Prepare the unique registered family indexed by the actual selected receiver.
Reuse: Language.invariantOf's unique typed receiver rule, native declaration telescopes,
Lean.Meta.etaStructReduce and the registered morphism boundary check. -/
opaque sourceMemberFamily (receiver : NativeSourceJudgement) (name : String)
    (qualification : Option String := none) : TermElabM NativeSourceJudgement := do
  let some selected := receiver.category
    | throwUnsupportedSource "member family application requires its selected object or map"
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
  let #[(row, slot)] := candidates
    | if candidates.isEmpty then
        throwError "no declared member family accepts this complete selected receiver"
      else
        throwSemanticAmbiguity "several declared member parameters accept this selected receiver"
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
  return ⟨value, some ⟨.morphism, category.expression, bundle, none⟩⟩

end CasCompiler
