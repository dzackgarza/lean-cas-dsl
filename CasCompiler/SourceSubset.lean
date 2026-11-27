module

public import CasCompiler.Surface
import CasCompiler.SourceTypeOrigin
public import CasCompiler.SourcePointOrigin

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue




def sourcePowerObject? (type : Expr) : SourceReadM (Option NativePowerObject) := do
  let selected ← SourceReadM.selection? type
  let (native, objects) ← registeredSourceDomain type
  if selected.isSome && objects.isEmpty then return none
  let state ← semanticState
  let mut found := #[]
  for row in state.powerObjects do
    let #[object] := state.objects.filter (·.id == row.object)
      | liftM (m := TermElabM) <| throwError "the registered power object {row.id.raw} has no unique original object family"
    let #[category] := state.categories.filter (·.id == object.category)
      | liftM (m := TermElabM) <| throwError "the registered power object {row.id.raw} has no complete original category"
    unless objects.isEmpty || objects.any (fun original => reprStr original == reprStr object) do
      continue
    discard <| checkedDeclaration object.declaration
    let family ← mkConstWithFreshMVarLevels object.declaration
    let base ← mkFreshExprMVar none
    let applicable ← liftM (m := TermElabM) <| withoutModifyingState do
      let object ← elabAppArgs family #[] #[Arg.expr base] none false false
      isDefEq object native
    unless applicable do continue
    let candidate ← elabAppArgs family #[] #[Arg.expr base] none false false
    discard <| isDefEq candidate native
    let base ← if objects.isEmpty then liftM (m := MetaM) (instantiateMVars base) else do
      let application := native.consumeMData.headBeta
      unless application.getAppFn.isConstOf object.declaration do
        liftM (m := TermElabM) <| throwError "the power object lost its original declared application"
      let information ← getFunInfoNArgs application.getAppFn application.getAppNumArgs
      let originals := (application.getAppArgs.zip information.paramInfo).filterMap
        fun (argument, parameter) => if parameter.isExplicit then some argument else none
      let #[original] := originals
        | liftM (m := TermElabM) <| throwError "the power object changed its original base position"
      unless ← isDefEq base original do
        liftM (m := TermElabM) <| throwError "the power object changed its original native base"
      pure original
    if base.hasMVar || base.hasLevelMVar then
      liftM (m := TermElabM) <| throwError "the registered power object is not determined by its native type"
    found := found.push ⟨row, object, category, base⟩
  match found with
  | #[] => return none
  | #[selected] => return some selected
  | _ => liftM (m := TermElabM) <| throwSemanticAmbiguity "the native type is the object of several registered power objects"


def sourcePowerObjectAt (base : Expr) : SourceReadM NativePowerObject := do
  let state ← semanticState
  let mut found := #[]
  for row in state.powerObjects do
    let #[object] := state.objects.filter (·.id == row.object)
      | liftM (m := TermElabM) <| throwError "the registered power object {row.id.raw} has no unique original object family"
    let #[category] := state.categories.filter (·.id == object.category)
      | liftM (m := TermElabM) <| throwError "the registered power object {row.id.raw} has no complete original category"
    discard <| checkedDeclaration object.declaration
    let family ← mkConstWithFreshMVarLevels object.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let some parameter := parameters[0]?
      | liftM (m := TermElabM) <| throwError "the registered power object {row.id.raw} has no base parameter"
    if ← liftM (m := MetaM) <| withoutModifyingState
        (isDefEq (← inferType parameter) (← inferType base)) then
      found := found.push (⟨row, object, category, base⟩ : NativePowerObject)
  match found with
  | #[selected] => return selected
  | #[] => liftM (m := TermElabM) <| throwUnsupportedSource "no registered power object accepts this base object"
  | _ => liftM (m := TermElabM) <| throwSemanticAmbiguity "several registered power objects accept this base object"


private def atBase (power : NativePowerObject) (declaration : Name) (arguments : Array Expr) :
    SourceReadM Expr := do
  discard <| checkedDeclaration declaration
  let function ← mkConstWithFreshMVarLevels declaration
  elabRetainedSourceApplication function (#[power.base] ++ arguments)




def sourceGlobalValue (power : NativePowerObject) (element : Expr) (expected : Option Expr) :
    SourceReadM Expr := do
  discard <| checkedDeclaration power.row.point
  let point ← mkConstWithFreshMVarLevels power.row.point
  let function ← sourceSetFunction element
  let value ← elabRetainedSourceApplication function #[point]
  let selected ← retainSourcePoint element { value, powerObject := some power }
  SourceReadM.select selected expected





def sourceSubsetLiteral (power : NativePowerObject) (elements : Array Expr) (expected : Expr) :
    SourceReadM Expr := do
  let rows := (← semanticState).subsetLiterals.filter (·.powerObject == power.row.id)
  let #[row] := rows
    | if rows.isEmpty then
        liftM (m := TermElabM) <| throwUnsupportedSource "the selected power object has no registered subset-literal form"
      else liftM (m := TermElabM) <| throwSemanticAmbiguity "the selected power object has several subset-literal forms"
  unless row.type == ``Finset do
    liftM (m := TermElabM) <| throwUnsupportedSource m!"the subset-literal form {row.id.raw} has an unread literal type"
  let list ← mkListLit power.base elements.toList
  let equalityType ← mkAppM ``DecidableEq #[power.base]
  let equality ← match ← SourceReadM.tryInstance equalityType with
    | .some instanceValue => pure instanceValue
    | .none | .undef => liftM (m := TermElabM) <| throwFailedToSynthesize equalityType
  let literal ← mkAppOptM ``List.toFinset #[some power.base, some equality, some list]
  let element ← atBase power row.denotation #[literal]
  let value ← sourceGlobalValue power element (some expected)
  let some original ← SourceReadM.selection? value
    | liftM (m := TermElabM) <| throwError "the subset literal lost its complete original power-object point"
  let selected ← sourceReferenceAt (.subset row) element value
  SourceReadM.select { original with
    value
    reference := selected.reference
    originalApplication := selected.originalApplication }





def sourceExtent? (judgement : NativeSourceJudgement) : SourceReadM (Option NativeSourceJudgement) := do
  if judgement.category.isSome then return none
  let selected ← SourceReadM.selection? judgement.value
  let power ← match selected with
    | some selected =>
      match selected.powerObject, selected.pointOrigin with
      | some original, some _ => pure (some original)
      | _, _ => sourcePowerObject? (← liftM (m := MetaM) <| instantiateMVars (← inferType judgement.value))
    | none => sourcePowerObject? (← liftM (m := MetaM) <| instantiateMVars (← inferType judgement.value))
  let some power := power | return none
  discard <| checkedDeclaration power.row.extent
  let extent ← mkConstWithFreshMVarLevels power.row.extent
  let element ← mkFreshExprMVar none
  discard <| elabAppArgs extent #[] #[Arg.expr power.base, Arg.expr element] none false false
  let elementType ← liftM (m := MetaM) <| instantiateMVars (← inferType element)
  let reference ← liftM (m := TermElabM) getRef
  let (global, _) ← elabSourceApplicationScoped
    (← mkConstWithFreshMVarLevels ``TypeCat.ofHom) #[reference] (some elementType)
    (sourceInstance := some SourceReadM.tryInstance) fun _ functionType => do
    let pointType ← liftM (m := MetaM) do
      let .forallE _ domain _ _ ← whnf functionType
        | throwError "the extent's native map constructor lost its function domain"
      pure domain
    let constant ← liftM (m := MetaM) <| withLocalDeclD `point pointType fun point => do
      mkLambdaFVars #[point] judgement.value
    SourceReadM.select { value := constant } (some functionType)
  let object ← elabRetainedSourceApplication extent #[power.base, global]
  let judgement ← sourceSetJudgement .object object
  let selected := (← SourceReadM.selection? judgement.value).getD { value := judgement.value }
  let value ← SourceReadM.select { selected with
    value := judgement.value
    powerObject := some power }
  return some { judgement with value }


def sourceMembership (power : NativePowerObject) (element container : Expr) : SourceReadM Expr := do
  let member ← atBase power power.row.member #[]
  let function ← sourceSetFunction member
  let pair ← mkAppM ``Prod.mk #[element, container]
  let reference ← liftM (m := TermElabM) getRef
  let (value, _) ← elabSourceApplicationScoped function #[reference] none
    (sourceInstance := some SourceReadM.tryInstance) fun _ expected =>
      retainSourceConstructor pair (some expected)
  SourceReadM.select { value, powerObject := some power }



def sourceComprehension (power : NativePowerObject) (predicate : Expr) (expected : Option Expr) :
    SourceReadM Expr := do
  let transpose ← mkConstWithFreshMVarLevels power.row.transpose
  discard <| checkedDeclaration power.row.transpose
  let classifier ← mkFreshExprMVar none
  discard <| elabAppArgs transpose #[] #[Arg.expr power.base, Arg.expr classifier] none false false
  let classifierType ← liftM (m := MetaM) <| instantiateMVars (← inferType classifier)
  let classifierValue ← elabRetainedSourceApplication (← mkConstWithFreshMVarLevels ``TypeCat.ofHom)
    #[predicate] (some classifierType)
  let element ← atBase power power.row.transpose #[classifierValue]
  sourceGlobalValue power element expected



def sourceImageOf (target : NativePowerObject) (domain arrow : Expr) (expected : Option Expr) :
    SourceReadM Expr := do
  let image ← mkConstWithFreshMVarLevels target.row.image
  discard <| checkedDeclaration target.row.image
  let element ← elabRetainedSourceApplication image #[domain, target.base, arrow]
  sourceGlobalValue target element expected



def sourceImage (target : NativePowerObject) (domain function : Expr) (expected : Option Expr) :
    SourceReadM Expr := do
  let image ← mkConstWithFreshMVarLevels target.row.image
  discard <| checkedDeclaration target.row.image
  let arrow ← mkFreshExprMVar none
  discard <| elabAppArgs image #[] #[Arg.expr domain, Arg.expr target.base, Arg.expr arrow]
    none false false
  let arrowType ← liftM (m := MetaM) <| instantiateMVars (← inferType arrow)
  let arrowValue ← elabRetainedSourceApplication (← mkConstWithFreshMVarLevels ``TypeCat.ofHom)
    #[function] (some arrowType)
  sourceImageOf target domain arrowValue expected

end CasCompiler
