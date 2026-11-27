module

public import CasCompiler.ReadContext
public import CasCompiler.SourceSubset
public import CasCompiler.SourceTuple
public import CasCompiler.SourceAdmission
public import CasCompiler.SourcePropertyQualification
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term




def checkReadJudgementApplicable (context : ReadContext) (judgement : NativeSourceJudgement) :
    SourceReadM (Except MessageData NativeSourceJudgement) := SourceReadM.withRef context.source do
  let judgement ← match ← retainSourceProjection? judgement.value with
    | none => pure judgement
    | some projected => pure { judgement with
        value := projected.value
        category := judgement.category <|> projected.category }
  let expected := context.expected
  let qualification := context.qualification
  let judgement ← if let some name := qualification then
    let required ← selectCategory (← CasCatalogue.semanticState) name
    match ← sourcePropertyQualificationApplicable judgement required with
    | .ok value => pure value
    | .error message => return .error message
  else pure judgement
  let nativeMorphismType? := fun (judgement : NativeSourceJudgement) => do
    let some category := judgement.category | return none
    unless category.role == .morphism &&
        category.expression.syntacticEq (.atom CasCatalogue.CategoryId.sets) do return none
    let type ← inferType judgement.value
    unless (← SourceReadM.selection? type).isSome do return none
    return some (← nativeTypeView type)
  let retain := fun (judgement : NativeSourceJudgement) (declaredType : Option Expr) => do
    let some category := judgement.category | return judgement
    let selected := (← SourceReadM.selection? judgement.value).getD { value := judgement.value }
    let value ← SourceReadM.select {
      selected with value := judgement.value, category := some category } declaredType
    return { judgement with value }
  if let some expected := expected then


    let judgement ← if (← liftM (m := MetaM) <| instantiateMVars expected).isSort then
      if judgement.category.any (·.role == .object) then sourceCarrier judgement
      else match ← sourceExtent? judgement with
        | some extent => sourceCarrier extent
        | none => pure judgement
    else pure judgement



    let judgement ← if (← whnfR (← liftM (m := MetaM) <| instantiateMVars expected)).isForall &&
        judgement.category.any (·.role == .morphism) then do
      let judgement ← match ← nativeMorphismType? judgement with
        | some type => retain judgement (some type)
        | none => pure judgement
      pure (⟨← sourceFunction judgement, none⟩ : NativeSourceJudgement)
    else pure judgement
    let actual ← inferType judgement.value
    let nativeFits ← withoutModifyingState (isDefEq actual expected)
    let scope ← get
    let sourceFits ← if nativeFits then pure true else
      scope.context.withOriginalSources #[actual, expected] fun original =>
        withoutModifyingState (isDefEq original[0]! original[1]!)
    unless sourceFits do

      if judgement.category.isNone then
        if let some value ← sourceCoercion? judgement.value
            (← liftM (m := MetaM) <| instantiateMVars expected) then
          return .ok ⟨value, none⟩
    match ← registeredSourceDomainsApplicable (← inferType judgement.value) expected with
    | .error message => return .error message
    | .ok () => pure ()
    unless sourceFits do
      return .error (MessageData.tagged `CasCompiler.SourceReader.declaredParameterType
        m!"the source expression does not have its independently declared parameter type; \
        source={context.source}; expected={expected}; actual={← inferType judgement.value}; \
        value={judgement.value}; category={(judgement.category.map (fun selected => (toJson selected.expression).compress)).getD "none"}")
    if nativeFits then
      discard <| isDefEq actual expected
      return .ok (← retain judgement none)
    let selected := (← SourceReadM.selection? judgement.value).getD {
      value := judgement.value, category := judgement.category }
    let value ← SourceReadM.select {
      selected with value := judgement.value, category := judgement.category } (some expected)
    return .ok { judgement with value }
  return .ok (← retain judgement (← nativeMorphismType? judgement))



def readWithCompletingRules (rules : Array ReadCompletingRule) (context : ReadContext) :
    SourceReadM (Except MessageData NativeSourceJudgement) := SourceReadM.withRef context.source do
  go rules.toList

where
  go : List ReadCompletingRule → SourceReadM (Except MessageData NativeSourceJudgement)
    | [] => liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource
        m!"source translation is not implemented for expression {context.source}"
    | rule :: rest => do



      let matched ← liftM (m := IO) <| IO.mkRef false
      try rule context fun judgement => do
        liftM (m := IO) <| matched.set true
        checkReadJudgementApplicable context judgement
      catch exception =>
        match exception with
        | .internal id _ =>
          if id == readRuleMismatch && !(← liftM (m := IO) matched.get) then go rest else throw exception
        | _ => throw exception


def readWithApplicableRules (rules : Array ReadApplicableRule) (context : ReadContext) :
    SourceReadM (Except MessageData NativeSourceJudgement) :=
  readWithCompletingRules (rules.map ReadApplicableRule.completing) context


def readWithRulesApplicable (rules : Array ReadRule) (context : ReadContext) :
    SourceReadM (Except MessageData NativeSourceJudgement) :=
  readWithApplicableRules (rules.map ReadRule.applicable) context




def readWithRules (rules : Array ReadRule) (context : ReadContext) :
    SourceReadM NativeSourceJudgement := SourceReadM.withRef context.source do
  match ← readWithRulesApplicable rules context with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

end CasCompiler
