module

public import CasCompiler.ReadContext
public import CasCompiler.SourceSubset
public import CasCompiler.SourceAdmission
public import CasCompiler.SourcePropertyQualification
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

/-- Native elaborator-style dispatch. Unmatched syntax tries the next rule; a matched rule's
semantic error is retained. No rule registry contains mathematical declarations. -/
def readWithRules (rules : Array ReadRule) (context : ReadContext) :
    TermElabM NativeSourceJudgement := withRef context.source do
  let expected := context.expected
  let qualification := context.qualification
  let judgement ← go rules.toList
  let judgement ← if let some name := qualification then
    let required ← selectCategory (← CasCatalogue.semanticState) name
    sourcePropertyQualification judgement required
  else pure judgement
  if let some expected := expected then
    -- A native type parameter consumes the actual selected object's carrier.
    -- Reuse the same checked source action as public function domains.
    let judgement ← if (← instantiateMVars expected).isSort then
      if judgement.category.any (·.role == .object) then sourceCarrier judgement
      else match ← sourceExtent? judgement with
        | some extent => sourceCarrier extent
        | none => pure judgement
    else pure judgement
    -- A native function parameter consumes the actual selected morphism's carrier map.
    -- Its source category was checked above; sourceFunction retains the complete selected
    -- action and map before the ordinary native type and registered-domain checks below.
    let judgement ← if (← whnfR (← instantiateMVars expected)).isForall &&
        judgement.category.any (·.role == .morphism) then
      pure (⟨← sourceFunction judgement, none⟩ : NativeSourceJudgement)
    else pure judgement
    unless ← withoutModifyingState (isDefEq (← inferType judgement.value) expected) do
      -- An element of a related named set is read through the registered maps between them.
      if judgement.category.isNone then
        if let some value ← sourceCoercion? judgement.value (← instantiateMVars expected) then
          return ⟨value, none⟩
    checkRegisteredDomains (← inferType judgement.value) expected
    unless ← isDefEq (← inferType judgement.value) expected do
      throwError (MessageData.tagged `CasCompiler.SourceReader.declaredParameterType
        m!"the source expression does not have its independently declared parameter type; \
        source={context.source}; expected={expected}; actual={← inferType judgement.value}; \
        value={judgement.value}; category={(judgement.category.map (fun selected => (toJson selected.expression).compress)).getD "none"}")
    return judgement
  return judgement

where
  go : List ReadRule → TermElabM NativeSourceJudgement
    | [] => CasCatalogue.throwUnsupportedSource
        m!"source translation is not implemented for expression {context.source}"
    | rule :: rest => do
      try rule context
      catch exception =>
        match exception with
        | .internal id _ =>
          if id == readRuleMismatch then go rest else throw exception
        | _ => throw exception

end CasCompiler
