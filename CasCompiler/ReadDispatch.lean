module

public import CasCompiler.ReadContext
public import CasCompiler.SourceSubset
public import CasCompiler.SourceAdmission
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
  if let some name := qualification then
    let required ← selectCategory (← CasCatalogue.semanticState) name
    let some selected := judgement.category
      | throwError "the retained source value has no selected category"
    unless selected.expression.syntacticEq required.expression do
      throwError "the retained source value has a different selected category"
  if let some expected := expected then
    -- A native type parameter consumes the actual selected object's carrier.
    -- Reuse the same checked source action as public function domains.
    let judgement ← if (← instantiateMVars expected).isSort then
      if judgement.category.any (·.role == .object) then sourceCarrier judgement
      else match ← sourceExtent? judgement with
        | some extent => sourceCarrier extent
        | none => pure judgement
    else pure judgement
    unless ← withoutModifyingState (isDefEq (← inferType judgement.value) expected) do
      -- An element of a related named set is read through the registered maps between them.
      if judgement.category.isNone then
        if let some value ← sourceCoercion? judgement.value (← instantiateMVars expected) then
          return ⟨value, none⟩
    checkRegisteredDomains (← inferType judgement.value) expected
    unless ← isDefEq (← inferType judgement.value) expected do
      throwError "the source expression does not have its independently declared parameter type"
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
