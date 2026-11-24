module

public import CasCompiler.ReadContext
public import CasCompiler.SourceSubset
public import CasCompiler.SourceAdmission
public import CasCompiler.SourcePropertyQualification
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

/-- Complete a source rule's judgement using the ordinary qualification, carrier,
registered-domain and native expected-type checks. Already read numeric inclusion sources
use these same checks without replaying their syntax or suppressing a failed reading. -/
def checkReadJudgementApplicable (context : ReadContext) (judgement : NativeSourceJudgement) :
    TermElabM (Except MessageData NativeSourceJudgement) := withRef context.source do
  let expected := context.expected
  let qualification := context.qualification
  let judgement ← if let some name := qualification then
    let required ← selectCategory (← CasCatalogue.semanticState) name
    match ← sourcePropertyQualificationApplicable judgement required with
    | .ok value => pure value
    | .error message => return .error message
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
          return .ok ⟨value, none⟩
    match ← registeredDomainsApplicable (← inferType judgement.value) expected with
    | .error message => return .error message
    | .ok () => pure ()
    unless ← isDefEq (← inferType judgement.value) expected do
      return .error (MessageData.tagged `CasCompiler.SourceReader.declaredParameterType
        m!"the source expression does not have its independently declared parameter type; \
        source={context.source}; expected={expected}; actual={← inferType judgement.value}; \
        value={judgement.value}; category={(judgement.category.map (fun selected => (toJson selected.expression).compress)).getD "none"}")
    return .ok judgement
  return .ok judgement

/-- Native elaborator-style dispatch. Unmatched syntax tries the next rule; a matched rule's
semantic error is retained. No rule registry contains mathematical declarations. -/
def readWithCompletingRules (rules : Array ReadCompletingRule) (context : ReadContext) :
    TermElabM (Except MessageData NativeSourceJudgement) := withRef context.source do
  go rules.toList

where
  go : List ReadCompletingRule → TermElabM (Except MessageData NativeSourceJudgement)
    | [] => CasCatalogue.throwUnsupportedSource
        m!"source translation is not implemented for expression {context.source}"
    | rule :: rest => do
      -- Native candidate rollback does not turn a matched syntax rule back into an
      -- unmatched one. Once a rule invokes completion, every exception is its actual
      -- failure, including an internal identifier equal to the private mismatch marker.
      let matched ← liftM (m := IO) <| IO.mkRef false
      try rule context fun judgement => do
        matched.set true
        checkReadJudgementApplicable context judgement
      catch exception =>
        match exception with
        | .internal id _ =>
          if id == readRuleMismatch && !(← matched.get) then go rest else throw exception
        | _ => throw exception

/-- Ordinary applicable rules produce one judgement and complete it exactly once. -/
def readWithApplicableRules (rules : Array ReadApplicableRule) (context : ReadContext) :
    TermElabM (Except MessageData NativeSourceJudgement) :=
  readWithCompletingRules (rules.map ReadApplicableRule.completing) context

/-- Ordinary rules have no expected-type absence before producing their judgement. -/
def readWithRulesApplicable (rules : Array ReadRule) (context : ReadContext) :
    TermElabM (Except MessageData NativeSourceJudgement) :=
  readWithApplicableRules (rules.map ReadRule.applicable) context

/-- Ordinary source reading requires its own native expected-type check to succeed.
The applicability variant returns only that check's explicit mismatch, never an exception
from a matched rule, nested operand, selected carrier, or native type operation. -/
def readWithRules (rules : Array ReadRule) (context : ReadContext) :
    TermElabM NativeSourceJudgement := withRef context.source do
  match ← readWithRulesApplicable rules context with
  | .ok value => pure value
  | .error message => throwError message

end CasCompiler
