module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadApplicationRules

open SourceReader

def ruleCompleting (context : ReadContext) (complete : ReadCompletion) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let application := fun function arguments expected =>
    applicationResultCompleting context function arguments expected complete
  match source with
  | `(cas_term| ($function:cas_term)($arguments:cas_term,*)) => do
    let function ← readExpression categoryOf function none
    application function arguments.getElems expected
  | `(cas_term| $function:cas_term($arguments:cas_term,*)) => do
    let function ← readExpression categoryOf function none
    application function arguments.getElems expected
  | _ => do
    if source.raw.isOfKind ``CasCatalogue.Language.casMatrix then
      let some expected := expected
        | liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource "source matrix default-domain interpretation is not implemented"
      let rows := source.raw[1].getSepArgs.map fun row =>
        row.getSepArgs.map fun cell => (⟨cell⟩ : TSyntax `cas_term)
      let value ← sourceMatrix rows expected fun component type => do
        return (← readExpression categoryOf component (some type)).value
      return ← complete ⟨value, none⟩
    liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource
      m!"source translation is not implemented for expression {source}"


def ruleApplicable (context : ReadContext) : SourceReadM (Except MessageData NativeSourceJudgement) :=
  ruleCompleting context (checkReadJudgementApplicable { context with qualification := none })

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  match ← ruleApplicable context with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

end ReadApplicationRules

end CasCompiler
