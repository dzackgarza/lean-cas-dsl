module

public import CasCompiler.ReadContext
public import CasCompiler.ReadMember
public import CasCompiler.ReadSubset

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadMemberRules

open SourceReader

def ruleCompleting (context : ReadContext) (complete : ReadCompletion) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let member := memberCompleting context complete
  match source with
  | `(cas_term| $receiver.$method:ident()) =>
    member receiver method.getId.toString #[]
  | `(cas_term| |$operand:cas_term|) => do
    let receiver ← asObject (← readExpression categoryOf operand none)


    if !receiver.category.any (·.role == .object) then
      return .ok (← readExpression categoryOf
        (← liftM (m := TermElabM) `(cas_term| $(mkIdentFrom source `abs):ident($operand:cas_term)))
        context.expected context.qualification context.expectedCategory)
    else
      methodCompleting context complete receiver "cardinality"
  | _ => throwReadRuleMismatch

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  match ← ruleCompleting context (fun value => pure (.ok value)) with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

end ReadMemberRules

end CasCompiler
