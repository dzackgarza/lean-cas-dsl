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
    TermElabM (Except MessageData NativeSourceJudgement) := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let member := memberCompleting context complete
  match source with
  | `(cas_term| $receiver.$method:ident()) =>
    member receiver method.getId.toString #[]
  | `(cas_term| |$operand:cas_term|) => do
    let receiver ← asObject (← readExpression categoryOf operand none)
    -- The bars of an element are its registered absolute value `abs` (`|z|` for z in ℂ);
    -- those of an object are its cardinality.
    if !receiver.category.any (·.role == .object) then
      return .ok (← readExpression categoryOf
        (← `(cas_term| $(mkIdentFrom source `abs):ident($operand:cas_term)))
        context.expected context.qualification context.expectedCategory)
    else
      methodCompleting context complete receiver "cardinality"
  | _ => throwReadRuleMismatch

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  match ← ruleCompleting context (fun value => pure (.ok value)) with
  | .ok value => pure value
  | .error message => throwError message

end ReadMemberRules

end CasCompiler
