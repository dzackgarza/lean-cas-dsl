module

public import CasCompiler.ReadContext
public import CasCompiler.ReadSubset
public import CasCompiler.SourceLimit

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadLimitRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let qualification := context.qualification
  match source with
  | `(cas_term| $left:cas_term × $right:cas_term) => do
    let left ← asObject (← readExpression categoryOf left none qualification)
    let right ← asObject (← readExpression categoryOf right none qualification)
    sourceBinaryLimit left right false
  | `(cas_term| $left:cas_term ⊔ $right:cas_term) => do
    let left ← asObject (← readExpression categoryOf left none qualification)
    let right ← asObject (← readExpression categoryOf right none qualification)
    sourceBinaryLimit left right true
  | _ => throwReadRuleMismatch

end ReadLimitRules

end CasCompiler
