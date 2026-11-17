module

public import CasCompiler.ReadContext
public import CasCompiler.ReadOperation

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadOperationRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  let elementOperation := elementOperation context
  let action := action context
  let relation := relation context
  match source with
  | `(cas_term| $left:cas_term + $right:cas_term) =>
    elementOperation "+" #[left, right] #[] #[] none
  | `(cas_term| $left:cas_term - $right:cas_term) => do
    -- `x - y` is `x + -y` in the selected structure (public language contract).
    -- The expansion is read once through the same registered addition and negation.
    return ← readExpression categoryOf (← `(cas_term| $left:cas_term + (-$right:cas_term)))
      expected qualification expectedCategory
  | `(cas_term| $left:cas_term ∪ $right:cas_term) =>
    elementOperation "∪" #[left, right] #[] #[] none
  | `(cas_term| $left:cas_term ∩ $right:cas_term) =>
    elementOperation "∩" #[left, right] #[] #[] none
  | `(cas_term| $left:cas_term \ $right:cas_term) =>
    elementOperation "\\" #[left, right] #[] #[] none
  | `(cas_term| $left:cas_term △ $right:cas_term) =>
    elementOperation "△" #[left, right] #[] #[] none
  | `(cas_term| $left:cas_term ⊆ $right:cas_term) => relation "⊆" left right
  | `(cas_term| $left:cas_term ≤ $right:cas_term) => relation "≤" left right
  | `(cas_term| $left:cas_term < $right:cas_term) => relation "<" left right
  | `(cas_term| $left:cas_term · $right:cas_term) =>
    elementOperation "·" #[left, right] #[] #[] none
  | `(cas_term| $left:cas_term • $right:cas_term) => action left right
  | `(cas_term| -$operand:cas_term) =>
    elementOperation "-" #[operand] #[] #[] none
  | _ => throwReadRuleMismatch

end ReadOperationRules

end CasCompiler
