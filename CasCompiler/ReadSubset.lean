module

public import CasCompiler.ReadContext
public import CasCompiler.SourceSubset

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def membership (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (element container : TSyntax `cas_term) => do
    let container ← readExpression categoryOf container none
    let some power ← sourcePowerObject? (← instantiateMVars (← inferType container.value))
      | do
        -- Membership in an object is the element's reading in that object, settled when the
        -- statement is read (`-3 ∈ ℤ`, `p ∈ ℤ[x]`).
        let domain ← sourceCarrier container
        discard <| getLevel domain.value
        return ← readExpression categoryOf element (some domain.value)
    let element ← readExpression categoryOf element (some power.base)
    return (⟨← sourceMembership power element.value container.value, none⟩ :
      NativeSourceJudgement)

def boundIn (context : ReadContext) :
    Ident → TSyntax `cas_term → (Expr → Expr → TermElabM NativeSourceJudgement) → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (bound : Ident) (domain : TSyntax `cas_term)
      (body : Expr → Expr → TermElabM NativeSourceJudgement) => do
    let domain ← sourceCarrier (← readExpression categoryOf domain none)
    withLocalDeclD bound.getId domain.value fun parameter => body domain.value parameter

def asObject :
    NativeSourceJudgement → TermElabM NativeSourceJudgement :=
  fun (judgement : NativeSourceJudgement) => do
    return (← sourceExtent? judgement).getD judgement

end SourceReader

end CasCompiler
