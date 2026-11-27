module

public import CasCompiler.ReadContext
public import CasCompiler.SourceSubset
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def membership (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (element container : TSyntax `cas_term) => do
    let container ← readExpression categoryOf container none
    let type ← liftM (m := MetaM) <| instantiateMVars (← inferType container.value)
    let some power ← sourcePowerObject? type
      | do


        let domain ← sourceCarrier container
        discard <| getLevel domain.value
        return ← readExpression categoryOf element (some domain.value)
    let element ← readExpression categoryOf element (some power.base)
    return (⟨← sourceMembership power element.value container.value, none⟩ :
      NativeSourceJudgement)

def boundIn (context : ReadContext) :
    Ident → TSyntax `cas_term → (Expr → Expr → SourceReadM NativeSourceJudgement) → SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (bound : Ident) (domain : TSyntax `cas_term)
      (body : Expr → Expr → SourceReadM NativeSourceJudgement) => do
    let domain ← sourceCarrier (← readExpression categoryOf domain none)
    SourceReadM.withBinder bound.getId domain.value none .default
      (fun _ judgement => pure judgement) fun parameter => body domain.value parameter

def asObject :
    NativeSourceJudgement → SourceReadM NativeSourceJudgement :=
  fun (judgement : NativeSourceJudgement) => do
    return (← sourceExtent? judgement).getD judgement

end SourceReader

end CasCompiler
