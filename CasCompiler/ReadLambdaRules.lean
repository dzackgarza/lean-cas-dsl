module

public import CasCompiler.ReadContext
public import CasCompiler.SourcePattern
public import CasCompiler.SourceRing

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def lambda (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  fun (pattern body : TSyntax `cas_term) => do
    let some expected := expected
      | liftM (m := TermElabM) <| throwError "a source lambda requires its independently declared function type"
    let type ← whnf expected
    if type.isAppOf ``TypeCat.Hom then
      -- Mathlib's set-map constructor wraps this exact native function. It supplies
      -- no structured-map laws; the complete declared Hom type fixes both endpoints.
      let constructor ← mkConstWithFreshMVarLevels ``TypeCat.ofHom
      let hole ← mkFreshExprMVar none
      discard <| elabAppArgs constructor #[] #[Arg.expr hole] (some expected) false false
      let function ← readExpression categoryOf source (some (← inferType hole))
      let value ← elabAppArgs constructor #[] #[Arg.expr function.value]
        (some expected) false false
      return ← sourceSetJudgement .morphism value
    let .forallE _ domain codomain binderInfo := type
      | do
        -- `x ↦ e` in `R[x]`: the element `e` with `x` the ring's registered generator.
        let `(cas_term| $name:ident) := pattern
          | liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource
              "source lambda formation is not implemented for this declared map type"
        let some generator ← sourceGeneratorAt? expected none
          | liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource
              "source lambda formation is not implemented for this declared map type"
        let value ← SourceReadM.withLet name.getId expected generator fun _ => do
          return (← readExpression categoryOf body (some expected)).value
        return ⟨value, none⟩
    let value ← sourcePatternLambda pattern domain binderInfo fun parameter => do
      return (← readExpression categoryOf body (some (codomain.instantiate1 parameter))).value
    return ⟨value, none⟩

end SourceReader

namespace ReadLambdaRules

open SourceReader

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  let source := context.source
  let lambda := lambda context
  match source with
  | `(cas_term| $name:ident ↦ $body:cas_term) => do
    lambda (← liftM (m := TermElabM) `(cas_term| $name:ident)) body
  | `(cas_term| ($first:cas_term, $rest:cas_term,*) ↦ $body:cas_term) => do
    lambda (← liftM (m := TermElabM) `(cas_term| ($first:cas_term, $rest:cas_term,*))) body
  | _ => throwReadRuleMismatch

end ReadLambdaRules

end CasCompiler
