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
    let phase : String → SourceReadM Unit := fun event => do
      try
        let scope ← get
        let heartbeats ← liftM (m := BaseIO) IO.getNumHeartbeats
        liftM (m := CoreM) <| CasTools.Diagnostics.emit event (Json.mkObj [
          ("heartbeats", toJson heartbeats),
          ("contextBindings", toJson scope.context.bindings.size),
          ("formals", toJson scope.formals.size)])
      catch _ => pure ()
    phase "source.lambda.view.started"
    let type ← nativeTypeView expected
    phase "source.lambda.view.finished"
    if type.isAppOf ``TypeCat.Hom then
      let constructor ← mkConstWithFreshMVarLevels ``TypeCat.ofHom
      let (value, _) ← elabSourceApplicationScoped constructor #[source.raw] (some type)
        (sourceInstance := some SourceReadM.tryInstance) fun _ functionType => do
          phase "source.lambda.function.started"
          let function ← readExpression categoryOf source (some functionType)
          phase "source.lambda.function.finished"
          return function.value
      phase "source.lambda.map.finished"
      return ← sourceSetJudgement .morphism value
    let .forallE _ domain codomain binderInfo := type
      | do

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
      phase "source.lambda.body.started"
      let result ← readExpression categoryOf body (some (codomain.instantiate1 parameter))
      phase "source.lambda.body.finished"
      return result.value
    phase "source.lambda.pattern.finished"
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
