module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadApplicationRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let application := application context
  match source with
  | `(cas_term| ($function:cas_term)($arguments:cas_term,*)) => do
    let function ← readExpression categoryOf function none
    pure ⟨← application function arguments.getElems expected, none⟩
  | `(cas_term| $function:cas_term($arguments:cas_term,*)) => do
    let function ← readExpression categoryOf function none
    pure ⟨← application function arguments.getElems expected, none⟩
  | _ => do
    if source.raw.isOfKind ``CasCatalogue.Language.casMatrix then
      let some expected := expected
        | CasCatalogue.throwUnsupportedSource "source matrix default-domain interpretation is not implemented"
      let rows := source.raw[1].getSepArgs.map fun row =>
        row.getSepArgs.map fun cell => (⟨cell⟩ : TSyntax `cas_term)
      let value ← sourceMatrix rows expected fun component type => do
        return (← readExpression categoryOf component (some type)).value
      return ⟨value, none⟩
    CasCatalogue.throwUnsupportedSource
      m!"source translation is not implemented for expression {source}"

end ReadApplicationRules

end CasCompiler
