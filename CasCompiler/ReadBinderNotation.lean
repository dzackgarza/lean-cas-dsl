module

public import CasCompiler.ReadContext
public import CasCompiler.SourceRing
public import CasCompiler.SourceAdmission

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadBinderNotation

open SourceReader

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let readArgument : TSyntax `cas_term → Expr → SourceReadM (Except MessageData Expr) :=
    fun source type => do
      return (← context.readExpressionApplicable categoryOf source (some type)).map (·.value)
  if source.raw.isOfKind ``CasCatalogue.Language.casDefinite then do

    let some bound := sourceDifferentialOf? source.raw[6].getId
      | liftM (m := TermElabM) <| throwError "a definite integral ends with the differential of its variable"
    let bounds : Array (TSyntax `cas_term) := #[⟨source.raw[1]⟩, ⟨source.raw[3]⟩]
    let value ← sourceBinder "∫" (bounds.map fun bound => readArgument bound)
      bound fun _ => do return (← readExpression categoryOf ⟨source.raw[5]⟩ none).value
    pure ⟨value, none⟩
  else if source.raw.isOfKind ``CasCatalogue.Language.casLimit then do

    let point : TSyntax `cas_term := ⟨source.raw[3]⟩
    let value ← sourceBinder "lim" #[readArgument point]
      source.raw[1].getId fun _ => do
        return (← readExpression categoryOf ⟨source.raw[5]⟩ none).value
    pure ⟨value, none⟩
  else if source.raw.isOfKind ``CasCatalogue.Language.casBig then do

    let token := (source.raw[0].find? (·.isAtom)).map (·.getAtomVal) |>.getD "∑"
    let index : TSyntax `cas_term := ⟨source.raw[4]⟩
    let value ← sourceBinder token #[readArgument index]
      source.raw[2].getId fun _ => do
        return (← readExpression categoryOf ⟨source.raw[6]⟩ none).value
    pure ⟨value, none⟩
  else throwReadRuleMismatch

end ReadBinderNotation

end CasCompiler
