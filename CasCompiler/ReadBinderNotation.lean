module

public import CasCompiler.ReadContext
public import CasCompiler.SourceRing
public import CasCompiler.SourceAdmission

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadBinderNotation

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  if source.raw.isOfKind ``CasCatalogue.Language.casDefinite then do
    -- `∫_{a}^{b} e dt`: the registered binder `∫` at the bounds, binding `t`.
    let some bound := sourceDifferentialOf? source.raw[6].getId
      | throwError "a definite integral ends with the differential of its variable"
    let bounds : Array (TSyntax `cas_term) := #[⟨source.raw[1]⟩, ⟨source.raw[3]⟩]
    let value ← sourceBinder "∫" (bounds.map fun bound type => do
        return (← readExpression categoryOf bound (some type)).value)
      bound fun _ => do return (← readExpression categoryOf ⟨source.raw[5]⟩ none).value
    pure ⟨value, none⟩
  else if source.raw.isOfKind ``CasCatalogue.Language.casLimit then do
    -- `lim_{t → a} e`: the registered binder `lim` at the point `a`.
    let point : TSyntax `cas_term := ⟨source.raw[3]⟩
    let value ← sourceBinder "lim" #[fun type => do
        return (← readExpression categoryOf point (some type)).value]
      source.raw[1].getId fun _ => do
        return (← readExpression categoryOf ⟨source.raw[5]⟩ none).value
    pure ⟨value, none⟩
  else if source.raw.isOfKind ``CasCatalogue.Language.casBig then do
    -- `∑_{t ∈ A} e`, `∏_{t ∈ A} e`: the registered binder at the index set `A`.
    let token := (source.raw[0].find? (·.isAtom)).map (·.getAtomVal) |>.getD "∑"
    let index : TSyntax `cas_term := ⟨source.raw[4]⟩
    let value ← sourceBinder token #[fun type => do
        return (← readExpression categoryOf index (some type)).value]
      source.raw[2].getId fun _ => do
        return (← readExpression categoryOf ⟨source.raw[6]⟩ none).value
    pure ⟨value, none⟩
  else throwReadRuleMismatch

end ReadBinderNotation

end CasCompiler
