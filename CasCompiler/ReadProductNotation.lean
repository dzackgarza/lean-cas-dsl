module

public import CasCompiler.ReadContext
public import CasCompiler.ReadOperation

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadProductNotation

open SourceReader

private def scaled : TSyntax `cas_term → Syntax → TermElabM (TSyntax `cas_term) :=
  fun (factor : TSyntax `cas_term) (power : Syntax) => do
    let factor ← match power.find? (·.isAtom) |>.map (·.getAtomVal) with
      | some "²" => `(cas_term| $factor:cas_term ^ 2)
      | some "³" => `(cas_term| $factor:cas_term ^ 3)
      | _ => pure factor
    return factor

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  let juxtapose := juxtapose context
  if source.raw.isOfKind ``CasCatalogue.Language.casTimes then
    juxtapose ⟨source.raw[0]⟩ ⟨source.raw[2]⟩
  else if source.raw.isOfKind ``CasCatalogue.Language.casActed then
    juxtapose ⟨source.raw[0]⟩ (← `(cas_term| $(⟨source.raw[1]⟩):ident))
  else if source.raw.isOfKind ``CasCatalogue.Language.casScaled then do
    -- `2n`, `3x²`: the numeral times the variable (public language contract).
    let factor ← scaled (← `(cas_term| $(⟨source.raw[1]⟩):ident)) source.raw[2]
    readExpression categoryOf (← `(cas_term| $(⟨source.raw[0]⟩):num · $factor:cas_term))
      expected qualification expectedCategory
  else if source.raw.isOfKind ``CasCatalogue.Language.casScaledRoot then do
    -- `2√2`: the numeral times the square root.
    let factor ← `(cas_term| √$(⟨source.raw[2]⟩):cas_term)
    readExpression categoryOf (← `(cas_term| $(⟨source.raw[0]⟩):num · $factor:cas_term))
      expected qualification expectedCategory
  else if source.raw.isOfKind ``CasCatalogue.Language.casCoefficient then do
    -- `(a)x²`: the parenthesized coefficient times the variable.
    let factor ← scaled (← `(cas_term| $(⟨source.raw[3]⟩):ident)) source.raw[4]
    let coefficient : TSyntax `cas_term := ⟨source.raw[1]⟩
    readExpression categoryOf (← `(cas_term| ($coefficient:cas_term) · $factor:cas_term))
      expected qualification expectedCategory
  else throwReadRuleMismatch

end ReadProductNotation

end CasCompiler
