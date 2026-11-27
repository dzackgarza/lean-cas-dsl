module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadSubsetNotation

open SourceReader

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  let registered := registered context
  if source.raw.isOfKind ``CasCatalogue.Language.casProgression then do


    let numerals ← source.raw[1].getSepArgs.mapM fun numeral => do
      let `(cas_term| $value:num) := (⟨numeral⟩ : TSyntax `cas_term)
        | liftM (m := TermElabM) <| throwError "a progression `…, ...` is of numerals"
      pure value.getNat
    let (some first, some second) := (numerals[0]?, numerals[1]?)
      | liftM (m := TermElabM) <| throwError "a progression `…, ...` begins with two numerals"
    unless first ≤ second do liftM (m := TermElabM) <| throwError "a progression `…, ...` in ℕ increases"
    let difference := second - first
    unless (numerals.toList.zip numerals.toList.tail).all fun (x, y) => y = x + difference do
      liftM (m := TermElabM) <| CasCatalogue.throwStratum .invalid
        m!"{numerals.toList}, ... is not an arithmetic progression"
    let first : TSyntax `num := ⟨Syntax.mkNumLit (toString first)⟩
    let difference : TSyntax `num := ⟨Syntax.mkNumLit (toString difference)⟩
    readExpression categoryOf
      (← liftM (m := TermElabM) `(cas_term| {$first:num + $difference:num · index | index ∈ ℕ}))
      expected qualification expectedCategory
  else if source.raw.isOfKind ``CasCatalogue.Language.casMultiples then do

    let factor : TSyntax `num := ⟨source.raw[0]⟩
    let set : TSyntax `cas_term := ⟨mkNode ``CasCatalogue.Language.casAtom #[source.raw[1]]⟩
    readExpression categoryOf (← liftM (m := TermElabM) `(cas_term| {$factor:num · index | index ∈ $set:cas_term}))
      expected qualification expectedCategory
  else if source.raw.isOfKind ``CasCatalogue.Language.casUnits then
    registered (mkIdentFrom source `Units) #[⟨source.raw[0]⟩]
  else if source.raw.isOfKind ``CasCatalogue.Language.casFiniteSubsets then
    registered (mkIdentFrom source (.mkSimple "𝒫_fin")) #[⟨source.raw[2]⟩]
  else throwReadRuleMismatch

end ReadSubsetNotation

end CasCompiler
