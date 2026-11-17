module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadSubsetNotation

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  let registered := registered context
  if source.raw.isOfKind ``CasCatalogue.Language.casProgression then do
    -- `{a₀, a₁, …, ...}`: the progression `{a₀ + d·k | k ∈ ℕ}` its numerals begin, with
    -- `d = a₁ - a₀` constant (public language contract).
    let numerals ← source.raw[1].getSepArgs.mapM fun numeral => do
      let `(cas_term| $value:num) := (⟨numeral⟩ : TSyntax `cas_term)
        | throwError "a progression `…, ...` is of numerals"
      pure value.getNat
    let (some first, some second) := (numerals[0]?, numerals[1]?)
      | throwError "a progression `…, ...` begins with two numerals"
    unless first ≤ second do throwError "a progression `…, ...` in ℕ increases"
    let difference := second - first
    unless (numerals.toList.zip numerals.toList.tail).all fun (x, y) => y = x + difference do
      CasCatalogue.throwStratum .invalid
        m!"{numerals.toList}, ... is not an arithmetic progression"
    let first : TSyntax `num := ⟨Syntax.mkNumLit (toString first)⟩
    let difference : TSyntax `num := ⟨Syntax.mkNumLit (toString difference)⟩
    readExpression categoryOf
      (← `(cas_term| {$first:num + $difference:num · index | index ∈ ℕ}))
      expected qualification expectedCategory
  else if source.raw.isOfKind ``CasCatalogue.Language.casMultiples then do
    -- `2ℕ`: the multiples `{2·n | n ∈ ℕ}` of the numeral in the named set.
    let factor : TSyntax `num := ⟨source.raw[0]⟩
    let set : TSyntax `cas_term := ⟨mkNode ``CasCatalogue.Language.casAtom #[source.raw[1]]⟩
    readExpression categoryOf (← `(cas_term| {$factor:num · index | index ∈ $set:cas_term}))
      expected qualification expectedCategory
  else if source.raw.isOfKind ``CasCatalogue.Language.casUnits then
    registered (mkIdentFrom source `Units) #[⟨source.raw[0]⟩]
  else if source.raw.isOfKind ``CasCatalogue.Language.casFiniteSubsets then
    registered (mkIdentFrom source (.mkSimple "𝒫_fin")) #[⟨source.raw[2]⟩]
  else throwReadRuleMismatch

end ReadSubsetNotation

end CasCompiler
