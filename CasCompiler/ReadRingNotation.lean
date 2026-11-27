module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed
public import CasCompiler.SourceMember

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadRingNotation

open SourceReader

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let registered := registered context
  let relatedObject := relatedObject context
  if source.raw.isOfKind ``CasCatalogue.Language.casCoefficientOf then do

    let monomial : TSyntax `cas_term := ⟨source.raw[1]⟩
    let exponent ← match monomial with
      | `(cas_term| $_:ident ^ $power:num) => pure power
      | `(cas_term| $_:ident²) => liftM (m := TermElabM) `(num| 2)
      | `(cas_term| $_:ident³) => liftM (m := TermElabM) `(num| 3)
      | `(cas_term| $_:ident) => liftM (m := TermElabM) `(num| 1)
      | _ => liftM (m := TermElabM) <| throwError "a coefficient is of a monomial `[tⁿ]`"
    let series ← readExpression categoryOf ⟨source.raw[3]⟩ none
    let some value ← sourceElementMember? "coefficient" (some series)
        (fun _ => pure series.value) (some fun type => do
          return (← readExpression categoryOf (← liftM (m := TermElabM) `(cas_term| $exponent:num)) (some type)).value)
      | liftM (m := TermElabM) <| throwError "the series has no registered coefficient"
    pure ⟨value, none⟩
  else if source.raw.isOfKind ``CasCatalogue.Language.casInfinity then
    registered (mkIdentFrom source (.mkSimple "∞")) #[]
  else if source.raw.isOfKind ``CasCatalogue.Language.casIntegral then
    registered (mkIdentFrom source (.mkSimple "∫")) #[⟨source.raw[1]⟩]
  else if source.raw.isOfKind ``CasCatalogue.Language.casNonzero then do

    unless source.raw[2].isNatLit? == some 0 do
      liftM (m := TermElabM) <| throwError "`X ∖ n` is written for n = 0 only, the nonzero elements"
    relatedObject ⟨source.raw[0]⟩ fun name => s!"{name}∖0"
  else if source.raw.isOfKind ``CasCatalogue.Language.casSpec then
    relatedObject ⟨source.raw[1]⟩ fun name => s!"Spec {name}"
  else if source.raw.isOfKind ``CasCatalogue.Language.casRing then
    registered (mkIdentFrom source `Poly) #[⟨source.raw[0]⟩]
  else if source.raw.isOfKind ``CasCatalogue.Language.casMvRing then do

    let names ← match sourceRingVariableNames source.raw with
      | .ok names => pure names
      | .error message => liftM (m := TermElabM) <| throwError message
    let count : TSyntax `cas_term ← liftM (m := TermElabM) `(cas_term| $(⟨Syntax.mkNumLit (toString names.size)⟩):num)
    registered (mkIdentFrom source `MvPoly) #[count, ⟨source.raw[0]⟩]
  else if source.raw.isOfKind ``CasCatalogue.Language.casSeries then
    registered (mkIdentFrom source `PowerSeries) #[⟨source.raw[0]⟩]
  else throwReadRuleMismatch

end ReadRingNotation

end CasCompiler
