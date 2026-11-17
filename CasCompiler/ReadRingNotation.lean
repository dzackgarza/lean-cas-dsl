module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed
public import CasCompiler.SourceMember

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadRingNotation

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let registered := registered context
  let relatedObject := relatedObject context
  if source.raw.isOfKind ``CasCatalogue.Language.casCoefficientOf then do
    -- `[tⁿ]f`, `[t^n]f`, `[t]f`: the registered coefficient of `f` at the exponent `n`.
    let monomial : TSyntax `cas_term := ⟨source.raw[1]⟩
    let exponent ← match monomial with
      | `(cas_term| $_:ident ^ $power:num) => pure power
      | `(cas_term| $_:ident²) => `(num| 2)
      | `(cas_term| $_:ident³) => `(num| 3)
      | `(cas_term| $_:ident) => `(num| 1)
      | _ => throwError "a coefficient is of a monomial `[tⁿ]`"
    let series ← readExpression categoryOf ⟨source.raw[3]⟩ none
    let some value ← sourceElementMember? "coefficient" (some series)
        (fun _ => pure series.value) (some fun type => do
          return (← readExpression categoryOf (← `(cas_term| $exponent:num)) (some type)).value)
      | throwError "the series has no registered coefficient"
    pure ⟨value, none⟩
  else if source.raw.isOfKind ``CasCatalogue.Language.casInfinity then
    registered (mkIdentFrom source (.mkSimple "∞")) #[]
  else if source.raw.isOfKind ``CasCatalogue.Language.casIntegral then
    registered (mkIdentFrom source (.mkSimple "∫")) #[⟨source.raw[1]⟩]
  else if source.raw.isOfKind ``CasCatalogue.Language.casNonzero then do
    -- `X ∖ 0` for `X = N(…)`: the registered object `N∖0` at the same parameters.
    unless source.raw[2].isNatLit? == some 0 do
      throwError "`X ∖ n` is written for n = 0 only, the nonzero elements"
    relatedObject ⟨source.raw[0]⟩ fun name => s!"{name}∖0"
  else if source.raw.isOfKind ``CasCatalogue.Language.casSpec then
    relatedObject ⟨source.raw[1]⟩ fun name => s!"Spec {name}"
  else if source.raw.isOfKind ``CasCatalogue.Language.casRing then
    registered (mkIdentFrom source `Poly) #[⟨source.raw[0]⟩]
  else if source.raw.isOfKind ``CasCatalogue.Language.casMvRing then do
    -- `R[x, y]`, `R[x_0, …, x_9]`: `MvPoly(n, R)` in its `n` listed variables.
    let names ← match sourceRingVariableNames source.raw with
      | .ok names => pure names
      | .error message => throwError message
    let count : TSyntax `cas_term ← `(cas_term| $(⟨Syntax.mkNumLit (toString names.size)⟩):num)
    registered (mkIdentFrom source `MvPoly) #[count, ⟨source.raw[0]⟩]
  else if source.raw.isOfKind ``CasCatalogue.Language.casSeries then
    registered (mkIdentFrom source `PowerSeries) #[⟨source.raw[0]⟩]
  else throwReadRuleMismatch

end ReadRingNotation

end CasCompiler
