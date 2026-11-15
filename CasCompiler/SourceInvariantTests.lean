module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.MvPolynomials
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.MvPolynomials
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the invariant source did not parse"
  return ⟨source⟩

/- An invariant of objects is a registered family of global elements indexed by objects:
`dimension (A : CommRingCat) : 1 ⟶ ℕ∞ ∪ {-∞}`. Applied to the commutative ring ℚ it reads as that
family at ℚ, not as a map on elements. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  for text in #["dimension(ℚ)"] do
    let result ← session.read (← sourceTerm text)
    result.source.withOpen fun _ value => do
      let some family := (← instantiateMVars value).find?
          (·.isAppOfArity ``CasCatalogue.Algebra.MvPolynomials.dimension 1)
        | throwError "`{text}` did not read as the dimension family: {value}"
      let ring := Expr.const ``CasCatalogue.Algebra.NamedCommutativeRings.rationals []
      unless ← isDefEq family.appArg! ring do
        throwError "`{text}` applied the dimension family to another object: {family.appArg!}"
