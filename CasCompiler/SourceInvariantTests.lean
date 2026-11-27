module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.MvPolynomials
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.MvPolynomials
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems

open Lean Meta Elab Term CasCompiler CasCatalogue CasCompiler.SourceTest

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the invariant source did not parse"
  return ⟨source⟩




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  for text in #["dimension(ℚ)"] do
    let result ← session.read (← sourceTerm text)
    checkSelected result fun expression => do
      checkOriginal #[expression] fun native => do
        let value ← instantiateMVars native[0]!
        let some family := value.find?
            (·.isAppOfArity ``CasCatalogue.Algebra.MvPolynomials.dimension 1)
          | throwError "`{text}` did not read as the dimension family: {value}"
        let ring := Expr.const ``CasCatalogue.Algebra.NamedCommutativeRings.rationals []
        unless ← isDefEq family.appArg! ring do
          throwError "`{text}` applied the dimension family to another object: {family.appArg!}"




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let result ← session.read (← sourceTerm "dimension(ℚ) = 0")
  checkSelected result fun expression => do
    checkOriginal #[expression] fun native => do
      let value ← instantiateMVars native[0]!
      unless value.isAppOfArity ``Eq 3 do throwError "the comparison is not an equation: {value}"
      unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.MvPolynomials.naturalsDimensions)).isSome do
        throwError "the numeral did not enter the dimensions through their inclusion: {value}"
