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

/- An invariant compared with a numeral (`dimension(ℚ) = 0`): the global element is compared at
its point, where the numeral reads in the set of dimensions through the registered inclusion
ℕ ↪ ℕ∞ ∪ {-∞}. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let result ← session.read (← sourceTerm "dimension(ℚ) = 0")
  result.source.withOpen fun _ value => do
    let value ← instantiateMVars value
    unless value.isAppOfArity ``Eq 3 do throwError "the comparison is not an equation: {value}"
    unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.MvPolynomials.naturalsDimensions)).isSome do
      throwError "the numeral did not enter the dimensions through their inclusion: {value}"
