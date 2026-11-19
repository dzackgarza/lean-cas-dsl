module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems

open Lean Meta Elab Term CasCompiler CasCatalogue

/- Several arguments of a named map on a product are the components of one pair:
`gcd(84, 30)` is the registered map `gcd : ℤ × ℤ → ℤ` (`mor.sets.gcd`) at the pair `(84, 30)`,
as in tests/acceptance/numbers.cas (`numbers.gcd`). The map is selected with its ends stated as
projections of its own arrow; the product is read from its declared source. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "gcd(84, 30)"
    | throwError "the application did not parse"
  let result ← session.read ⟨source⟩
  result.source.withOpen fun _ value => do
    let value ← instantiateMVars value
    unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.NumberSystems.gcd)).isSome do
      throwError "`gcd(84, 30)` is not the registered map gcd: {value}"
    unless (value.find? (·.isAppOf ``Prod.mk)).isSome do
      throwError "`gcd(84, 30)` did not read its arguments as one pair: {value}"
    let integers := Expr.const ``CasCatalogue.Foundation.Objects.integers []
    unless ← isDefEq (← inferType value) integers do
      throwError "`gcd(84, 30)` is not an integer: {← inferType value}"
