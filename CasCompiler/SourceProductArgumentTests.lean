module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest





run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "gcd(84, 30)"
    | throwError "the application did not parse"
  let result ← session.read ⟨source⟩
  checkSelected result fun value => do
    let scope ← get
    let applications ← declaredApplications scope.context scope.selections
      ``CasCatalogue.Algebra.NumberSystems.gcd value
    unless applications.size == 1 do
      throwError "`gcd(84, 30)` is not its single original registered map application"
    checkOriginal #[value] fun native => do
      let value ← instantiateMVars native[0]!
      unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.NumberSystems.gcd)).isSome do
        throwError "`gcd(84, 30)` is not the registered map gcd: {value}"
      unless (value.find? (·.isAppOf ``Prod.mk)).isSome do
        throwError "`gcd(84, 30)` did not read its arguments as one pair: {value}"
      let integers := Expr.const ``CasCatalogue.Foundation.Objects.integers []
      unless ← isDefEq (← inferType value) integers do
        throwError "`gcd(84, 30)` is not an integer: {← inferType value}"
