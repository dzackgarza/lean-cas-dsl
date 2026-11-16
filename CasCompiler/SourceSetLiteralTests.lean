module

import CasCompiler.Read
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source did not parse"
  return ⟨source⟩

/- A set literal with no declared power object (the argument of `span({u₁, u₂})`,
tests/acceptance/linear_algebra.cas) is a subset of the set in which its elements meet: here the
vectors of ℚ³, in that set's registered power object. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let space ← empty.read (← sourceTerm "ℚ³")
  let session ← empty.defineTerm `u₁ (← empty.read (← sourceTerm "(1, 0, 1)") (some space.source))
  let session ← session.defineTerm `u₂ (← session.read (← sourceTerm "(0, 1, 1)") (some space.source))
  let literal ← session.read (← sourceTerm "{u₁, u₂}")
  literal.source.withOpen fun _ value => do
    let some power ← sourcePowerObject? (← instantiateMVars (← inferType value))
      | throwError "the literal is not a subset of a registered power object: {value}"
    let vectors ← mkAppM ``CasCatalogue.Algebra.LinearAlgebra.vectors
      #[Expr.const ``CasCatalogue.Algebra.NamedRings.rationals [], mkNatLit 3]
    unless ← isDefEq power.base vectors do
      throwError "the literal is not a subset of ℚ³: {power.base}"
