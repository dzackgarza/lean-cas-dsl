module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source did not parse"
  return ⟨source⟩

/- A number-system atom given as an argument is read at the declared parameter type:
in `Mat₂(ℚ)` the coefficient object ℚ is the field the family takes, and a matrix literal is
then read in that domain (`tests/acceptance/linear_algebra.cas`). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let domain ← session.read (← sourceTerm "Mat₂(ℚ)")
  let value ← session.read (← sourceTerm "[1, 2; 3, 4]") (some domain.source)
  value.source.withOpen fun _ expression => do
    let type ← instantiateMVars (← inferType expression)
    unless (type.find? (·.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.matrices)).isSome do
      throwError "the matrix literal is not read in Mat₂(ℚ): {expression} : {type}"
