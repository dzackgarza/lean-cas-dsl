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

/- A matrix of Mat₂(ℚ) acting on a vector of ℚ² (tests/acceptance/linear_algebra.cas,
`matrices.product`): the action's ring is determined by the operands before their registered
domains are compared, so `M*v` reads. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let matrices ← empty.read (← sourceTerm "Mat₂(ℚ)")
  let session ← empty.defineTerm `M (← empty.read (← sourceTerm "[1, 2; 3, 4]") (some matrices.source))
  let vectors ← session.read (← sourceTerm "ℚ²")
  let session ← session.defineTerm `v (← session.read (← sourceTerm "(1, 2)") (some vectors.source))
  let product ← session.read (← sourceTerm "M*v")
  product.source.withOpen fun _ value => do
    let value ← instantiateMVars value
    if value.hasMVar then throwError "the matrix action left a parameter undetermined: {value}"
