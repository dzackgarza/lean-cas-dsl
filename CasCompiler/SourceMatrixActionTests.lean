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
`matrices.application` and `matrices.product`): the registered application `(M, v) ↦ M v` of
Mat is reached with no argument object, its parameters fixed by the matrix, and `M(v)` and
`M*v` read. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let matrices ← empty.read (← sourceTerm "Mat₂(ℚ)")
  let session ← empty.defineTerm `M (← empty.read (← sourceTerm "[1, 2; 3, 4]") (some matrices.source))
  let vectors ← session.read (← sourceTerm "ℚ²")
  let session ← session.defineTerm `v (← session.read (← sourceTerm "(1, 2)") (some vectors.source))
  for text in #["M(v)", "M*v"] do
    let product ← session.read (← sourceTerm text)
    product.source.withOpen fun _ value => do
      let value ← instantiateMVars value
      if value.hasMVar then throwError "`{text}` left a parameter undetermined: {value}"
      unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.apply)).isSome do
        throwError "`{text}` is not the registered application of Mat: {value}"

  -- The original public juxtaposition spelling reaches the same independently
  -- registered matrix application; a rejected scalar-action input cannot hide it.
  let product ← session.read (← sourceTerm "M v")
  product.source.withOpen fun _ value => do
    let value ← instantiateMVars value
    unless !value.hasMVar &&
        (value.find? (·.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.apply)).isSome do
      throwError "matrix juxtaposition lost its actual registered application"
    check value
