module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue CasCompiler.SourceTest

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source did not parse"
  return ⟨source⟩





run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let matrices ← empty.read (← sourceTerm "Mat₂(ℚ)")
  let session ← empty.defineTerm `M (← empty.read (← sourceTerm "[1, 2; 3, 4]") (some matrices.source) matrices.selections)
  let vectors ← session.read (← sourceTerm "ℚ²")
  let session ← session.defineTerm `v (← session.read (← sourceTerm "(1, 2)") (some vectors.source) vectors.selections)
  for text in #["M(v)", "M*v"] do
    let product ← session.read (← sourceTerm text)
    checkSelected product fun expression => do
      checkOriginal #[expression] fun native => do
        let value ← instantiateMVars native[0]!
        if value.hasMVar then throwError "`{text}` left a parameter undetermined: {value}"
        unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.apply)).isSome do
          throwError "`{text}` is not the registered application of Mat: {value}"



  let product ← session.read (← sourceTerm "M v")
  checkSelected product fun expression => do
    checkOriginal #[expression] fun native => do
      let value ← instantiateMVars native[0]!
      unless !value.hasMVar &&
          (value.find? (·.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.apply)).isSome do
        throwError "matrix juxtaposition lost its actual registered application"
      check value
