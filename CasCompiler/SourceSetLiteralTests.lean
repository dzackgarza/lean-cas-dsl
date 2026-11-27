module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source did not parse"
  return ⟨source⟩




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let space ← empty.read (← sourceTerm "ℚ³")
  let session ← empty.defineTerm `u₁ (← empty.read (← sourceTerm "(1, 0, 1)") (some space.source) space.selections)
  let session ← session.defineTerm `u₂ (← session.read (← sourceTerm "(0, 1, 1)") (some space.source) space.selections)
  let literal ← session.read (← sourceTerm "{u₁, u₂}")
  checkSelected literal fun value => do
    checkOriginal #[value] fun native => do
      let vectors ← mkAppM ``CasCatalogue.Algebra.LinearAlgebra.vectors
        #[Expr.const ``CasCatalogue.Algebra.NamedRings.rationals [], mkNatLit 3]
      let power ← mkAppM ``CasCatalogue.Foundation.PowerSets.powerSet #[vectors]
      unless ← isDefEq (← inferType native[0]!) power do
        throwError "the literal is not a subset of ℚ³: {← inferType native[0]!}"
