module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler

/- The bars of an element are its registered absolute value: `|z|` for `z` in ℂ is the morphism
of sets `abs : ℂ → ℝ` (`mor.sets.complex_abs`), as in tests/acceptance/numbers.cas; the bars of
an object remain its cardinality. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-abs.cas" "let z := 2 + 2i in ℂ\n"
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the complex statement did not parse"
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the complex number did not extend its source context"
    session := next
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "|z|"
    | throwError "the absolute value did not parse"
  let value ← session.read ⟨source⟩
  value.source.withOpen fun _ value => do
    unless ((← instantiateMVars value).find?
        (·.isConstOf ``CasCatalogue.Algebra.NumberSystems.abs)).isSome do
      throwError "`|z|` is not the registered absolute value: {value}"
