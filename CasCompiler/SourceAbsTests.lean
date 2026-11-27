module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCompiler.SourceTest




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
  checkSelected value fun expression => do
    checkOriginal #[expression] fun native => do
      let value ← instantiateMVars native[0]!
      unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.NumberSystems.abs)).isSome do
        throwError "`|z|` is not the registered absolute value: {value}"
