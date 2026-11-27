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
  let file ← SourceFile.parse "source-image.cas" "let m2 : ℕ → ℕ := n ↦ 2n\n"
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the source map statement did not parse"
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the source map did not extend its source context"
    session := next
  for text in #["m2(ℕ)", "m2.image()"] do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the image source did not parse"
    let image ← session.read ⟨source⟩
    checkSelected image fun expression => do
      checkOriginal #[expression] fun native => do
        let value ← instantiateMVars native[0]!
        unless (value.find? (·.isConstOf ``CasCatalogue.Foundation.PowerSets.image)).isSome do
          throwError "`{text}` is not the registered image of m2: {value}"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-whole.cas" "let A := {1, 2} in 𝒫(ℕ)\n"
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the source subset statement did not parse"
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the source subset did not extend its source context"
    session := next
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "A = ℕ"
    | throwError "the equation did not parse"
  let equation ← session.read ⟨source⟩
  checkSelected equation fun expression => do
    checkOriginal #[expression] fun native => do
      let value ← instantiateMVars native[0]!
      let some (_, _, right) := value.eq?
        | throwError "`A = ℕ` is not an equation: {value}"
      unless (right.find? (·.isConstOf ``CasCatalogue.Foundation.PowerSets.image)).isSome do
        throwError "ℕ is not read as the whole subset of ℕ: {right}"
