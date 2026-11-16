module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler

/- A map applied to its whole domain is the image of the map: `m2(ℕ)` for `m2 : ℕ → ℕ` is the
registered image of the power object of ℕ at `m2` (PowerObjectEntry.image), as in
tests/acceptance/finite_sets.cas. -/
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
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "m2(ℕ)"
    | throwError "the image source did not parse"
  let image ← session.read ⟨source⟩
  image.source.withOpen fun _ value => do
    unless ((← instantiateMVars value).find?
        (·.isConstOf ``CasCatalogue.Foundation.PowerSets.image)).isSome do
      throwError "`m2(ℕ)` is not the registered image of m2: {value}"

/- A set compared with a subset of itself is the whole subset: in `X = ℕ` for `X` in `𝒫(ℕ)`
(tests/acceptance/ellipses.cas), `ℕ` is the image of its identity map. -/
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
  equation.source.withOpen fun _ value => do
    let some (_, _, right) := (← instantiateMVars value).eq?
      | throwError "`A = ℕ` is not an equation: {value}"
    unless (right.find? (·.isConstOf ``CasCatalogue.Foundation.PowerSets.image)).isSome do
      throwError "ℕ is not read as the whole subset of ℕ: {right}"
