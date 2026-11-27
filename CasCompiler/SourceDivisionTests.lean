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


private def readInRationals (text : String) : TermElabM SourceTerm := do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-division.cas" "let Q := ℚ in CommutativeRings\n"
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the ring statement did not parse"
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the ring did not extend its source context"
    session := next
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the quotient did not parse"
  session.read ⟨source⟩






run_cmd Lean.Elab.Command.liftTermElabM do
  let environment ← getEnv
  try
    let failure ← try
        discard <| readInRationals "3/2 in Q"
        pure none
      catch error => pure (some error)
    match failure with
    | none => throwError "`3/2` was read with no declared preferred monoid route"
    | some error => unless CasCatalogue.Exception.isSemanticAmbiguity error do throw error
  finally setEnv environment



run_cmd Lean.Elab.Command.liftTermElabM do
  let environment ← getEnv
  try
    setPreferredRoutes #[⟨"/", "cat.commutative_rings",
      #["fun.commutative_rings.ring", "fun.rings.multiplicative_monoid"]⟩]
    let value ← readInRationals "3/2 in Q"
    checkSelected value fun expression => do
      checkOriginal #[expression] fun native => do
        let value ← instantiateMVars native[0]!
        unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.Units.divide)).isSome do
          throwError "`3/2` is not the registered division: {value}"
  finally setEnv environment
