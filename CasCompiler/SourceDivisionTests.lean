module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler

/-- Read `text` after `let Q := ℚ in CommutativeRings`. -/
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

/- `a / b` is the registered division `/ : M × Mˣ → M` (mor.sets.divide) at the monoid `M` of the
operands' object, with `b` admitted into `Mˣ` by the domain's own evidence
(tests/acceptance/fractions.cas; RX-LIFT's row `[3/2, -1]`). A commutative ring is a monoid along
several structural routes that agree by no registered comparison, so without a declared
preferred route the reading is ambiguous (constitution C6). -/
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

/- With a declared preferred route for `/` on commutative rings along the multiplicative monoid,
`3/2` reads as that division. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let environment ← getEnv
  try
    setPreferredRoutes #[⟨"/", "cat.commutative_rings",
      #["fun.commutative_rings.ring", "fun.rings.multiplicative_monoid"]⟩]
    let value ← readInRationals "3/2 in Q"
    value.source.withOpen fun _ value => do
      unless ((← instantiateMVars value).find?
          (·.isConstOf ``CasCatalogue.Algebra.Units.divide)).isSome do
        throwError "`3/2` is not the registered division: {value}"
  finally setEnv environment
