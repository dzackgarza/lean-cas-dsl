module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler

/-- Read `text` after `let C := cokernel(to_dual(1))` (tests/acceptance/lattices.cas). -/
private def readAtCokernel (text : String) : TermElabM SourceTerm := do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-leg.cas" "let C := cokernel(to_dual(1))\n"
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the cokernel statement did not parse"
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the cokernel did not extend its source context"
    session := next
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the leg did not parse"
  session.read ⟨source⟩

/- A universal construction supplies its defining maps (constitution C7): `C.leg(j)` is the leg of
the registered cocone at the object of its shape that the ordinal `j` names, the `j`-th constructor
of the shape's enumeration (the original reader's `constructionLeg`). The cokernel's shape is
`WalkingParallelPair`; its leg at `one` is the quotient map. An ordinal outside the shape is
invalid. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let leg ← readAtCokernel "C.leg(1)"
  unless leg.category.any (·.role == .morphism) do
    throwError "`C.leg(1)` did not read as a morphism"
  leg.source.withOpen fun _ value => do
    let value ← instantiateMVars value
    unless (value.find? (·.isConstOf ``CategoryTheory.Limits.Cocone.ι)).isSome &&
        (value.find? (·.isConstOf ``CategoryTheory.Limits.WalkingParallelPair.one)).isSome do
      throwError "`C.leg(1)` is not the cocone's leg at `one`: {value}"
  let failure ← try
      discard <| readAtCokernel "C.leg(2)"
      pure none
    catch error => pure (some error)
  match failure with
  | none => throwError "an ordinal outside the cokernel's shape was admitted"
  | some error =>
    unless CasCatalogue.Exception.stratum? error == some .invalid do throw error
