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

/- `span` names a registered morphism of sets and a registered object of module subobjects.
Of the two, only the morphism accepts a finite set of vectors of ℚ³ (the object needs a module
whose carrier the argument does not determine), so `span({u₁, u₂})` reads as that morphism
(tests/acceptance/linear_algebra.cas). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let space ← empty.read (← sourceTerm "ℚ³")
  let session ← empty.defineTerm `u₁ (← empty.read (← sourceTerm "(1, 0, 1)") (some space.source))
  let session ← session.defineTerm `u₂ (← session.read (← sourceTerm "(0, 1, 1)") (some space.source))
  let span ← session.read (← sourceTerm "span({u₁, u₂})")
  span.source.withOpen fun _ value => do
    unless ((← instantiateMVars value).find?
        (·.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.span)).isSome do
      throwError "the span is not the registered span of sets: {value}"

/- The span is a subset of the same set of vectors of ℚ³, so a tuple of numerals is read in it
as its elements are: `(1, 1, 2) ∈ span({u₁, u₂})` (tests/acceptance/linear_algebra.cas). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let space ← empty.read (← sourceTerm "ℚ³")
  let session ← empty.defineTerm `u₁ (← empty.read (← sourceTerm "(1, 0, 1)") (some space.source))
  let session ← session.defineTerm `u₂ (← session.read (← sourceTerm "(0, 1, 1)") (some space.source))
  discard <| session.read (← sourceTerm "(1, 1, 2) ∈ span({u₁, u₂})")
