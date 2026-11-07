module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.Calculus
import LeanCategories.Catalogue.Semantics.Algebra.Fields
import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Algebra.Calculus
meta import LeanCategories.Catalogue.Semantics.Algebra.Fields
meta import LeanCategories.Catalogue.Semantics.Algebra.Semirings

open Lean Meta Elab Term CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let cases : Array (String × String × Option String) := #[
    ("ℕ", "ℕ", none), ("ℤ", "ℤ", none), ("ℚ", "ℚ", none),
    ("ℝ", "ℝ", none), ("ℂ", "ℂ", none), ("ℕ⁺", "ℕ⁺", none),
    ("ℙ", "ℙ", none), ("C^∞", "C^∞", none),
    ("ℤ in Rings", "ℤ", some "Rings"), ("ℚ in Fields", "ℚ", some "Fields"),
    ("((ℤ)) in Rings", "ℤ", some "Rings"),
    ("(Fin(3)) in FiniteSets", "Fin", some "FiniteSets")]
  for (text, name, qualification) in cases do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "a registered source atom did not parse"
    let (entry, selected) ← selectObject name qualification
    let term ← session.read ⟨stx⟩
    unless term.source.expression.getAppFn.constName? == some entry.declaration do
      throwError "an atomic source changed its independently registered declaration"
    let some category := term.category
      | throwError "an atomic source lost its selected category bundle"
    unless category.expression.syntacticEq selected.expression do
      throwError "an atomic source changed its selected category"
    category.bundle.withOpen fun _ bundle => do
      unless bundle.getAppFn.constName? == some selected.declaration do
        throwError "an atomic source reconstructed a different native category bundle"
