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
    ("ℙ", "ℙ", none), ("C^∞", "C^∞", none), ("«C^∞»", "C^∞", none),
    ("ℤ in Rings", "ℤ", some "Rings"), ("ℚ in Fields", "ℚ", some "Fields"),
    ("((ℤ)) in Rings", "ℤ", some "Rings"),
    ("(Fin(3)) in FiniteSets", "Fin", some "FiniteSets")]
  for (text, name, qualification) in cases do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "a registered source atom did not parse"
    let (entry, selected) ← selectObject name qualification
    let term ← session.read ⟨stx⟩
    let .mdata data _ := term.source.expression
      | throwError "a registered source object lost its selected reference"
    unless data.getName `CasCompiler.source.kind == ``ObjectEntry &&
        data.getString `CasCompiler.source.id == entry.id.raw &&
        data.getName `CasCompiler.source.declaration == entry.declaration do
      throwError "a registered source object changed its exact selected reference"
    unless term.source.expression.consumeMData.getAppFn.constName? == some entry.declaration do
      throwError "an atomic source changed its independently registered declaration"
    let some category := term.category
      | throwError "an atomic source lost its selected category bundle"
    unless category.expression.syntacticEq selected.expression do
      throwError "an atomic source changed its selected category"
    category.bundle.withOpen fun _ bundle => do
      unless bundle.getAppFn.constName? == some selected.declaration do
        throwError "an atomic source reconstructed a different native category bundle"
    let bound ← session.defineTerm `X term
    let .ok retainedSyntax := Parser.runParserCategory (← getEnv) `cas_term "X"
      | throwError "the source reference alias did not parse"
    let retained ← bound.read ⟨retainedSyntax⟩
    retained.source.withOpen fun bindings value => do
      let some (id, declaration) ← sourceObjectReference? value
        | throwError "a native source alias lost its original object reference"
      unless id == entry.id && declaration == entry.declaration &&
          value == bindings[0]!.expression do
        throwError "a native source alias changed its selected object or binding"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  for (text, native) in #[
      ("Fin₂₃", ← `(CasCatalogue.Foundation.Objects.fin 23)),
      ("Fin₀", ← `(CasCatalogue.Foundation.Objects.fin 0)),
      ("Fin₂ in FiniteSets", ← `(CasCatalogue.Foundation.FiniteObjects.finiteFin 2))] do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the subscripted object did not parse"
    let value ← session.read ⟨source⟩
    let expected ← session.term native
    value.source.withOpen fun bindings expression => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      unless ← isDefEq expression expected do
        throwError "a subscripted object changed its actual declaration or leading parameter"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
  let session ← session.assume `Fin₂₃ (← `(Nat → Type))
  let session ← session.assume `n (← `(Nat))
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "Fin₂₃(n)"
    | throwError "the local subscripted callable did not parse"
  let value ← session.read ⟨source⟩
  value.source.withOpen fun bindings expression => do
    unless expression == mkApp bindings[0]!.expression bindings[1]!.expression do
      throwError "a subscripted spelling replaced its exact local callable binding"
