module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the construction source did not parse"
  return ⟨source⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← `(Nat))
  let object ← session.read (← sourceTerm "Fin(n)")
  let session ← session.defineTerm `X object
  let session ← session.assume `unused (← `(Nat))
  let some category := object.category
    | throwError "the actual finite family has no selected source category"
  for (name, declaration) in #[
      ("Aut", ``CasCatalogue.Algebra.Automorphisms.automorphismsConstruction),
      ("End", ``CasCatalogue.Algebra.Automorphisms.endomorphismsConstruction)] do
    for text in #[s!"{name}(X)", s!"view X along {name}()"] do
      let result ← session.read (← sourceTerm text)
      let some selected := result.category
        | throwError "the construction lost its complete target category"
      unless selected.role == .object do
        throwError "the construction result changed its native object role"
      result.source.withOpen fun bindings value => do
        let context ← ContextTelescope.capture bindings
        let bundle ← category.bundle.inContext context
        let functor ← mkAppM declaration #[bundle]
        let input ← mkAppM ``CategoryTheory.Core.mk #[bindings[1]!.expression]
        let (_, target) ← functorCategoryBundles functor
        let expected ← functorObject functor input target
        unless bindings.size == 3 && (← isDefEq value expected) do
          throwError "the construction changed its actual source category, receiver or context"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
