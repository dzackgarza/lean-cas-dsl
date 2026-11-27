module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the limit source did not parse"
  return ⟨source⟩




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let result ← session.read (← sourceTerm "pullback(rev(3), rev(3))")
  unless result.category.any (·.role == .object) do
    throwError "the pullback did not read as an object"
  checkSelected result fun value => do
    let some retained ← SourceReadM.selection? value
      | throwError "the pullback lost its exact selected source"
    let some presentation := retained.originalApplication
      | throwError "the pullback lost its original complete presentation"
    unless presentation.isAppOf ``CasCatalogue.Limits.Registration.setsPullback do
      throwError "the pullback is not the declared presentation: {value}"
    let rev ← mkAppM ``CasCatalogue.Foundation.Morphisms.finRev #[mkNatLit 3]
    checkOriginal #[presentation.appFn!.appArg!, presentation.appArg!, rev] fun native => do
      unless ← isDefEq native[0]! native[2]! <&&> isDefEq native[1]! native[2]! do
        throwError "the pullback lost its diagram maps: {presentation}"




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let f ← empty.read (← sourceTerm "{0 ↦ 0, 1 ↦ 1, 2 ↦ 1} : (Fin(3) in FiniteSets) → (Fin(2) in FiniteSets)")
  let session ← empty.defineTerm `f' f
  let g ← session.read (← sourceTerm "{0 ↦ 1, 1 ↦ 0} : (Fin(2) in FiniteSets) → (Fin(2) in FiniteSets)")
  let session ← session.defineTerm `g' g
  let result ← session.read (← sourceTerm "pullback(f', g')")
  unless result.category.any (·.role == .object) do
    throwError "the created pullback did not read as an object"
  checkSelected result fun value => do
    let some retained ← SourceReadM.selection? value
      | throwError "the created pullback lost its exact original selection"
    let some construction := retained.limit
      | throwError "the created pullback lost its complete original owner"
    unless construction.source.creation.isSome && construction.source.creationFamily.isSome do
      throwError "the created pullback lost its actual selected creation interface"
    checkOriginal #[value] fun native => do
      unless (native[0]!.find? (·.isAppOf ``CategoryTheory.liftLimit)).isSome &&
          (native[0]!.find? (·.isAppOf ``CasCatalogue.Limits.Registration.setsPullback)).isSome do
        throwError "the pullback is not the lifted registered pullback of sets: {value}"
