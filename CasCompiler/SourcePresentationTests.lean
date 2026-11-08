module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the presentation source did not parse"
  return ⟨source⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← `(Nat))
  let q ← session.read (← sourceTerm "CyclicQuotient(n) in Groups")
  let session ← session.defineTerm `Q q
  let r ← session.read (← sourceTerm "ZMod(n) in Groups")
  let session ← session.defineTerm `R r
  let session ← session.assume `unused (← `(Nat))
  for (text, projection) in #[
      ("presentation(cyclic_quotient_residue(n))", ``CategoryTheory.Iso.hom),
      ("inverse_presentation(cyclic_quotient_residue(n))", ``CategoryTheory.Iso.inv)] do
    let result ← session.read (← sourceTerm text)
    unless result.category.any (·.role == .morphism) do
      throwError "the presentation changed its ordinary morphism role"
    result.source.withOpen fun bindings value => do
      let iso ← mkAppM ``CasCatalogue.Algebra.CyclicQuotients.residueComparison
        #[bindings[0]!.expression]
      let expected ← mkAppM projection #[iso]
      unless bindings.size == 4 && (← isDefEq value expected) do
        throwError "the selected presentation changed its full dependent parameters or context"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  let arrow ← session.read (← sourceTerm "presentation(cyclic_quotient_residue(n))")
  let session ← session.defineTerm `e arrow
  let result ← session.read (← sourceTerm "map e along Aut()")
  result.source.withOpen fun bindings value => do
    let iso ← mkAppM ``CasCatalogue.Algebra.CyclicQuotients.residueComparison
      #[bindings[0]!.expression]
    let type ← whnfR (← inferType iso)
    let x ← mkAppM ``CategoryTheory.Core.mk #[type.getAppArgs[2]!]
    let y ← mkAppM ``CategoryTheory.Core.mk #[type.getAppArgs[3]!]
    let core ← mkAppOptM ``CategoryTheory.CoreHom.mk
      #[some type.getAppArgs[0]!, some type.getAppArgs[1]!, some x, some y, some iso]
    let bundle ← mkAppOptM ``CategoryTheory.Cat.of
      #[some type.getAppArgs[0]!, some type.getAppArgs[1]!]
    let functor ← mkAppM ``CasCatalogue.Algebra.Automorphisms.automorphismsConstruction #[bundle]
    let expected ← mkAppM ``CategoryTheory.Functor.map #[functor, core]
    unless ← isDefEq value expected do
      throwError "Aut lost the selected presentation's actual inverse data"
