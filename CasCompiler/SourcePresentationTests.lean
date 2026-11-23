module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms

import CasCompiler.Parse
import CasCompiler.PresentationFamily
import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
meta import CasCompiler.Parse
meta import CasCompiler.PresentationFamily
meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations

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
    unless value.containsFVar bindings[4]!.expression.fvarId! do
      throwError "the presentation action discarded its actual source map reference"

-- These four questions are unchanged from the original public B0 consumer. This control
-- checks source formation and the retained named family only; no proof procedure runs and
-- no comparison, generator image or arithmetic answer is supplied by this test.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let identities ← CasRuntime.IdentitySupply.new
    let file ← SourceFile.parse "source-original-f9-comparisons.cas"
      "let X := F9x\nlet Y := F9y\n\
       assert (map generator(X) along F9translation) = generator(Y) + 2\n\
       assert (map generator(Y) back along F9translation) = generator(X) - 2\n\
       assert (map F9x_constants(2) along F9translation) = F9y_constants(2)\n\
       assert (map F9y_constants(2) back along F9translation) = F9x_constants(2)\n"
    let mut session ← SourceSession.empty identities
    let mut questions := 0
    for item in file.items do
      let `(cas_item| $statement:cas_stmt) := item
        | throwError "an original F9 statement changed its parsed category"
      match ← file.withContext (session.readStatement statement) with
      | .definition next _ => session := next
      | .question term =>
        questions := questions + 1
        term.source.withOpen fun _ expression => do
          let some (.mdata data body) := expression.find? fun term =>
              match term with
              | .mdata data _ => data.getName `CasCompiler.source.kind == ``PresentationFamily
              | _ => false
            | throwError "an original F9 comparison lost its published native boundary"
          unless data.getString `CasCompiler.source.id == "cmp.f9.translation" &&
              body.getAppFn.isConstOf
                ``CasCatalogue.Algebra.PolynomialPresentations.quadraticComparison do
            throwError "an original F9 comparison changed its named Iso or operation address"
      | _ => throwError "an original F9 assertion was replaced by a settled source result"
    unless questions == 4 do throwError "the original F9 comparison control omitted a question"
  finally setEnv original

-- Both directions come from the original Iso under the complete rigid parameter family.
-- A proper prefix or extension of its checked carrier path is not a point action.
run_cmd Lean.Elab.Command.liftTermElabM do
  let state ← semanticState
  for address in #["cmp.f9.translation", "cmp.polynomial_quotient.translation"] do
    let some row := state.presentations.find? (·.id.raw == address)
      | throwError "the independently registered presentation control is missing"
    let family ← PresentationFamily.forEntry row
    unless family.family.isConstOf row.declaration &&
        !family.family.hasMVar && !family.family.hasFVar &&
        family.direction? family.forwardPath == some false &&
        family.direction? family.inversePath == some true do
      throwError "the presentation changed its original rigid family or native directions"
    for path in #[family.forwardPath, family.inversePath] do
      unless !path.isEmpty &&
          (family.direction? (path.extract 0 (path.size - 1))).isNone &&
          (family.direction? (path.push `not_a_presentation_field)).isNone do
        throwError "an unrelated native field path became a presentation point action"
