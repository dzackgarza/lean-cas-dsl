module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Meta Elab Term CasCompiler

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native identity control did not parse"
  return ⟨parsed⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source identity control did not parse"
  return ⟨parsed⟩

-- Identity uses the actual object and its selected category, as does native composition.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for source in #["Fin(3)", "RegularModule(R)"] do
    let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
    let object ← session.read (← sourceTerm source)
    let session ← session.defineTerm `M object
    let expected ← session.term (← nativeTerm "CategoryTheory.CategoryStruct.id M")
    let session ← if source == "RegularModule(R)" then
        session.assume `unrelatedCategory
          (← nativeTerm "CategoryTheory.Category (ModuleCat.{0} R)") .instImplicit
      else pure session
    let value ← session.read (← sourceTerm "id(M)")
    let some category := value.category
      | throwError "the identity lost its selected source category"
    unless category.role == .morphism do
      throwError "the identity changed its source morphism role"
    value.source.withOpen fun bindings expression => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      unless expression.containsFVar bindings[1]!.expression.fvarId! &&
          (← isDefEq expression expected) do
        throwError "the identity changed its original object or selected native category"
      if source == "RegularModule(R)" &&
          expression.containsFVar bindings[2]!.expression.fvarId! then
        throwError "the identity used an unrelated local category instance"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
    let shadowed ← session.define `id
      (← nativeTerm "fun (_ : ModuleCat.{0} R) => (7 : Nat)")
    if source == "RegularModule(R)" then
      let value ← shadowed.read (← sourceTerm "id(M)")
      value.source.withOpen fun bindings expression => do
        unless expression.getAppFn == bindings.back!.expression &&
            expression.containsFVar bindings[1]!.expression.fvarId! do
          throwError "the identity syntax displaced an exact local callable binding"
