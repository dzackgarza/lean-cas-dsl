module

import CasCompiler.Read
import all CasCompiler.Elaborate
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Meta Elab Term CasCompiler
open CasCompiler.SourceTest

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native identity control did not parse"
  return ⟨parsed⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source identity control did not parse"
  return ⟨parsed⟩


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
          (← nativeTerm "CategoryTheory.Category.{0} (ModuleCat.{0} R)") .instImplicit
      else pure session
    let value ← session.read (← sourceTerm "id(M)")
    let some category := value.category
      | throwError "the identity lost its selected source category"
    unless category.role == .morphism do
      throwError "the identity changed its source morphism role"
    discard <| session.elaborateScoped Syntax.missing do
      let expression ← session.readTerm value
      let expected ← session.readTerm expected
      let scope ← get
      let bindings ← authoredBindings
      unless (← visitNativeData (fun term =>
          originatesAt scope.context scope.selections term bindings[1]!.expression false)
          expression false) > 0 do
        throwError "the identity changed its original object"
      if source == "RegularModule(R)" then
        unless (← visitNativeData (fun term =>
            originatesAt scope.context scope.selections term bindings[2]!.expression false)
            expression false) == 0 do
          throwError "the identity used an unrelated local category instance"
      checkOriginal #[expression, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "the identity changed its selected native category"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
      return expression
    let shadowed ← session.define `id
      (← nativeTerm "fun (_ : ModuleCat.{0} R) => (7 : Nat)")
    if source == "RegularModule(R)" then
      let value ← shadowed.read (← sourceTerm "id(M)")
      checkSelected value fun expression => do
        let scope ← get
        let bindings ← authoredBindings
        let count ← visitNativeData (fun applied => do
          unless applied.getAppFn.equal bindings.back!.expression do return false
          unless ← applied.getAppArgs.anyM fun actual =>
              originatesAt scope.context scope.selections actual bindings[1]!.expression false do
            throwError "the identity syntax replaced the exact original operand"
          return true) expression false
        unless count == 1 do
          throwError "the identity syntax displaced an exact local callable binding"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let object ← session.read (← sourceTerm "RegularModule(R)")
  let session ← session.defineTerm `M object
  let session ← session.assume `a (← nativeTerm "(M : Type)")
  let carrier ← session.term (← nativeTerm "(M : Type)")
  let value ← session.read (← sourceTerm "a in M")
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm value
    let carrier ← session.readTerm carrier
    let scope ← get
    let bindings ← authoredBindings
    unless ← originatesAt scope.context scope.selections expression bindings[2]!.expression false do
      throwError "a structured-domain annotation changed its actual source value"
    checkOriginal #[← inferType expression, carrier] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "a structured-domain annotation changed its chosen carrier"
    return expression
  let session ← empty.assume `A (← nativeTerm "Type")
  let session ← session.assume `B (← nativeTerm "Type")
  let session ← session.assume `a (← nativeTerm "A")
  let value ← session.read (← sourceTerm "a in A")
  checkSelected value fun expression => do
    let scope ← get
    let bindings ← authoredBindings
    unless ← originatesAt scope.context scope.selections expression bindings[2]!.expression false do
      throwError "an annotation replaced its exact native source binding"
  let rejected ← withoutModifyingState do
    try
      discard <| session.read (← sourceTerm "a in B")
      pure false
    catch error =>
      let detail ← error.toMessageData.toString
      unless (detail.splitOn "independently declared parameter type").length > 1 do
        throw error
      pure true
  unless rejected do throwError "a source annotation accepted an unrelated native domain"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let application ← session.read (← sourceTerm "rev(3, 0)")
  discard <| session.elaborateScoped Syntax.missing (session.readTerm application)
  let selected := application.selections.toArray.filter fun (_, selection) =>
    match selection.reference with
    | some (.named (.registered (.inr entry) _)) =>
      entry.id.raw == "mor.sets.fin_rev" && selection.originalApplication.isSome
    | _ => false
  unless !selected.isEmpty do
    throwError "the registered application lost its original selected map row"
  for (identity, _) in selected do
    let broken := { application with selections := application.selections.erase identity }
    let failure : Option Exception ← withoutModifyingState do
      try
        discard <| session.elaborateScoped Syntax.missing (session.readTerm broken)
        pure none
      catch error => pure (some error)
    let some failure := failure
      | throwError "the reader accepted an application without its selected row"
    unless failure.toMessageData.hasTag (· == `CasCompiler.SourceReadM.missingSelection) do
      throw failure



run_cmd Lean.Elab.Command.liftTermElabM do
  let results ← withLocalDeclD `n (mkConst ``Nat) fun n =>
    withLetDecl `m (mkConst ``Nat) n fun m => do
      let originalContext ← getLCtx
      let originalInstances ← getLocalInstances
      let localValue ← withSynthesize <| elabTermEnsuringType
        (← nativeTerm "cas_source% m") (some (mkConst ``Nat))
      checkWithKernel localValue
      unless ← isDefEq localValue m do
        throwError "native source quotation replaced its original ambient local"
      let expected ← withSynthesize <| elabTerm
        (← nativeTerm "CasCatalogue.Foundation.Objects.fin m") none
      let registered ← withSynthesize <| elabTermEnsuringType
        (← nativeTerm "cas_source% (Fin(m) in Sets)") (some (← inferType expected))
      checkWithKernel registered
      unless ← isDefEq registered expected do
        throwError "native source quotation lost its registered object's original parameter"
      let current := (← getLCtx).foldl (fun ids declaration =>
        ids.push declaration.fvarId) #[]
      let currentInstances ← getLocalInstances
      unless current == originalContext.foldl (fun ids declaration =>
          ids.push declaration.fvarId) #[] && currentInstances.size == originalInstances.size do
        throwError "native source quotation changed its caller's complete native scope"
      for first in originalInstances, second in currentInstances do
        unless first.className == second.className && first.fvar.equal second.fvar do
          throwError "native source quotation changed its caller's selected instance order"
      return #[← mkLambdaFVars #[n, m] localValue (usedOnly := false) (usedLetOnly := false),
        ← mkLambdaFVars #[n, m] registered (usedOnly := false) (usedLetOnly := false)]
  for result in results do
    if result.hasFVar || result.hasMVar then
      throwError "native source quotation escaped its completed original telescope"
    checkWithKernel result
