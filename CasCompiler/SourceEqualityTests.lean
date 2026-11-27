module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts

open Lean Meta Elab Term CasCompiler
open CasCompiler.SourceTest

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native source equality control did not parse"
  return ⟨parsed⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source equality control did not parse"
  return ⟨parsed⟩




run_cmd Lean.Elab.Command.liftTermElabM do
  let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx-lift-prescribed-stages.cas"
  let file ← SourceFile.parse path (← liftM (m := IO) (IO.FS.readFile path))
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  let mut original := false
  for item in file.items do
    if let `(cas_item| test $id:ident $_:str : assert $body:cas_term) := item then
      unless id.getId.toString.endsWith ".formed_arrow_action" do
        throwError "the original first whole-arrow assertion changed its source position"
      let expected ← session.term (← nativeTerm
        "(CategoryTheory.forget (ModuleCat ℚ)).map underlyingF = expectedF")
      let question ← file.withContext (session.readQuestion body)
      discard <| session.elaborateScoped Syntax.missing do
        let expression ← session.readTerm question
        let expected ← session.readTerm expected
        checkOriginal #[expression, expected] fun native => do
          unless ← isDefEq native[0]! native[1]! do
            throwError "the original arrow equation changed its complete native map comparison"
          checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
            (← mkEq native[0]! native[1]!))
        return expression
      original := true
      break
    let `(cas_item| $statement:cas_stmt) := item | continue
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the original arrow context did not form its preceding definition"
    session := next
  unless original do throwError "the original whole-arrow assertion was not observed"
  for (source, native) in #[
      ("expectedF = underlyingF",
        "expectedF = (CategoryTheory.forget (ModuleCat ℚ)).map underlyingF"),
      ("underlyingF = underlyingF", "underlyingF = underlyingF")] do
    let expected ← session.term (← nativeTerm native)
    let question ← session.readQuestion (← sourceTerm source)
    discard <| session.elaborateScoped Syntax.missing do
      let expression ← session.readTerm question
      let expected ← session.readTerm expected
      if source == "underlyingF = underlyingF" then
        let scope ← get
        let some entry := session.context.entries.find? (·.userName == `underlyingF)
          | throwError "the original structured arrow entry is absent"
        let some binding := scope.context.bindings.find? (·.id == entry.id)
          | throwError "the original structured arrow binding is absent"
        let equality ← selectedValue expression
        unless equality.isAppOfArity ``Eq 3 &&
            (← originatesAt scope.context scope.selections
              equality.getAppArgs[1]! binding.expression false) &&
            (← originatesAt scope.context scope.selections
              equality.getAppArgs[2]! binding.expression false) do
          throwError "a structured-map equality displaced its original native arrows"
      checkOriginal #[expression, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "a whole-arrow comparison changed its principal typed source terms"
      return expression
  let composed ← session.read (← sourceTerm "expectedF ∘ id(sourceModule)")
  let expected ← session.term (← nativeTerm
    "CategoryTheory.CategoryStruct.comp ((CategoryTheory.forget (ModuleCat ℚ)).map (CategoryTheory.CategoryStruct.id sourceModule)) expectedF")
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm composed
    let expected ← session.readTerm expected
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "source composition changed its selected carrier action or arrow order"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
    return expression
