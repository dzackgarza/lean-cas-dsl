module

import CasCompiler.Surface
import CasCompiler.Parse
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Surface
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native source parameter did not parse"
  return ⟨stx⟩

private def definition (file : SourceFile) (index : Nat) : TermElabM (Ident × TSyntax `cas_term) := do
  let some item := file.items[index]? | throwError "the source definition is absent"
  let `(cas_item| let $name:ident := $value:cas_term) := item
    | throwError "the source item is not a definition"
  return (name, value)

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeTerm "Nat")
  let session ← parameters.assume `h (← nativeTerm "n = n")
  let state ← semanticState
  let some rings := state.categories.find? (·.name == "Rings")
    | throwError "the scalar source category is absent"
  let ringType ← session.elaborate Syntax.missing fun _ => do
    let info ← checkedDeclaration rings.declaration
    mkAppM ``CategoryTheory.Bundled.α
      #[Lean.mkConst rings.declaration (info.levelParams.map Level.param)]
  let mut session ← session.assumeTerm `R ringType
  let file ← SourceFile.parse "public-source.cas"
    "let X := Fin(n)\nlet X := Fin(3)\nlet Y := X\n\
     let Z := (Fin(n) in FiniteSets)\nlet M := RegularModule(R)\n"
  for index in [:file.items.size] do
    let (name, syntax) ← definition file index
    let term ← file.withContext <| session.read syntax
    unless term.source.context.entries.size == 3 + index &&
        term.span.fileName == "public-source.cas" && term.span.start == syntax.raw.getPos? do
      throwError "public source reading lost its complete scope or actual source span"
    if index == 0 then
      term.source.withOpen fun bindings expression => do
        unless expression.containsFVar bindings[0]!.expression.fvarId! do
          throwError "public source reading discarded an actual native parameter"
    if index == 2 then
      unless term.source.expression == mkBVar 0 do
        throwError "public source reading replayed or rebound a shadowed source definition"
    if index == 3 then
      let some refined := state.objects.find? fun entry =>
          entry.name == "Fin" && entry.refines.isSome
        | throwError "the source refinement is absent"
      unless term.source.expression.getAppFn.constName? == some refined.declaration do
        throwError "public source qualification lost its exact refined declaration"
    if index == 4 then
      term.source.withOpen fun bindings expression => do
        unless expression.containsFVar bindings[2]!.expression.fvarId! do
          throwError "public source reading discarded its selected scalar object"
    session ← session.defineTerm name.getId term
  for source in #["Fin(h)", "Fin(unregistered_parameter)", "Fin(n) in Rings", "3"] do
    let .ok syntax := Parser.runParserCategory (← getEnv) `cas_term source
      | throwError "the source rejection control did not parse"
    let rejected ← try
      discard <| session.read ⟨syntax⟩
      pure false
    catch _ => pure true
    unless rejected do throwError "public source reading accepted an untyped source argument"
