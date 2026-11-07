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

private def nativeSyntax (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the registered source control did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeSyntax "Nat")
  let session ← parameters.assume `h (← nativeSyntax "n = n")
  let argument ← session.term (← nativeSyntax "n")
  let file ← SourceFile.parse "named-object.cas" "let X := Fin(n)\n"
  let some reference := file.items[0]? | throwError "the named source input is absent"
  let plain ← file.withContext <| session.namedObject reference.raw "Fin" none #[argument]
  let refined ← file.withContext <|
    session.namedObject reference.raw "Fin" (some "FiniteSets") #[argument]
  unless plain.entry.name == "Fin" && plain.entry.refines.isNone &&
      plain.categoryEntry.name == "Sets" && refined.entry.refines.isSome &&
      refined.categoryEntry.name == "FiniteSets" && plain.entry.id != refined.entry.id do
    throwError "named object intake lost its exact source category or refinement selection"
  for object in #[plain, refined] do
    unless object.value.source.context.entries.size == 2 &&
        object.category.source.context.entries.size == 2 &&
        object.value.span.fileName == "named-object.cas" do
      throwError "named object intake lost its complete native scope or original file"
    object.value.source.withOpen fun bindings value => do
      unless value.getAppFn.constName? == some object.entry.declaration &&
          value.containsFVar bindings[0]!.expression.fvarId! do
        throwError "named object intake replaced its declaration or actual source parameter"
  let defined ← session.defineTerm `X plain.value
  unless defined.context.entries.size == 3 do
    throwError "a registered object could not become a retained source definition"
  for (name, category, arguments) in #[
      ("Fin", some "UnregisteredCategory", #[argument]),
      ("UnregisteredObject", none, #[]), ("Fin", none, #[])] do
    let rejected ← try
      discard <| session.namedObject reference.raw name category arguments
      pure false
    catch _ => pure true
    unless rejected do throwError "named source intake accepted an absent or incomplete family"
  let state ← semanticState
  let some rings := state.categories.find? (·.name == "Rings")
    | throwError "the registered scalar category is absent from the source imports"
  let ringType ← session.elaborate reference.raw fun _ => do
    let info ← checkedDeclaration rings.declaration
    let category := Lean.mkConst rings.declaration (info.levelParams.map Level.param)
    mkAppM ``CategoryTheory.Bundled.α #[category]
  let withRing ← session.assumeTerm `R ringType
  let ring ← withRing.term (← nativeSyntax "R")
  let regular ← withRing.namedObject reference.raw "RegularModule" none #[ring]
  unless regular.entry.name == "RegularModule" && regular.categoryEntry.name == "Modules" do
    throwError "a parameterized object family lost its registered category"
  regular.category.source.withOpen fun bindings category => do
    unless category.containsFVar bindings[2]!.expression.fvarId! do
      throwError "a category fibre discarded the actual retained scalar parameter"
