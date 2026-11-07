module

import CasCompiler.Resolve
import CasCompiler.Parse
import LeanCategories.Catalogue.Semantics.Modules.Operations
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue.Semantics.Modules.Operations

open Lean Meta Elab Term CasCompiler CasCatalogue

private def native (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native route control did not parse"
  return ⟨stx⟩

private def categoryLevels (name : String) : MetaM (List Level) := do
  let state ← semanticState
  let some category := state.categories.find? (·.name == name)
    | throwError "the source category control is absent"
  return (← checkedDeclaration category.declaration).levelParams.map Level.param

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let file ← SourceFile.parse "native-route.cas" "let U := RegularModule(R)\n"
  let some reference := file.items[0]? | throwError "the original route reference is absent"
  let rings ← empty.namedCategory reference.raw "Rings" (← categoryLevels "Rings") #[]
  let ringType ← empty.elaborate reference.raw fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← rings.value.source.inContext context]
  let parameters ← empty.assumeTerm `R ringType
  let ring ← parameters.term (← native "R")
  let modules ← parameters.namedCategory reference.raw "Modules" (← categoryLevels "Modules")
    #[ring]
  let sets ← parameters.namedCategory reference.raw "Sets" (← categoryLevels "Sets") #[]
  let session ← parameters.assume `h (← native "R = R")
  let routes ← SourceRoutes.forOwner modules.expression sets.expression
  let some trace := routes.language.grammar.shortest
    | throwError "the actual source has no selected underlying-set route control"
  let selected ← file.withContext <| routes.prepareFunctor session reference.raw trace modules
  let original ← routes.reconstruct trace
  unless selected.route.refs == original.refs && selected.target.expression.syntacticEq
      original.target do
    throwError "native route formation replaced the actual selected source derivation"
  unless selected.functor.source.context.entries.size == 2 &&
      selected.target.value.source.context.entries.size == 2 &&
      selected.functor.span.fileName == "native-route.cas" do
    throwError "native route formation discarded unused source scope or the original file"
  selected.functor.source.withOpen fun bindings expression => do
    unless expression.containsFVar bindings[0]!.expression.fvarId! do
      throwError "native route formation discarded its actual scalar parameter"
    let context ← ContextTelescope.capture bindings
    let (source, target) ← functorCategoryBundles expression
    unless ← isDefEq source (← modules.value.source.inContext context) <&&>
        isDefEq target (← selected.target.value.source.inContext context) do
      throwError "native route formation changed a complete category bundle"
  for level in modules.value.source.universeParams do
    unless selected.functor.source.universeParams.contains level do
      throwError "native route formation discarded a rigid source universe"
  let identitiesRoute ← SourceRoutes.forOwner modules.expression modules.expression
  let identity ← identitiesRoute.prepareFunctor session reference.raw #[] modules
  identity.functor.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let (source, target) ← functorCategoryBundles expression
    let category ← modules.value.source.inContext context
    unless ← isDefEq source category <&&> isDefEq target category do
      throwError "the empty route changed the selected category structure"
  let objectType ← session.elaborate reference.raw fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← modules.value.source.inContext context]
  let objects ← session.assumeTerm `X objectType
  let object ← objects.term (← native "X")
  let image ← file.withContext <| objects.routeImage reference.raw selected object
  unless image.source.context.entries.size == 3 do
    throwError "the source image discarded the actual object binding"
  image.source.withOpen fun bindings expression => do
    unless expression.containsFVar bindings[0]!.expression.fvarId! &&
        expression.containsFVar bindings[2]!.expression.fvarId! do
      throwError "the source image replaced its scalar or actual source object"
  let rejected ← try
    discard <| routes.prepareFunctor session reference.raw trace rings
    pure false
  catch _ => pure true
  unless rejected do throwError "native route formation ignored its exact source category"
