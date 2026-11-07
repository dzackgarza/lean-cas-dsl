module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.Fields
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Algebra.Fields
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue

private def readSource (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the explicit source view did not parse"
  session.read ⟨stx⟩

private def nativeSource (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native view parameter did not parse"
  return ⟨stx⟩

private def reference (term : SourceTerm) (kind : Name) (id : String)
    (declaration : Name) : MetaM Unit := do
  let .mdata data _ := term.source.expression
    | throwError "the source view lost its selected reference"
  unless data.getName `CasCompiler.view.kind == kind &&
      data.getString `CasCompiler.view.id == id &&
      data.getName `CasCompiler.view.declaration == declaration do
    throwError "the source view changed its selected reference or declaration"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let object ← readSource empty "Fin(3)"
  let session ← empty.defineTerm `X object
  let some entry := (← semanticState).functor? FunctorId.setsList
    | throwError "the actual list functor is absent from the source"
  unless !entry.structural do throwError "the source list functor changed its declared role"
  for text in #["view X along «fun.sets.list»", "view X along «fun.sets.list»()"] do
    let image ← readSource session text
    reference image ``EdgeRef.functor entry.id.raw entry.declaration
    let some category := image.category
      | throwError "the source image lost its complete target category"
    unless category.expression.syntacticEq entry.target do
      throwError "the source image changed its declared target"
    image.source.withOpen fun bindings value => do
      let functor := Lean.mkConst entry.declaration [.zero]
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[0]!.expression]
      unless value.containsFVar bindings[0]!.expression.fvarId! && (← isDefEq value expected) do
        throwError "the explicit view changed its actual declared action or retained object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let scalars ← empty.assume `R (← nativeSource "RingCat.{0}")
  let module ← readSource scalars "RegularModule(R)"
  let modules ← scalars.defineTerm `M module
  let image ← readSource modules "view M along «fun.modules.fibre_inclusion»(R)"
  let some entry := (← semanticState).functor? FunctorId.modulesFibreInclusion
    | throwError "the source fibre inclusion is absent"
  reference image ``EdgeRef.functor entry.id.raw entry.declaration
  image.source.withOpen fun bindings value => do
    let functor := mkApp (Lean.mkConst entry.declaration [.zero, .zero]) bindings[0]!.expression
    let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
    let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[1]!.expression]
    unless (← isDefEq value expected) && value.containsFVar bindings[0]!.expression.fvarId! &&
        value.containsFVar bindings[1]!.expression.fvarId! do
      throwError "the source view lost its chosen scalar or actual module"
  let bound ← modules.defineTerm `A image
  let ring ← bound.term (← nativeSource "R")
  let shadowed ← bound.defineTerm `R ring
  let underlying ← readSource shadowed "view A along «fun.modules.underlying»()"
  let some forget := (← semanticState).functor? FunctorId.modulesUnderlying
    | throwError "the source underlying-set functor is absent"
  reference underlying ``EdgeRef.functor forget.id.raw forget.declaration
  underlying.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[2]!.expression.fvarId! &&
        !value.containsFVar bindings[3]!.expression.fvarId! do
      throwError "a later view replaced its retained object after scalar shadowing"
  let unrelated ← shadowed.assume `S (← nativeSource "RingCat.{0}")
  let failure : Option Exception ← try
    discard <| readSource unrelated "view M along «fun.modules.fibre_inclusion»(S)"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "a source view accepted an unrelated scalar at its complete native boundary"
  unless (← failure.toMessageData.toString).startsWith
      "the selected source action has a different complete native source category" do throw failure

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for (text, id) in #[
      ("view (Fin(3) in FiniteSets) along «clf.sets.finite»()", ClassifierId.setsFinite),
      ("view (ℚ in Fields) along «clf.commutative_rings.field»()", ClassifierId.commutativeRingsField)] do
    let image ← readSource empty text
    let some entry := (← semanticState).classifier? id
      | throwError "the selected source classifier is absent"
    reference image ``EdgeRef.classifierForget entry.id.raw entry.declaration
    let some category := image.category
      | throwError "the classifier view lost its actual target category"
    unless category.expression.syntacticEq entry.host do
      throwError "the classifier view changed its independently declared host"
