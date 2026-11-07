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
  for (receiver, id) in #[
      ("Fin(3) in FiniteSets", ClassifierId.setsFinite),
      ("ℚ in Fields", ClassifierId.commutativeRingsField)] do
    let object ← readSource empty receiver
    let session ← empty.defineTerm `X object
    let image ← readSource session s!"view X along «{id.raw}»()"
    let some entry := (← semanticState).classifier? id
      | throwError "the selected source classifier is absent"
    reference image ``EdgeRef.classifierForget entry.id.raw entry.declaration
    let some category := image.category
      | throwError "the classifier view lost its actual target category"
    unless category.expression.syntacticEq entry.host do
      throwError "the classifier view changed its independently declared host"
    image.source.withOpen fun bindings value => do
      let functor ← classifierForgetInstance entry
      let context ← ContextTelescope.capture bindings
      let some source := object.category
        | throwError "the classifier input lost its selected source category"
      let (domain, _) ← functorCategoryBundles functor
      unless ← isDefEq domain (← source.bundle.inContext context) do
        throwError "the independent classifier projection has a different source bundle"
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[0]!.expression]
      unless value.containsFVar bindings[0]!.expression.fvarId! && (← isDefEq value expected) do
        throwError "the classifier view changed its actual declared projection or bound object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `X (← nativeSource "Type")
  let image ← readSource parameters "view X along «fun.sets.list»"
  let some entry := (← semanticState).functor? FunctorId.setsList
    | throwError "the explicitly selected source context is absent"
  reference image ``EdgeRef.functor entry.id.raw entry.declaration
  image.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[0]!.expression.fvarId! do
      throwError "the explicit source context replaced its actual formal object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let domains ← empty.assume `A (← nativeSource "Type")
  let domains ← domains.assume `B (← nativeSource "Type")
  let functions ← domains.assume `f (← nativeSource "TypeCat.Hom A B")
  let image ← readSource functions "map f along «fun.sets.list»()"
  let some entry := (← semanticState).functor? FunctorId.setsList
    | throwError "the actual map action is absent from the source"
  reference image ``EdgeRef.functor entry.id.raw entry.declaration
  let some category := image.category
    | throwError "the source map action lost its selected target category"
  unless category.role == .morphism && category.expression.syntacticEq entry.target do
    throwError "the source map action changed its categorical role or target"
  image.source.withOpen fun bindings value => do
    let expected ← mkAppM ``CategoryTheory.Functor.map
      #[Lean.mkConst entry.declaration [.zero], bindings[2]!.expression]
    unless value.containsFVar bindings[2]!.expression.fvarId! && (← isDefEq value expected) do
      throwError "the source map action changed the actual declared functor or input arrow"
  let bound ← functions.defineTerm `mapped image
  let repeated ← readSource bound "map mapped along «fun.sets.list»()"
  repeated.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[3]!.expression.fvarId! do
      throwError "successive map action replaced the actual bound arrow"
  let failure : Option Exception ← try
    discard <| readSource bound "view mapped along «fun.sets.list»()"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "an object action accepted a source arrow"
  unless (← failure.toMessageData.toString).startsWith
      "the source functor action has a different object or morphism role" do throw failure
  let arguments ← bound.assume `xs (← nativeSource "List A")
  let applied ← readSource arguments "mapped(xs)"
  applied.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[3]!.expression.fvarId! &&
        value.containsFVar bindings[4]!.expression.fvarId! do
      throwError "a mapped callable lost its actual binding or later argument"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.assume `R (← nativeSource "CommRingCat.{0}")
  let rings ← rings.assume `S (← nativeSource "CommRingCat.{0}")
  let arrows ← rings.assume `f (← nativeSource "CommRingCat.Hom R S")
  let image ← readSource arrows "map f along «fun.commutative_rings.ring»()"
  let bound ← arrows.defineTerm `q image
  let some selected := image.category
    | throwError "the mapped ring arrow lost its selected category"
  unless selected.role == .morphism do
    throwError "the mapped ring arrow lost its morphism role"
  let failure : Option Exception ← try
    discard <| readSource bound "map q along «fun.commutative_rings.ring»()"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "a mapped arrow changed its selected source category"
  unless (← failure.toMessageData.toString).startsWith
      "the selected source action has a different complete symbolic source category" do
    throw failure

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let domains ← empty.assume `A (← nativeSource "Type")
  let domains ← domains.assume `B (← nativeSource "Type")
  let domains ← domains.assume `C (← nativeSource "Type")
  let arrows ← domains.assume `f (← nativeSource "TypeCat.Hom A B")
  let arrows ← arrows.assume `g (← nativeSource "TypeCat.Hom B C")
  let f ← readSource arrows "map f along «fun.sets.list»()"
  let bound ← arrows.defineTerm `fL f
  let g ← readSource bound "map g along «fun.sets.list»()"
  let bound ← bound.defineTerm `gL g
  let composite ← readSource bound "gL ∘ fL"
  let some category := composite.category
    | throwError "source composition lost its selected category"
  unless category.role == .morphism do
    throwError "source composition lost its morphism role"
  composite.source.withOpen fun bindings value => do
    let expected ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[bindings[5]!.expression, bindings[6]!.expression]
    unless (← isDefEq value expected) && value.containsFVar bindings[5]!.expression.fvarId! &&
        value.containsFVar bindings[6]!.expression.fvarId! do
      throwError "source composition changed its actual arrow occurrences or order"
  let rejected ← try
    discard <| readSource bound "fL ∘ gL"
    pure false
  catch _ => pure true
  unless rejected do throwError "source composition accepted different middle objects"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.assume `R (← nativeSource "CommRingCat.{0}")
  let coefficients ← readSource rings "integerCoefficients(R)"
  let some category := coefficients.category
    | throwError "the named morphism lost its selected category"
  unless category.role == .morphism do
    throwError "the named morphism lost its categorical role"
  coefficients.source.withOpen fun bindings value => do
    let expected ← mkAppM ``CasCatalogue.Algebra.NamedCommutativeRings.integerCoefficients
      #[bindings[0]!.expression]
    unless (← isDefEq value expected) && value.containsFVar bindings[0]!.expression.fvarId! do
      throwError "the named morphism changed its registered declaration or actual ring"
  let bound ← rings.defineTerm `q coefficients
  let mapped ← readSource bound "map q along «fun.commutative_rings.ring»()"
  mapped.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[1]!.expression.fvarId! do
      throwError "a named morphism was replayed during a later functor action"
  let dimensions ← empty.assume `n (← nativeSource "Nat")
  let reversal ← readSource dimensions "rev(n)"
  let some category := reversal.category
    | throwError "a parameterized named morphism lost its category"
  unless category.role == .morphism do
    throwError "a parameterized named morphism lost its categorical role"
  reversal.source.withOpen fun bindings value => do
    let expected ← mkAppM ``CasCatalogue.Foundation.Morphisms.finRev
      #[bindings[0]!.expression]
    unless (← isDefEq value expected) do
      throwError "a parameterized named morphism changed its declared action"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let point ← readSource empty "rev(3,2)"
  unless point.source.expression.containsConst
      (· == ``CasCatalogue.Foundation.Morphisms.finPoint) do
    throwError "a source point numeral omitted its independent declared point"
  let rejected ← try
    discard <| readSource empty "rev(3,3)"
    pure false
  catch _ => pure true
  unless rejected do throwError "a source point numeral bypassed its declared domain obligation"
