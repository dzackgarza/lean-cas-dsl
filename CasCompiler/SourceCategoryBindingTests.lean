module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Meta Elab Term CasCompiler

private def readSource (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the categorical source binding did not parse"
  session.read ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let refined ← readSource empty "Fin(3) in FiniteSets"
  let first ← empty.defineTerm `X refined
  let same ← readSource first "X in FiniteSets"
  unless same.source.expression == mkBVar 0 do
    throwError "source qualification replaced the retained object by its definition"
  let aliased ← first.defineTerm `Y same
  let plain ← readSource aliased "Fin(3)"
  let shadowed ← aliased.defineTerm `X plain
  let retained ← readSource shadowed "Y in FiniteSets"
  unless retained.source.expression == mkBVar 1 do
    throwError "a shadowed source definition changed its earlier selected category"
  let plain ← readSource shadowed "X in Sets"
  unless plain.source.expression == mkBVar 0 do
    throwError "source qualification lost the actual latest lexical binding"
  let failure : Option Exception ← try
    discard <| readSource shadowed "X in Rings"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "qualification changed a retained category without a supplied source action"
  unless (← failure.toMessageData.toString).startsWith
      "the retained source value has a different selected category" do throw failure

private def nativeSource (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native categorical parameter did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let scalars ← empty.assume `R (← nativeSource "RingCat.{0}")
  let module ← readSource scalars "RegularModule(R)"
  let modules ← scalars.defineTerm `M module
  let originalRing ← modules.term (← nativeSource "R")
  let shadowed ← modules.defineTerm `R originalRing
  let retained ← readSource shadowed "(M in Modules)"
  let some category := retained.category
    | throwError "the parameterized source object lost its selected category"
  retained.source.withOpen fun bindings value => do
    let context ← ContextTelescope.capture bindings
    let bundle ← category.bundle.inContext context
    unless value == bindings[1]!.expression &&
        bundle.containsFVar bindings[0]!.expression.fvarId! &&
        !bundle.containsFVar bindings[2]!.expression.fvarId! do
      throwError "a category bundle replaced its original scalar with a shadowing alias"
  let functions ← shadowed.define `f (← nativeSource "fun (N : ModuleCat.{0} R) => N")
  let nested ← readSource functions "f(M in Modules)"
  nested.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[1]!.expression.fvarId! &&
        value.containsFVar bindings[3]!.expression.fvarId! do
      throwError "a qualified dependent argument lost its actual source bindings"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.define `poly (← nativeSource "fun {A : Type} (x : A) => x")
  let retained ← readSource session "poly"
  unless retained.source.expression == mkBVar 0 do
    throwError "reading a callable name specialized its unapplied native family"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for (source, declaration) in #[
      ("ℤ", ``CasCatalogue.Algebra.NamedRings.ringIntegers),
      ("ℚ", ``CasCatalogue.Algebra.NamedRings.ringRationals)] do
    let module ← readSource empty s!"RegularModule({source})"
    let some category := module.category
      | throwError "a declaration-directed parameter lost the module category"
    module.source.withOpen fun _ value => do
      let expected ← mkAppM ``CasCatalogue.Modules.CatalogueRegistration.regularModule
        #[Lean.mkConst declaration]
      unless (← isDefEq value expected) && value.containsConst (· == declaration) do
        throwError "a source parameter changed its independently declared ring"
    category.bundle.withOpen fun _ bundle => do
      unless bundle.containsConst (· == declaration) do
        throwError "a module category lost its actual registered scalar parameter"
    let bound ← empty.defineTerm `M module
    let image ← readSource bound s!"view M along «fun.modules.fibre_inclusion»({source})"
    image.source.withOpen fun bindings value => do
      let functor := mkApp
        (Lean.mkConst ``CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration
          [.zero, .zero]) (Lean.mkConst declaration)
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[0]!.expression]
      unless (← isDefEq value expected) && value.containsFVar bindings[0]!.expression.fvarId! do
        throwError "a source view changed its independently typed scalar or actual module"
  let set ← readSource empty "ℚ"
  let bound ← empty.defineTerm `Q set
  for source in #["RegularModule(Q)", "RegularModule(ℚ in Sets)"] do
    let failure : Option Exception ← try
      discard <| readSource bound source
      pure none
    catch error => pure (some error)
    let some failure := failure
      | throwError "a declared parameter type replaced an existing source category"
    unless (← failure.toMessageData.toString).startsWith
        "the source expression does not have its independently declared parameter type" do
      throw failure
