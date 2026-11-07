module

import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
meta import LeanCategories.Catalogue.Semantics.ConstructorRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.namedCategory Syntax.missing "Rings" [.param `u] #[]
  let ringType ← empty.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← rings.value.source.inContext context]
  let parameters ← empty.assumeTerm `R ringType
  let ring ← parameters.term (← `(term| $(mkIdent `R):ident))
  let modules ← parameters.namedCategory Syntax.missing "Modules" [.param `u, .param `w] #[ring]
  let first ← parameters.namedFunctor Syntax.missing FunctorId.modulesFibreInclusion #[ring] modules
  let second ← parameters.namedFunctor Syntax.missing FunctorId.modulesUnderlying #[] first.target
  let identity ← parameters.identityFunctor Syntax.missing modules
  let composite ← parameters.composeFunctors Syntax.missing first second
  let .identity category := identity.derivation
    | throwError "source functor identity lost its original category"
  unless category.expression.syntacticEq modules.expression do
    throwError "source functor identity changed its complete symbolic category"
  let .composition (.registered firstEntry _) (.registered secondEntry _) := composite.derivation
    | throwError "source functor composition lost its ordered registered derivations"
  unless firstEntry.id == FunctorId.modulesFibreInclusion &&
      secondEntry.id == FunctorId.modulesUnderlying do
    throwError "source functor composition reordered its original references"
  for id in #[ConstructorId.arrow, ConstructorId.core] do
    let constructed ← parameters.constructFunctor Syntax.missing id composite
    let .constructed constructor (.composition _ _) := constructed.derivation
      | throwError "constructed functor lost its exact constructor or inner derivation"
    unless constructor.id == id do throwError "constructed functor changed its source constructor"
    let objectType ← parameters.elaborate Syntax.missing fun context => do
      mkAppM ``CategoryTheory.Bundled.α #[← constructed.source.value.source.inContext context]
    let shadowed ← parameters.assumeTerm `R ringType
    let objects ← shadowed.assumeTerm `X objectType
    let object ← objects.term (← `(term| $(mkIdent `X):ident))
    let image ← objects.functorImage Syntax.missing constructed object
    image.source.withOpen fun bindings value => do
      let context ← ContextTelescope.capture bindings
      let first := mkApp
        (Lean.mkConst ``CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration
          [.param `u, .param `w]) bindings[0]!.expression
      let second := Lean.mkConst
        ``CasCatalogue.Modules.CatalogueRegistration.modulesUnderlyingDeclaration [.param `u, .param `w]
      let some action := constructor.functorialAction
        | throwError "the actual constructor lost its functor action"
      let expected ← applyConstructorInterface action
        #[← modules.value.source.inContext context, ← composite.target.value.source.inContext context]
        #[← mkFunctorComp first second]
      unless ← isDefEq expected (← constructed.functor.source.inContext context) do
        throwError "constructed functor changed its original whole parameterized action"
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[expected]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[2]!.expression]
      unless ← isDefEq value expected do
        throwError "source functor image changed its original scalar or actual object"
      unless value.containsFVar bindings[0]!.expression.fvarId! &&
          value.containsFVar bindings[2]!.expression.fvarId! &&
          !value.containsFVar bindings[1]!.expression.fvarId! do
        throwError "source functor image rebound an original parameter after shadowing"
      checkWithKernel value
  let invalid ← try
    discard <| parameters.composeFunctors Syntax.missing second first
    pure false
  catch _ => pure true
  unless invalid do throwError "source functor composition ignored its actual intermediate category"
