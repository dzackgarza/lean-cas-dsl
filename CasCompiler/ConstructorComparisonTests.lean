module

import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.ConstructorRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let entry ← selectCategory (← semanticState) "Sets"
  let levels := (← checkedDeclaration entry.declaration).levelParams.map Level.param
  let sets ← empty.namedCategory Syntax.missing "Sets" levels #[]
  let session ← empty.assume `h (← `(True))
  let original ← session.cell Syntax.missing NaturalTransformationId.listReverse #[] sets
  let noninvertible ← session.cell Syntax.missing NaturalTransformationId.listJoin #[] sets
  for id in #[ConstructorId.arrow, ConstructorId.core] do
    let transformed ← session.constructCell Syntax.missing id original
    let .constructed constructor (.registered cell _ _) := transformed.derivation
      | throwError "constructor comparison lost its actual source derivation"
    unless constructor.id == id && cell.id == NaturalTransformationId.listReverse &&
        transformed.source.expression.syntacticEq (.construct id #[.category sets.expression]) do
      throwError "constructor comparison changed its exact symbolic source or registered action"
    let objectType ← session.elaborate Syntax.missing fun context => do
      mkAppM ``CategoryTheory.Bundled.α #[← transformed.source.value.source.inContext context]
    let objects ← session.assumeTerm `X objectType
    let object ← objects.term (← `(term| $(mkIdent `X):ident))
    let inverse ← objects.inverseCell Syntax.missing transformed
    for (directed, backwards) in #[(transformed, false), (inverse, true)] do
      let component ← objects.cellComponent Syntax.missing directed object
      component.value.source.withOpen fun bindings value => do
        let context ← ContextTelescope.capture bindings
        let some action := constructor.comparisonAction
          | throwError "the actual source constructor lost its comparison action"
        let some iso := original.isomorphism
          | throwError "the actual source comparison lost its native isomorphism"
        let category ← sets.value.source.inContext context
        let expectedIso ← applyConstructorInterface action #[category, category]
          #[← iso.source.inContext context]
        let transformation ← mkAppM
          (if backwards then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[expectedIso]
        let expected ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, bindings[1]!.expression]
        unless ← isDefEq value expected do
          throwError "constructor comparison replaced the source-owned directed component"
        checkWithKernel expectedIso
        checkWithKernel value
    let rejected ← try
      discard <| session.constructCell Syntax.missing id noninvertible
      pure false
    catch _ => pure true
    unless rejected do throwError "an isomorphism-only source constructor acquired a new cell action"
