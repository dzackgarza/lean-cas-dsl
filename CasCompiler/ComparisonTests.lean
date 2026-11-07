module

import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.Lists
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists

open Lean Meta Elab Term CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let categoryEntry ← selectCategory (← semanticState) "Sets"
  let levels := (← checkedDeclaration categoryEntry.declaration).levelParams.map Level.param
  let sets ← empty.namedCategory Syntax.missing "Sets" levels #[]
  let objectType ← empty.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← sets.value.source.inContext context]
  let objects ← empty.assumeTerm `X objectType
  let session ← objects.assume `h (← `(True))
  let object ← session.term (← `(X))
  let cases := #[
    (NaturalTransformationId.listUnit, false),
    (NaturalTransformationId.listJoin, false),
    (NaturalTransformationId.listReverse, false),
    (NaturalTransformationId.listReverse, true)]
  for (id, inverse) in cases do
    let selected ← session.cellComponent Syntax.missing id #[] sets object inverse
    unless selected.entry.id == id && selected.inverse == inverse &&
        selected.value.source.context.entries.size == session.context.entries.size do
      throwError "source cell formation changed its role, direction or complete scope"
    selected.value.source.withOpen fun bindings value => do
      let context ← ContextTelescope.capture bindings
      let transformation ← selected.transformation.source.inContext context
      let left ← selected.left.source.inContext context
      let right ← selected.right.source.inContext context
      let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
      unless ← isDefEq (← inferType transformation) expected do
        throwError "the retained transformation has different complete native endpoints"
      let actualObject ← selected.object.source.inContext context
      let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, actualObject]
      unless ← isDefEq value component do
        throwError "source component formation replaced its actual directed action"
      unless value.getUsedConstants.contains selected.entry.declaration &&
          value.containsFVar bindings[0]!.expression.fvarId! do
        throwError "source component formation discarded its declaration or generic object"
      checkWithKernel value
  let rejected ← try
    discard <| session.cellComponent Syntax.missing NaturalTransformationId.listUnit
      #[] sets object true
    pure false
  catch _ => pure true
  unless rejected do throwError "a noninvertible source cell acquired an inverse"
