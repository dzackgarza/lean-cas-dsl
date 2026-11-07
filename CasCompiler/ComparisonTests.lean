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
  let session ← empty.assume `h (← `(True))
  let cases := #[
    (NaturalTransformationId.listUnit, false),
    (NaturalTransformationId.listJoin, false),
    (NaturalTransformationId.listReverse, false),
    (NaturalTransformationId.listReverse, true)]
  for (id, inverse) in cases do
    let cell ← session.cell Syntax.missing id #[] sets inverse
    unless cell.transformation.source.context.entries.size == session.context.entries.size do
      throwError "whole source cell formation changed its complete formal scope"
    let objects ← session.assumeTerm `X objectType
    let object ← objects.term (← `(term| $(mkIdent `X):ident))
    let selected ← objects.cellComponent Syntax.missing cell object
    unless selected.cell.entry.id == id && selected.cell.inverse == inverse &&
        selected.value.source.context.entries.size == objects.context.entries.size do
      throwError "source cell formation changed its role, direction or complete scope"
    selected.value.source.withOpen fun bindings value => do
      let context ← ContextTelescope.capture bindings
      let transformation ← selected.cell.transformation.source.inContext context
      let left ← selected.cell.left.source.inContext context
      let right ← selected.cell.right.source.inContext context
      let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
      unless ← isDefEq (← inferType transformation) expected do
        throwError "the retained transformation has different complete native endpoints"
      let actualObject ← selected.object.source.inContext context
      let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, actualObject]
      unless ← isDefEq value component do
        throwError "source component formation replaced its actual directed action"
      let declaration := Lean.mkConst selected.cell.entry.declaration levels
      let original ← if selected.cell.entry.invertible then
          mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom)
            #[declaration]
        else pure declaration
      let originalComponent ← mkAppM ``CategoryTheory.NatTrans.app #[original, actualObject]
      unless ← isDefEq value originalComponent do
        throwError "source component formation changed the independently declared component"
      unless value.getUsedConstants.contains selected.cell.entry.declaration &&
          value.containsFVar bindings[1]!.expression.fvarId! do
        throwError "source component formation discarded its declaration or generic object"
      checkWithKernel value
  let rejected ← try
    discard <| session.cell Syntax.missing NaturalTransformationId.listUnit #[] sets true
    pure false
  catch _ => pure true
  unless rejected do throwError "a noninvertible source cell acquired an inverse"
